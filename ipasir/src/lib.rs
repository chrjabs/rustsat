//! # rustsat-ipasir - IPASIR Bindings for RustSAT
//!
//! [IPASIR](https://github.com/biotomas/ipasir) is a general incremental interface for SAT
//! solvers. This crate provides bindings for this API to be used with the
//! [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! **Note**: This crate only provides bindings to the API, linking to a IPASIR library needs to be
//! set up by the user. This is intentional to allow easy integration of solvers that we do not
//! provide a specialized crate for. For a plug-and-play experience see the other RustSAT solver
//! crates.
//!
//! ## Linking
//!
//! Linking to a IPASIR library can be done by adding something like the following to your projects
//! build script (`build.rs`).
//!
//! ```
//! // Link to custom IPASIR solver
//! // Modify this for linking to your static library
//! // The name of the library should be _without_ the prefix 'lib' and the suffix '.a'
//! println!("cargo:rustc-link-lib=static=<path-to-your-static-lib>");
//! println!("cargo:rustc-link-search=<name-of-your-static-lib>");
//! // If your IPASIR solver links to the C++ stdlib, the next four lines are required
//! #[cfg(target_os = "macos")]
//! println!("cargo:rustc-flags=-l dylib=c++");
//! #[cfg(not(target_os = "macos"))]
//! println!("cargo:rustc-flags=-l dylib=stdc++");
//! ```

#![warn(clippy::pedantic)]
#![warn(missing_docs)]

use core::ffi::{c_int, c_void, CStr};

use cpu_time::ProcessTime;
use ffi::IpasirHandle;
use rustsat::{
    solvers::{
        ControlSignal, Learn, Solve, SolveIncremental, SolveStats, SolverResult, SolverState,
        SolverStats, StateError, Terminate,
    },
    types::{Cl, Clause, Lit, TernaryVal},
};
use thiserror::Error;

/// Fatal error returned if the IPASIR API returns an invalid value
#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("ipasir c-api returned an invalid value: {api_call} -> {value}")]
pub struct InvalidApiReturn {
    api_call: &'static str,
    value: c_int,
}

#[derive(Debug, PartialEq, Eq, Default)]
#[allow(dead_code)] // Not all solvers use all states
enum InternalSolverState {
    #[default]
    Configuring,
    Input,
    Sat,
    Unsat(Vec<Lit>),
}

impl InternalSolverState {
    fn to_external(&self) -> SolverState {
        match self {
            InternalSolverState::Configuring => SolverState::Configuring,
            InternalSolverState::Input => SolverState::Input,
            InternalSolverState::Sat => SolverState::Sat,
            InternalSolverState::Unsat(_) => SolverState::Unsat,
        }
    }
}

type TermCallbackPtr<'a> = Box<dyn FnMut() -> ControlSignal + 'a>;
type LearnCallbackPtr<'a> = Box<dyn FnMut(Clause) + 'a>;
/// Double boxing is necessary to get thin pointers for casting
type OptTermCallbackStore<'a> = Option<Box<TermCallbackPtr<'a>>>;
/// Double boxing is necessary to get thin pointers for casting
type OptLearnCallbackStore<'a> = Option<Box<LearnCallbackPtr<'a>>>;

/// Type for an IPASIR solver.
pub struct IpasirSolver<'term, 'learn> {
    handle: *mut IpasirHandle,
    state: InternalSolverState,
    terminate_cb: OptTermCallbackStore<'term>,
    learner_cb: OptLearnCallbackStore<'learn>,
    stats: SolverStats,
}

unsafe impl Send for IpasirSolver<'_, '_> {}

impl Default for IpasirSolver<'_, '_> {
    fn default() -> Self {
        Self {
            handle: unsafe { ffi::ipasir_init() },
            state: InternalSolverState::default(),
            terminate_cb: None,
            learner_cb: None,
            stats: SolverStats::default(),
        }
    }
}

impl IpasirSolver<'_, '_> {
    fn get_core_assumps(&self, assumps: &[Lit]) -> Result<Vec<Lit>, InvalidApiReturn> {
        let mut core = Vec::with_capacity(assumps.len());
        core.reserve(assumps.len());
        for a in assumps {
            match unsafe { ffi::ipasir_failed(self.handle, a.to_ipasir()) } {
                0 => (),
                1 => core.push(!*a),
                value => {
                    return Err(InvalidApiReturn {
                        api_call: "ipasir_failed",
                        value,
                    })
                }
            }
        }
        Ok(core)
    }

    #[allow(clippy::cast_precision_loss)]
    #[inline]
    fn update_avg_clause_len(&mut self, clause: &Cl) {
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
    }
}

impl Solve for IpasirSolver<'_, '_> {
    fn signature(&self) -> &'static str {
        let c_chars = unsafe { ffi::ipasir_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("IPASIR signature returned invalid UTF-8.")
    }

    fn solve(&mut self) -> anyhow::Result<SolverResult> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        }
        if let InternalSolverState::Unsat(core) = &self.state {
            if core.is_empty() {
                return Ok(SolverResult::Unsat);
            }
        }
        let start = ProcessTime::now();
        // Solve with IPASIR backend
        let res = unsafe { ffi::ipasir_solve(self.handle) };
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            0 => {
                self.stats.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.stats.n_sat += 1;
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::Sat)
            }
            20 => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Unsat(vec![]);
                Ok(SolverResult::Unsat)
            }
            value => Err(InvalidApiReturn {
                api_call: "ipasir_solve",
                value,
            }
            .into()),
        }
    }

    fn lit_val(&self, lit: Lit) -> anyhow::Result<TernaryVal> {
        if self.state != InternalSolverState::Sat {
            return Err(StateError {
                required_state: SolverState::Sat,
                actual_state: self.state.to_external(),
            }
            .into());
        }
        let lit = lit.to_ipasir();
        match unsafe { ffi::ipasir_val(self.handle, lit) } {
            0 => Ok(TernaryVal::DontCare),
            p if p == lit => Ok(TernaryVal::True),
            n if n == -lit => Ok(TernaryVal::False),
            value => Err(InvalidApiReturn {
                api_call: "ipasir_val",
                value,
            }
            .into()),
        }
    }

    fn add_clause_ref<C>(&mut self, clause: &C) -> anyhow::Result<()>
    where
        C: AsRef<Cl> + ?Sized,
    {
        let clause = clause.as_ref();
        // Update wrapper-internal state
        self.stats.n_clauses += 1;
        clause.iter().for_each(|l| match self.stats.max_var {
            None => self.stats.max_var = Some(l.var()),
            Some(var) => {
                if l.var() > var {
                    self.stats.max_var = Some(l.var());
                }
            }
        });
        self.update_avg_clause_len(clause);
        self.state = InternalSolverState::Input;
        // Call IPASIR backend
        for lit in clause {
            unsafe { ffi::ipasir_add(self.handle, lit.to_ipasir()) }
        }
        unsafe { ffi::ipasir_add(self.handle, 0) };
        Ok(())
    }
}

impl SolveIncremental for IpasirSolver<'_, '_> {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult> {
        // If in error state, remain there
        // If not, need to resolve because assumptions might have changed
        let start = ProcessTime::now();
        // Solve with IPASIR backend
        for a in assumps {
            unsafe { ffi::ipasir_assume(self.handle, a.to_ipasir()) }
        }
        let res = unsafe { ffi::ipasir_solve(self.handle) };
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            0 => {
                self.stats.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.stats.n_sat += 1;
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::Sat)
            }
            20 => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Unsat(self.get_core_assumps(assumps)?);
                Ok(SolverResult::Unsat)
            }
            value => Err(InvalidApiReturn {
                api_call: "ipasir_solve",
                value,
            }
            .into()),
        }
    }

    fn core(&mut self) -> anyhow::Result<Vec<Lit>> {
        match &self.state {
            InternalSolverState::Unsat(core) => Ok(core.clone()),
            other => Err(StateError {
                required_state: SolverState::Unsat,
                actual_state: other.to_external(),
            }
            .into()),
        }
    }
}

impl<'term> Terminate<'term> for IpasirSolver<'term, '_> {
    /// Sets a terminator callback that is regularly called during solving.
    ///
    /// # Examples
    ///
    /// Terminate solver after 10 callback calls.
    ///
    /// ```no_run
    /// use rustsat::solvers::{ControlSignal, Solve, SolverResult, Terminate};
    /// use rustsat_ipasir::IpasirSolver;
    ///
    /// let mut solver = IpasirSolver::default();
    ///
    /// // Load instance
    ///
    /// let mut cnt = 1;
    /// solver.attach_terminator(move || {
    ///     if cnt > 10 {
    ///         ControlSignal::Terminate
    ///     } else {
    ///         cnt += 1;
    ///         ControlSignal::Continue
    ///     }
    /// });
    ///
    /// let ret = solver.solve().unwrap();
    ///
    /// // Assuming an instance is actually loaded and runs long enough
    /// // assert_eq!(ret, SolverResult::Interrupted);
    /// ```
    fn attach_terminator<CB>(&mut self, cb: CB)
    where
        CB: FnMut() -> ControlSignal + 'term,
    {
        self.terminate_cb = Some(Box::new(Box::new(cb)));
        let cb_ptr =
            std::ptr::from_ref(self.terminate_cb.as_mut().unwrap().as_mut()).cast::<c_void>();
        unsafe { ffi::ipasir_set_terminate(self.handle, cb_ptr, Some(ffi::ipasir_terminate_cb)) }
    }

    fn detach_terminator(&mut self) {
        self.terminate_cb = None;
        unsafe { ffi::ipasir_set_terminate(self.handle, std::ptr::null(), None) }
    }
}

impl<'learn> Learn<'learn> for IpasirSolver<'_, 'learn> {
    /// Sets a learner callback that gets passed clauses up to a certain length learned by the solver.
    ///
    /// The callback goes out of scope with the solver, afterwards captured variables become accessible.
    ///
    /// # Examples
    ///
    /// Count number of learned clauses up to length 10.
    ///
    /// ```no_run
    /// use rustsat::solvers::{Solve, SolverResult, Learn};
    /// use rustsat_ipasir::IpasirSolver;
    ///
    /// let mut cnt = 0;
    ///
    /// {
    ///     let mut solver = IpasirSolver::default();
    ///     // Load instance
    ///
    ///     solver.attach_learner(|_| cnt += 1, 10);
    ///
    ///     solver.solve().unwrap();
    /// }
    ///
    /// // cnt variable can be accessed from here on
    /// ```
    fn attach_learner<CB>(&mut self, cb: CB, max_len: usize)
    where
        CB: FnMut(Clause) + 'learn,
    {
        self.learner_cb = Some(Box::new(Box::new(cb)));
        let cb_ptr =
            std::ptr::from_ref(self.learner_cb.as_mut().unwrap().as_mut()).cast::<c_void>();
        unsafe {
            ffi::ipasir_set_learn(
                self.handle,
                cb_ptr,
                max_len.try_into().unwrap(),
                Some(ffi::ipasir_learn_cb),
            );
        }
    }

    fn detach_learner(&mut self) {
        self.terminate_cb = None;
        unsafe { ffi::ipasir_set_learn(self.handle, std::ptr::null(), 0, None) }
    }
}

impl SolveStats for IpasirSolver<'_, '_> {
    fn stats(&self) -> SolverStats {
        self.stats.clone()
    }
}

impl Drop for IpasirSolver<'_, '_> {
    fn drop(&mut self) {
        unsafe { ffi::ipasir_release(self.handle) }
    }
}

impl Extend<Clause> for IpasirSolver<'_, '_> {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"));
    }
}

impl<'a, C> Extend<&'a C> for IpasirSolver<'_, '_>
where
    C: AsRef<Cl> + ?Sized,
{
    fn extend<T: IntoIterator<Item = &'a C>>(&mut self, iter: T) {
        iter.into_iter().for_each(|cl| {
            self.add_clause_ref(cl)
                .expect("Error adding clause in extend");
        });
    }
}

mod ffi {
    use super::{LearnCallbackPtr, TermCallbackPtr};
    use core::ffi::{c_char, c_int, c_void};
    use rustsat::{solvers::ControlSignal, types::Lit};
    use std::slice;

    #[repr(C)]
    pub struct IpasirHandle {
        _private: [u8; 0],
    }

    extern "C" {
        // Redefinitions of IPASIR functions
        pub fn ipasir_signature() -> *const c_char;
        pub fn ipasir_init() -> *mut IpasirHandle;
        pub fn ipasir_release(solver: *mut IpasirHandle);
        pub fn ipasir_add(solver: *mut IpasirHandle, lit_or_zero: c_int);
        pub fn ipasir_assume(solver: *mut IpasirHandle, lit: c_int);
        pub fn ipasir_solve(solver: *mut IpasirHandle) -> c_int;
        pub fn ipasir_val(solver: *mut IpasirHandle, lit: c_int) -> c_int;
        pub fn ipasir_failed(solver: *mut IpasirHandle, lit: c_int) -> c_int;
        pub fn ipasir_set_terminate(
            solver: *mut IpasirHandle,
            state: *const c_void,
            terminate: Option<extern "C" fn(state: *const c_void) -> c_int>,
        );
        pub fn ipasir_set_learn(
            solver: *mut IpasirHandle,
            state: *const c_void,
            max_length: c_int,
            learn: Option<extern "C" fn(state: *const c_void, clause: *const c_int)>,
        );
    }

    // Raw callbacks forwarding to user callbacks
    pub extern "C" fn ipasir_terminate_cb(ptr: *const c_void) -> c_int {
        let cb = unsafe { &mut *(ptr as *mut TermCallbackPtr<'_>) };
        match cb() {
            ControlSignal::Continue => 0,
            ControlSignal::Terminate => 1,
        }
    }

    pub extern "C" fn ipasir_learn_cb(ptr: *const c_void, clause: *const c_int) {
        let cb = unsafe { &mut *(ptr as *mut LearnCallbackPtr<'_>) };

        let mut cnt = 0;
        for n in 0.. {
            if unsafe { *clause.offset(n) } != 0 {
                cnt += 1;
            }
        }
        let int_slice = unsafe { slice::from_raw_parts(clause, cnt) };
        let clause = int_slice
            .iter()
            .map(|il| {
                Lit::from_ipasir(*il).expect("Invalid literal in learned clause from IPASIR solver")
            })
            .collect();
        cb(clause);
    }
}
