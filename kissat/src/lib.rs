//! # rustsat-kissat - Interface to the kissat SAT Solver for RustSAT
//!
//! Armin Biere's SAT solver [Kissat](https://github.com/arminbiere/kissat) to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! **Note**: at the moment this crate is known to not work on Windows since Kissat is non-trivial to get to work on Windows.
//!
//! ## Features
//!
//! - `debug`: if this feature is enables, the C library will be built with debug functionality if the Rust project is built in debug mode
//! - `safe`: disable writing through 'popen' for more safe usage of the library in applications
//! - `quiet`: exclude message and profiling code (logging too)
//!
//! ## Kissat Versions
//!
//! Kissat versions can be selected via cargo crate features.
//! The following Kissat versions are available:
//! - `v3-1-0`: [Version 3.1.0](https://github.com/arminbiere/kissat/releases/tag/rel-3.1.0)
//! - `v3-0-0`: [Version 3.0.0](https://github.com/arminbiere/kissat/releases/tag/rel-3.0.0)
//! - `sc2022-light`: [SAT Competition 2022 Light](https://github.com/arminbiere/kissat/releases/tag/sc2022-light)
//! - `sc2022-hyper`: [SAT Competition 2022 Hyper](https://github.com/arminbiere/kissat/releases/tag/sc2022-hyper)
//! - `sc2022-bulky`: [SAT Competition 2022 Bulky](https://github.com/arminbiere/kissat/releases/tag/sc2022-bulky)
//!
//! Without any features selected, the newest version will be used.
//! If conflicting Kissat versions are requested, the newest requested version will be selected.

use core::ffi::{c_int, c_uint, c_void, CStr};
use std::{ffi::CString, fmt};

use cpu_time::ProcessTime;
use ffi::KissatHandle;
use rustsat::{
    solvers::{
        ControlSignal, Interrupt, InterruptSolver, Solve, SolveStats, SolverResult, SolverState,
        SolverStats, StateError, Terminate,
    },
    types::{Clause, Lit, TernaryVal, Var},
};
use thiserror::Error;

#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("kissat c-api returned an invalid value: {api_call} -> {value}")]
pub struct InvalidApiReturn {
    api_call: &'static str,
    value: c_int,
}

#[derive(Debug, PartialEq, Eq, Default)]
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
/// Double boxing is necessary to get thin pointers for casting
type OptTermCallbackStore<'a> = Option<Box<TermCallbackPtr<'a>>>;

/// The Kissat solver type
pub struct Kissat<'term> {
    handle: *mut KissatHandle,
    state: InternalSolverState,
    terminate_cb: OptTermCallbackStore<'term>,
    stats: SolverStats,
}

unsafe impl Send for Kissat<'_> {}

impl Default for Kissat<'_> {
    fn default() -> Self {
        let solver = Self {
            handle: unsafe { ffi::kissat_init() },
            state: Default::default(),
            terminate_cb: Default::default(),
            stats: Default::default(),
        };
        let quiet = CString::new("quiet").unwrap();
        unsafe { ffi::kissat_set_option(solver.handle, quiet.as_ptr(), 1) };
        solver
    }
}

impl Kissat<'_> {
    /// Gets the commit ID that Kissat was built from
    pub fn commit_id() -> &'static str {
        let c_chars = unsafe { ffi::kissat_id() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str.to_str().expect("Kissat id returned invalid UTF-8.")
    }

    /// Gets the Kissat version
    pub fn version() -> &'static str {
        let c_chars = unsafe { ffi::kissat_version() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Kissat version returned invalid UTF-8.")
    }

    /// Gets the compiler Kissat was built with
    pub fn compiler() -> &'static str {
        let c_chars = unsafe { ffi::kissat_compiler() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Kissat compiler returned invalid UTF-8.")
    }

    /// Sets a pre-defined configuration for Kissat's internal options
    pub fn set_configuration(&mut self, config: Config) -> anyhow::Result<()> {
        if self.state != InternalSolverState::Configuring {
            return Err(StateError {
                required_state: SolverState::Configuring,
                actual_state: self.state.to_external(),
            }
            .into());
        }
        let config_name = match config {
            Config::Default => CString::new("default").unwrap(),
            Config::Basic => CString::new("basic").unwrap(),
            Config::Plain => CString::new("plain").unwrap(),
            Config::SAT => CString::new("sat").unwrap(),
            Config::UNSAT => CString::new("unsat").unwrap(),
        };
        let ret = unsafe { ffi::kissat_set_configuration(self.handle, config_name.as_ptr()) };
        if ret != 0 {
            Ok(())
        } else {
            Err(InvalidApiReturn {
                api_call: "kissat_configure",
                value: 0,
            }
            .into())
        }
    }

    /// Sets the value of a Kissat option. For possible options, check Kissat with `kissat --help`.
    /// Requires state [`SolverState::Configuring`].
    pub fn set_option(&mut self, name: &str, value: c_int) -> anyhow::Result<()> {
        let c_name = CString::new(name)?;
        if unsafe { ffi::kissat_set_option(self.handle, c_name.as_ptr(), value) } != 0 {
            Ok(())
        } else {
            Err(InvalidApiReturn {
                api_call: "kissat_set_option",
                value: 0,
            }
            .into())
        }
    }

    /// Gets the value of a Kissat option. For possible options, check Kissat with `kissat --help`.
    pub fn get_option(&self, name: &str) -> anyhow::Result<c_int> {
        let c_name = CString::new(name)?;
        Ok(unsafe { ffi::kissat_get_option(self.handle, c_name.as_ptr()) })
    }

    /// Sets an internal limit for Kissat
    pub fn set_limit(&mut self, limit: Limit) {
        match limit {
            Limit::Conflicts(val) => unsafe { ffi::kissat_set_conflict_limit(self.handle, val) },
            Limit::Decisions(val) => unsafe { ffi::kissat_set_decision_limit(self.handle, val) },
        }
    }

    /// Prints the solver statistics from the Kissat backend
    pub fn print_stats(&self) {
        unsafe { ffi::kissat_print_statistics(self.handle) }
    }
}

impl Extend<Clause> for Kissat<'_> {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"))
    }
}

impl Solve for Kissat<'_> {
    fn signature(&self) -> &'static str {
        let c_chars = unsafe { ffi::kissat_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Kissat signature returned invalid UTF-8.")
    }

    fn reserve(&mut self, max_var: Var) -> anyhow::Result<()> {
        self.state = InternalSolverState::Input;
        unsafe { ffi::kissat_reserve(self.handle, max_var.to_ipasir()) };
        Ok(())
    }

    fn solve(&mut self) -> anyhow::Result<SolverResult> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        }
        if let InternalSolverState::Unsat(_) = self.state {
            return Ok(SolverResult::Unsat);
        }
        let start = ProcessTime::now();
        // Solve with Kissat backend
        let res = unsafe { ffi::kissat_solve(self.handle) };
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
                api_call: "kissat_solve",
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
        match unsafe { ffi::kissat_value(self.handle, lit) } {
            0 => Ok(TernaryVal::DontCare),
            p if p == lit => Ok(TernaryVal::True),
            n if n == -lit => Ok(TernaryVal::False),
            value => Err(InvalidApiReturn {
                api_call: "kissat_value",
                value,
            }
            .into()),
        }
    }

    fn add_clause(&mut self, clause: Clause) -> anyhow::Result<()> {
        // Kissat is non-incremental, so only add if in input or configuring state
        if !matches!(
            self.state,
            InternalSolverState::Input | InternalSolverState::Configuring
        ) {
            return Err(StateError {
                required_state: SolverState::Input,
                actual_state: self.state.to_external(),
            }
            .into());
        }
        // Update wrapper-internal state
        self.stats.n_clauses += 1;
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
        clause.iter().for_each(|l| match self.stats.max_var {
            None => self.stats.max_var = Some(l.var()),
            Some(var) => {
                if l.var() > var {
                    self.stats.max_var = Some(l.var())
                }
            }
        });
        self.state = InternalSolverState::Input;
        // Call Kissat backend
        clause
            .into_iter()
            .for_each(|l| unsafe { ffi::kissat_add(self.handle, l.to_ipasir()) });
        unsafe { ffi::kissat_add(self.handle, 0) };
        Ok(())
    }
}

impl<'term> Terminate<'term> for Kissat<'term> {
    /// Sets a terminator callback that is regularly called during solving.
    ///
    /// # Examples
    ///
    /// Terminate solver after 10 callback calls.
    ///
    /// ```
    /// use rustsat::solvers::{ControlSignal, Solve, SolverResult, Terminate};
    /// use rustsat_kissat::Kissat;
    ///
    /// let mut solver = Kissat::default();
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
        let cb_ptr = self.terminate_cb.as_mut().unwrap().as_mut() as *const _ as *const c_void;
        unsafe { ffi::kissat_set_terminate(self.handle, cb_ptr, Some(ffi::kissat_terminate_cb)) }
    }

    fn detach_terminator(&mut self) {
        self.terminate_cb = None;
        unsafe { ffi::kissat_set_terminate(self.handle, std::ptr::null(), None) }
    }
}

impl Interrupt for Kissat<'_> {
    type Interrupter = Interrupter;

    fn interrupter(&mut self) -> Self::Interrupter {
        Interrupter {
            handle: self.handle,
        }
    }
}

/// An Interrupter for the Kissat solver
pub struct Interrupter {
    /// The C API handle
    handle: *mut KissatHandle,
}

unsafe impl Send for Interrupter {}
unsafe impl Sync for Interrupter {}

impl InterruptSolver for Interrupter {
    fn interrupt(&self) {
        unsafe { ffi::kissat_terminate(self.handle) }
    }
}

impl SolveStats for Kissat<'_> {
    fn stats(&self) -> SolverStats {
        self.stats.clone()
    }
}

impl Drop for Kissat<'_> {
    fn drop(&mut self) {
        unsafe { ffi::kissat_release(self.handle) }
    }
}

/// Possible Kissat configurations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Config {
    /// Default configuration
    Default,
    /// Basic CDCL solving ([`Config::Plain`] but no restarts, minimize, reduce)
    Basic,
    /// Plain CDCL solving without advanced techniques
    Plain,
    /// Target satisfiable instances
    SAT,
    /// Target unsatisfiable instances
    UNSAT,
}

impl fmt::Display for Config {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Config::Default => write!(f, "default"),
            Config::Basic => write!(f, "basic"),
            Config::Plain => write!(f, "plain"),
            Config::SAT => write!(f, "sat"),
            Config::UNSAT => write!(f, "unsat"),
        }
    }
}

/// Possible Kissat limits
#[derive(Debug)]
pub enum Limit {
    /// A limit on the number of conflicts
    Conflicts(c_uint),
    /// A limit on the number of decisions
    Decisions(c_uint),
}

impl fmt::Display for Limit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Limit::Conflicts(val) => write!(f, "conflicts ({})", val),
            Limit::Decisions(val) => write!(f, "decisions ({})", val),
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Config, Kissat, Limit};
    use rustsat::{
        lit,
        solvers::{Solve, SolverState, StateError},
    };

    rustsat_solvertests::basic_unittests!(Kissat);

    #[test]
    fn configure() {
        let mut solver = Kissat::default();
        solver.set_configuration(Config::Default).unwrap();
        solver.set_configuration(Config::Basic).unwrap();
        solver.set_configuration(Config::Plain).unwrap();
        solver.set_configuration(Config::SAT).unwrap();
        solver.set_configuration(Config::UNSAT).unwrap();
        solver.add_unit(lit![0]).unwrap();
        assert!(solver.set_configuration(Config::Default).is_err_and(|e| e
            .downcast::<StateError>()
            .unwrap()
            == StateError {
                required_state: SolverState::Configuring,
                actual_state: SolverState::Input
            }));
    }

    #[test]
    fn options() {
        let mut solver = Kissat::default();
        assert_eq!(solver.get_option("warmup").unwrap(), 1);
        solver.set_option("warmup", 0).unwrap();
        assert_eq!(solver.get_option("warmup").unwrap(), 0);
    }

    #[test]
    fn limit() {
        let mut solver = Kissat::default();
        solver.set_limit(Limit::Conflicts(100));
    }
}

mod ffi {
    use super::TermCallbackPtr;
    use core::ffi::{c_char, c_int, c_uint, c_void};
    use rustsat::solvers::ControlSignal;

    #[repr(C)]
    pub struct KissatHandle {
        _private: [u8; 0],
    }

    extern "C" {
        // Redefinitions of Kissat API
        pub fn kissat_signature() -> *const c_char;
        pub fn kissat_init() -> *mut KissatHandle;
        pub fn kissat_release(solver: *mut KissatHandle);
        pub fn kissat_add(solver: *mut KissatHandle, lit_or_zero: c_int);
        pub fn kissat_solve(solver: *mut KissatHandle) -> c_int;
        pub fn kissat_value(solver: *mut KissatHandle, lit: c_int) -> c_int;
        pub fn kissat_set_terminate(
            solver: *mut KissatHandle,
            state: *const c_void,
            terminate: Option<extern "C" fn(state: *const c_void) -> c_int>,
        );
        pub fn kissat_terminate(solver: *mut KissatHandle);
        pub fn kissat_reserve(solver: *mut KissatHandle, max_var: c_int);
        pub fn kissat_id() -> *const c_char;
        pub fn kissat_version() -> *const c_char;
        pub fn kissat_compiler() -> *const c_char;
        pub fn kissat_set_option(
            solver: *mut KissatHandle,
            name: *const c_char,
            val: c_int,
        ) -> c_int;
        pub fn kissat_get_option(solver: *mut KissatHandle, name: *const c_char) -> c_int;
        pub fn kissat_set_configuration(solver: *mut KissatHandle, name: *const c_char) -> c_int;
        pub fn kissat_set_conflict_limit(solver: *mut KissatHandle, limit: c_uint);
        pub fn kissat_set_decision_limit(solver: *mut KissatHandle, limit: c_uint);
        pub fn kissat_print_statistics(solver: *mut KissatHandle);
    }

    // Raw callbacks forwarding to user callbacks
    pub extern "C" fn kissat_terminate_cb(ptr: *const c_void) -> c_int {
        let cb = unsafe { &mut *(ptr as *mut TermCallbackPtr) };
        match cb() {
            ControlSignal::Continue => 0,
            ControlSignal::Terminate => 1,
        }
    }
}
