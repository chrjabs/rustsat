//! # CaDiCaL Solver Interface
//!
//! Interface to the [CaDiCaL](https://github.com/arminbiere/cadical) incremental SAT solver.

use core::ffi::{c_void, CStr};

use super::{
    ControlSignal, IncrementalSolve, InternalSolverState, Solve, SolveStats, SolverError,
    SolverResult, SolverState,
};
use crate::types::{Clause, Lit, TernaryVal, Var};
use ffi::CaDiCaLHandle;

/// The CaDiCaL solver type
pub struct CaDiCaL<'a> {
    handle: *mut CaDiCaLHandle,
    state: InternalSolverState,
    terminate_cb: Option<Box<Box<dyn FnMut() -> ControlSignal + 'a>>>,
    learner_cb: Option<Box<Box<dyn FnMut(Vec<Lit>) + 'a>>>,
    n_sat: u32,
    n_unsat: u32,
    n_terminated: u32,
    n_clauses: u32,
    max_var: Option<Var>,
    avg_clause_len: f32,
    cpu_solve_time: f32,
}

impl<'a> CaDiCaL<'a> {
    /// Creates a new instance of CaDiCaL
    pub fn new() -> CaDiCaL<'a> {
        CaDiCaL {
            handle: unsafe { ffi::ccadical_init() },
            state: InternalSolverState::Input,
            terminate_cb: None,
            learner_cb: None,
            n_sat: 0,
            n_unsat: 0,
            n_terminated: 0,
            n_clauses: 0,
            max_var: None,
            avg_clause_len: 0.0,
            cpu_solve_time: 0.0,
        }
    }

    /// Gets the signature of CaDiCaL
    pub fn signature(&self) -> &'static str {
        let c_chars = unsafe { ffi::ccadical_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("CaDiCaL signature returned invalid UTF-8.")
    }

    fn get_core_assumps(&self, assumps: &Vec<Lit>) -> Result<Vec<Lit>, SolverError> {
        let mut core = Vec::new();
        core.reserve(assumps.len());
        for a in assumps {
            match unsafe { ffi::ccadical_failed(self.handle, a.to_ipasir()) } {
                0 => (),
                1 => core.push(!*a),
                invalid => {
                    return Err(SolverError::API(format!(
                        "ccadical_failed returned invalid value: {}",
                        invalid
                    )))
                }
            }
        }
        Ok(core)
    }

    /// Sets a terminator callback that is regularly called during solving.
    ///
    /// # Examples
    ///
    /// Terminate solver after 10 callback calls.
    ///
    /// ```
    /// use rustsat::solvers::{CaDiCaL, ControlSignal, Solve, SolverResult};
    ///
    /// let mut solver = CaDiCaL::new();
    ///
    /// // Load instance
    ///
    /// let mut cnt = 1;
    /// solver.set_terminator(move || {
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
    pub fn set_terminator<CB>(&mut self, cb: CB)
    where
        CB: FnMut() -> ControlSignal + 'a,
    {
        self.terminate_cb = Some(Box::new(Box::new(cb)));
        let cb_ptr = self.terminate_cb.as_mut().unwrap().as_mut() as *const _ as *const c_void;
        unsafe { ffi::ccadical_set_terminate(self.handle, cb_ptr, ffi::ccadical_terminate_cb) }
    }

    /// Sets a learner callback that gets passed clauses up to a certain length learned by the solver.
    ///
    /// The callback goes out of scope with the solver, afterwards captured variables become accessible.
    ///
    /// # Examples
    ///
    /// Count number of learned clauses up to length 10.
    ///
    /// ```
    /// use rustsat::solvers::{CaDiCaL, Solve, SolverResult};
    ///
    /// let mut cnt = 0;
    ///
    /// {
    ///     let mut solver = CaDiCaL::new();
    ///     // Load instance
    ///
    ///     solver.set_learner(|_| cnt += 1, 10);
    ///
    ///     solver.solve().unwrap();
    /// }
    ///
    /// // cnt variable can be accessed from here on
    /// ```
    pub fn set_learner<CB>(&mut self, cb: CB, max_len: usize)
    where
        CB: FnMut(Vec<Lit>) + 'a,
    {
        self.learner_cb = Some(Box::new(Box::new(cb)));
        let cb_ptr = self.learner_cb.as_mut().unwrap().as_mut() as *const _ as *const c_void;
        unsafe {
            ffi::ccadical_set_learn(
                self.handle,
                cb_ptr,
                max_len.try_into().unwrap(),
                ffi::ccadical_learn_cb,
            )
        }
    }

    /// Adds a clause that only exists for the next solver call. Only one such
    /// clause can exist, a new new clause replaces the old one.
    ///
    /// _Note_: If this is used, in addition to [`IncrementalSolve::get_core`],
    /// [`CaDiCaL::tmp_clause_in_core`] needs to be checked to determine if the
    /// temporary clause is part of the core.
    pub fn add_tmp_clause(&mut self, clause: Clause) {
        if let InternalSolverState::Error(_) = self.state {
            // Don't add temporary clause if already in error state.
            return;
        }
        // Update wrapper-internal state
        self.n_clauses += 1;
        for lit in &clause {
            match self.max_var {
                None => self.max_var = Some(*lit.var()),
                Some(var) => {
                    if lit.var() > &var {
                        self.max_var = Some(*lit.var());
                    }
                }
            }
        }
        self.avg_clause_len = (self.avg_clause_len * ((self.n_clauses - 1) as f32)
            + clause.len() as f32)
            / self.n_clauses as f32;
        self.state = InternalSolverState::Input;
        // Call CaDiCaL backend
        for lit in &clause {
            unsafe { ffi::ccadical_constrain(self.handle, lit.to_ipasir()) }
        }
        unsafe { ffi::ccadical_constrain(self.handle, 0) }
    }

    /// Checks whether the temporary clause is part of the core if in
    /// unsatisfiable state. This needs to always be checked in addition to
    /// [`IncrementalSolve::get_core`] if a [`CaDiCaL::add_tmp_clause`] is used.
    pub fn tmp_clause_in_core(&mut self) -> Result<bool, SolverError> {
        match &self.state {
            InternalSolverState::UNSAT(_) => unsafe {
                Ok(ffi::ccadical_constraint_failed(self.handle) != 0)
            },
            state => Err(SolverError::State(state.to_external(), SolverState::UNSAT)),
        }
    }
}

impl Solve for CaDiCaL<'_> {
    fn solve(&mut self) -> Result<SolverResult, SolverError> {
        // If already solved, return state
        if let InternalSolverState::SAT = self.state {
            return Ok(SolverResult::SAT);
        } else if let InternalSolverState::UNSAT(_) = self.state {
            return Ok(SolverResult::UNSAT);
        } else if let InternalSolverState::Error(desc) = &self.state {
            return Err(SolverError::State(
                SolverState::Error(desc.clone()),
                SolverState::Input,
            ));
        }
        // Solve with CaDiCaL backend
        match unsafe { ffi::ccadical_solve(self.handle) } {
            0 => {
                self.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.n_sat += 1;
                self.state = InternalSolverState::SAT;
                Ok(SolverResult::SAT)
            }
            20 => {
                self.n_unsat += 1;
                self.state = InternalSolverState::UNSAT(vec![]);
                Ok(SolverResult::UNSAT)
            }
            invalid => Err(SolverError::API(format!(
                "ccadical_solve returned invalid value: {}",
                invalid
            ))),
        }
    }

    fn lit_val(&self, lit: &Lit) -> Result<TernaryVal, SolverError> {
        match &self.state {
            InternalSolverState::SAT => {
                let lit = lit.to_ipasir();
                match unsafe { ffi::ccadical_val(self.handle, lit) } {
                    0 => Ok(TernaryVal::DontCare),
                    p if p == lit => Ok(TernaryVal::True),
                    n if n == -lit => Ok(TernaryVal::False),
                    invalid => Err(SolverError::API(format!(
                        "ccadical_val returned invalid value: {}",
                        invalid
                    ))),
                }
            }
            other => Err(SolverError::State(other.to_external(), SolverState::SAT)),
        }
    }

    fn add_clause(&mut self, clause: Clause) {
        if let InternalSolverState::Error(_) = self.state {
            // Don't add clause if already in error state.
            return;
        }
        // Update wrapper-internal state
        self.n_clauses += 1;
        for lit in &clause {
            match self.max_var {
                None => self.max_var = Some(*lit.var()),
                Some(var) => {
                    if lit.var() > &var {
                        self.max_var = Some(*lit.var());
                    }
                }
            }
        }
        self.avg_clause_len = (self.avg_clause_len * ((self.n_clauses - 1) as f32)
            + clause.len() as f32)
            / self.n_clauses as f32;
        self.state = InternalSolverState::Input;
        // Call CaDiCaL backend
        for lit in &clause {
            unsafe { ffi::ccadical_add(self.handle, lit.to_ipasir()) }
        }
        unsafe { ffi::ccadical_add(self.handle, 0) }
    }
}

impl IncrementalSolve for CaDiCaL<'_> {
    fn solve_assumps(&mut self, assumps: Vec<Lit>) -> Result<SolverResult, SolverError> {
        // If in error state, remain there
        // If not, need to resolve because assumptions might have changed
        if let InternalSolverState::Error(desc) = &self.state {
            return Err(SolverError::State(
                SolverState::Error(desc.clone()),
                SolverState::Input,
            ));
        }
        // Solve with CaDiCaL backend
        for a in &assumps {
            unsafe { ffi::ccadical_assume(self.handle, a.to_ipasir()) }
        }
        match unsafe { ffi::ccadical_solve(self.handle) } {
            0 => {
                self.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.n_sat += 1;
                self.state = InternalSolverState::SAT;
                Ok(SolverResult::SAT)
            }
            20 => {
                self.n_unsat += 1;
                self.state = InternalSolverState::UNSAT(self.get_core_assumps(&assumps)?);
                Ok(SolverResult::UNSAT)
            }
            invalid => Err(SolverError::API(format!(
                "ccadical_solve returned invalid value: {}",
                invalid
            ))),
        }
    }

    fn get_core(&mut self) -> Result<Vec<Lit>, SolverError> {
        match &self.state {
            InternalSolverState::UNSAT(core) => Ok(core.clone()),
            other => Err(SolverError::State(other.to_external(), SolverState::UNSAT)),
        }
    }
}

impl SolveStats for CaDiCaL<'_> {
    fn get_n_sat_solves(&self) -> u32 {
        self.n_sat
    }

    fn get_n_unsat_solves(&self) -> u32 {
        self.n_unsat
    }

    fn get_n_terminated(&self) -> u32 {
        self.n_terminated
    }

    fn get_n_clauses(&self) -> u32 {
        self.n_clauses
    }

    fn get_max_var(&self) -> Option<Var> {
        self.max_var
    }

    fn get_avg_clause_len(&self) -> f32 {
        self.avg_clause_len
    }

    fn get_cpu_solve_time(&self) -> f32 {
        self.cpu_solve_time
    }
}

impl Drop for CaDiCaL<'_> {
    fn drop(&mut self) {
        unsafe { ffi::ccadical_release(self.handle) }
    }
}

mod ffi {
    use crate::solvers::ControlSignal;
    use crate::types::Lit;
    use core::ffi::{c_char, c_int, c_void};
    use std::{mem, slice};

    #[repr(C)]
    pub struct CaDiCaLHandle {
        _private: [u8; 0],
    }

    extern "C" {
        // Redefinitions of CaDiCaL C API
        pub fn ccadical_signature() -> *const c_char;
        pub fn ccadical_init() -> *mut CaDiCaLHandle;
        pub fn ccadical_release(solver: *mut CaDiCaLHandle);
        pub fn ccadical_add(solver: *mut CaDiCaLHandle, lit_or_zero: c_int);
        pub fn ccadical_assume(solver: *mut CaDiCaLHandle, lit: c_int);
        pub fn ccadical_solve(solver: *mut CaDiCaLHandle) -> c_int;
        pub fn ccadical_val(solver: *mut CaDiCaLHandle, lit: c_int) -> c_int;
        pub fn ccadical_failed(solver: *mut CaDiCaLHandle, lit: c_int) -> c_int;
        pub fn ccadical_set_terminate(
            solver: *mut CaDiCaLHandle,
            state: *const c_void,
            terminate: extern "C" fn(state: *const c_void) -> c_int,
        );
        pub fn ccadical_set_learn(
            solver: *mut CaDiCaLHandle,
            state: *const c_void,
            max_length: c_int,
            learn: extern "C" fn(state: *const c_void, clause: *const c_int),
        );
        pub fn ccadical_constrain(solver: *mut CaDiCaLHandle, lit: c_int);
        pub fn ccadical_constraint_failed(solver: *mut CaDiCaLHandle) -> c_int;
        pub fn ccadical_set_option(solver: *mut CaDiCaLHandle, name: *const c_char, val: c_int);
        pub fn ccadical_limit(solver: *mut CaDiCaLHandle, name: *const c_char, limit: c_int);
        pub fn ccadical_get_option(solver: *mut CaDiCaLHandle, name: *const c_char) -> c_int;
        pub fn ccadical_print_statistics(solver: *mut CaDiCaLHandle);
        pub fn ccadical_active(solver: *mut CaDiCaLHandle) -> i64;
        pub fn ccadical_irredundant(solver: *mut CaDiCaLHandle) -> i64;
        pub fn ccadical_fixed(solver: *mut CaDiCaLHandle, lit: c_int) -> c_int;
        pub fn ccadical_terminate(solver: *mut CaDiCaLHandle);
        pub fn ccadical_freeze(solver: *mut CaDiCaLHandle, lit: c_int);
        pub fn ccadical_frozen(solver: *mut CaDiCaLHandle, lit: c_int) -> c_int;
        pub fn ccadical_melt(solver: *mut CaDiCaLHandle, lit: c_int);
        pub fn ccadical_simplify(solver: *mut CaDiCaLHandle) -> c_int;
    }

    // Raw callbacks forwarding to user callbacks
    pub extern "C" fn ccadical_terminate_cb(ptr: *const c_void) -> c_int {
        let cb: &mut Box<dyn FnMut() -> ControlSignal> = unsafe { mem::transmute(ptr) };
        match cb() {
            ControlSignal::Continue => 0,
            ControlSignal::Terminate => 1,
        }
    }

    pub extern "C" fn ccadical_learn_cb(ptr: *const c_void, clause: *const c_int) {
        let cb: &mut Box<dyn FnMut(Vec<Lit>)> = unsafe { mem::transmute(ptr) };

        let mut cnt = 0;
        for n in 0.. {
            if unsafe { *clause.offset(n) } != 0 {
                cnt += 1;
            }
        }
        let int_slice = unsafe { slice::from_raw_parts(clause, cnt) };
        let clause: Vec<Lit> = int_slice
            .into_iter()
            .map(|il| {
                Lit::from_ipasir(*il).expect("Invalid literal in learned clause from CaDiCaL")
            })
            .collect();
        cb(clause)
    }
}
