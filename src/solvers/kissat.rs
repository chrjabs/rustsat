//! # Kissat Solver Interface
//!
//! Interface to the [Kissat](https://github.com/arminbiere/kissat) incremental SAT solver.

use core::ffi::{c_int, c_uint, c_void, CStr};
use std::{ffi::CString, fmt};

use super::{
    ControlSignal, InternalSolverState, Solve, SolveMightFail, SolveStats, SolverError,
    SolverResult, SolverState,
};
use crate::types::{Clause, Lit, TernaryVal, Var};
use ffi::KissatHandle;

/// The Kissat solver type
pub struct Kissat<'a> {
    handle: *mut KissatHandle,
    state: InternalSolverState,
    terminate_cb: Option<Box<Box<dyn FnMut() -> ControlSignal + 'a>>>,
    n_sat: u8,        // Since kissat is incremental, this should never be high
    n_unsat: u8,      // Since kissat is incremental, this should never be high
    n_terminated: u8, // Since kissat is incremental, this should never be high
    n_clauses: u32,
    max_var: Option<Var>,
    avg_clause_len: f32,
    cpu_solve_time: f32,
}

impl<'a> Kissat<'a> {
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

    /// Sets a terminator callback that is regularly called during solving.
    ///
    /// # Examples
    ///
    /// Terminate solver after 10 callback calls.
    ///
    /// ```
    /// use rustsat::solvers::{Kissat, ControlSignal, Solve, SolverResult};
    ///
    /// let mut solver = Kissat::new();
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
        unsafe { ffi::kissat_set_terminate(self.handle, cb_ptr, ffi::kissat_terminate_cb) }
    }

    /// Sets a pre-defined configuration for Kissat's internal options
    pub fn set_configuration(&mut self, config: Config) -> Result<(), SolverError> {
        if self.state == InternalSolverState::Configuring {
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
                Err(SolverError::API(format!("kissat_configure returned 0")))
            }
        } else {
            Err(SolverError::State(
                self.state.to_external(),
                SolverState::Configuring,
            ))
        }
    }

    /// Sets the value of a Kissat option. For possible options, check Kissat with `kissat --help`.
    /// Requires state [`SolverState::Configuring`].
    pub fn set_option(&mut self, name: &str, value: c_int) -> Result<(), SolverError> {
        let c_name = match CString::new(name) {
            Ok(cstr) => cstr,
            Err(_) => {
                return Err(SolverError::API(format!(
                    "Kissat option {} cannot be converted to a C string",
                    name
                )))
            }
        };
        if unsafe { ffi::kissat_set_option(self.handle, c_name.as_ptr(), value) } != 0 {
            Ok(())
        } else {
            Err(SolverError::API(format!(
                "kissat_set_option returned false for option {}",
                name
            )))
        }
    }

    /// Gets the value of a Kissat option. For possible options, check Kissat with `kissat --help`.
    pub fn get_option(&self, name: &str) -> Result<c_int, SolverError> {
        let c_name = match CString::new(name) {
            Ok(cstr) => cstr,
            Err(_) => {
                return Err(SolverError::API(format!(
                    "Kissat option {} cannot be converted to a C string",
                    name
                )))
            }
        };
        Ok(unsafe { ffi::kissat_get_option(self.handle, c_name.as_ptr()) })
    }

    /// Sets an internal limit for Kissat
    pub fn set_limit(&mut self, limit: Limit) {
        match limit {
            Limit::Conflicts(val) => unsafe { ffi::kissat_set_conflict_limit(self.handle, val) },
            Limit::Decisions(val) => unsafe { ffi::kissat_set_decision_limit(self.handle, val) },
        }
    }

    /// Asynchronously force the solver to terminate
    pub fn terminate(&mut self) {
        unsafe { ffi::kissat_terminate(self.handle) }
    }

    /// Prints the solver statistics from the Kissat backend
    pub fn print_stats(&self) {
        unsafe { ffi::kissat_print_statistics(self.handle) }
    }
}

impl<'a> Solve for Kissat<'a> {
    fn new() -> Self {
        let handle = unsafe { ffi::kissat_init() };
        // Suppress output by default
        let quiet = CString::new("quiet").unwrap();
        unsafe { ffi::kissat_set_option(handle, quiet.as_ptr(), 1) };
        Kissat {
            handle,
            state: InternalSolverState::Configuring,
            terminate_cb: None,
            n_sat: 0,
            n_unsat: 0,
            n_terminated: 0,
            n_clauses: 0,
            max_var: None,
            avg_clause_len: 0.0,
            cpu_solve_time: 0.0,
        }
    }

    fn signature(&self) -> &'static str {
        let c_chars = unsafe { ffi::kissat_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Kissat signature returned invalid UTF-8.")
    }

    fn reserve(&mut self, max_var: Var) -> SolveMightFail {
        self.state = match self.state {
            InternalSolverState::Error(_) => {
                return Err(SolverError::State(
                    self.state.to_external(),
                    SolverState::Input,
                ))
            }
            _ => InternalSolverState::Input,
        };
        Ok(unsafe { ffi::kissat_reserve(self.handle, max_var.to_ipasir()) })
    }

    fn solve(&mut self) -> Result<SolverResult, SolverError> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::SAT);
        } else if let InternalSolverState::Unsat(_) = self.state {
            return Ok(SolverResult::UNSAT);
        } else if let InternalSolverState::Error(desc) = &self.state {
            return Err(SolverError::State(
                SolverState::Error(desc.clone()),
                SolverState::Input,
            ));
        }
        // Solve with Kissat backend
        match unsafe { ffi::kissat_solve(self.handle) } {
            0 => {
                self.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.n_sat += 1;
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::SAT)
            }
            20 => {
                self.n_unsat += 1;
                self.state = InternalSolverState::Unsat(vec![]);
                Ok(SolverResult::UNSAT)
            }
            invalid => Err(SolverError::API(format!(
                "kissat_solve returned invalid value: {}",
                invalid
            ))),
        }
    }

    fn lit_val(&self, lit: &Lit) -> Result<TernaryVal, SolverError> {
        match &self.state {
            InternalSolverState::Sat => {
                let lit = lit.to_ipasir();
                match unsafe { ffi::kissat_value(self.handle, lit) } {
                    0 => Ok(TernaryVal::DontCare),
                    p if p == lit => Ok(TernaryVal::True),
                    n if n == -lit => Ok(TernaryVal::False),
                    invalid => Err(SolverError::API(format!(
                        "kissat_val returned invalid value: {}",
                        invalid
                    ))),
                }
            }
            other => Err(SolverError::State(other.to_external(), SolverState::SAT)),
        }
    }

    fn add_clause(&mut self, clause: Clause) -> Result<(), SolverError> {
        // Kissat is non-incremental, so only add if in input or configuring state
        match &mut self.state {
            InternalSolverState::Input | InternalSolverState::Configuring => (),
            InternalSolverState::Error(_) => {
                return Err(SolverError::State(
                    self.state.to_external(),
                    SolverState::Input,
                ))
            }
            other => {
                let old_state = other.to_external();
                // Transition into error state
                *other = InternalSolverState::Error(String::from(
                    "added clause while not in input state",
                ));
                return Err(SolverError::State(old_state, SolverState::Input));
            }
        }
        // Update wrapper-internal state
        self.n_clauses += 1;
        self.avg_clause_len = (self.avg_clause_len * ((self.n_clauses - 1) as f32)
            + clause.len() as f32)
            / self.n_clauses as f32;
        clause.iter().for_each(|l| match self.max_var {
            None => self.max_var = Some(l.var()),
            Some(var) => {
                if l.var() > var {
                    self.max_var = Some(l.var())
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

impl<'a> SolveStats for Kissat<'a> {
    fn get_n_sat_solves(&self) -> u32 {
        self.n_sat as u32
    }

    fn get_n_unsat_solves(&self) -> u32 {
        self.n_unsat as u32
    }

    fn get_n_terminated(&self) -> u32 {
        self.n_terminated as u32
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

impl<'a> Drop for Kissat<'a> {
    fn drop(&mut self) {
        unsafe { ffi::kissat_release(self.handle) }
    }
}

/// Possible Kissat configurations
#[derive(Debug)]
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
    use crate::{
        lit,
        solvers::{Solve, SolverError, SolverResult, SolverState},
        types::Lit,
    };

    #[test]
    fn build_destroy() {
        let _solver = Kissat::new();
    }

    #[test]
    fn build_two() {
        let _solver1 = Kissat::new();
        let _solver2 = Kissat::new();
    }

    #[test]
    fn tiny_instance() {
        let mut solver = Kissat::new();
        solver.add_binary(lit![0], !lit![1]).unwrap();
        solver.add_binary(lit![1], !lit![2]).unwrap();
        let ret = solver.solve();
        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::SAT),
        }
    }

    #[test]
    fn configure() {
        let mut solver = Kissat::new();
        solver.set_configuration(Config::Default).unwrap();
        solver.set_configuration(Config::Basic).unwrap();
        solver.set_configuration(Config::Plain).unwrap();
        solver.set_configuration(Config::SAT).unwrap();
        solver.set_configuration(Config::UNSAT).unwrap();
        solver.add_unit(lit![0]).unwrap();
        assert_eq!(
            solver.set_configuration(Config::Default),
            Err(SolverError::State(
                SolverState::Input,
                SolverState::Configuring
            ))
        );
    }

    #[test]
    fn options() {
        let mut solver = Kissat::new();
        assert_eq!(solver.get_option("warmup").unwrap(), 1);
        solver.set_option("warmup", 0).unwrap();
        assert_eq!(solver.get_option("warmup").unwrap(), 0);
    }

    #[test]
    fn limit() {
        let mut solver = Kissat::new();
        solver.set_limit(Limit::Conflicts(100));
    }
}

mod ffi {
    use crate::solvers::ControlSignal;
    use core::ffi::{c_char, c_int, c_uint, c_void};
    use std::mem;

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
            terminate: extern "C" fn(state: *const c_void) -> c_int,
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
        let cb: &mut Box<dyn FnMut() -> ControlSignal> = unsafe { mem::transmute(ptr) };
        match cb() {
            ControlSignal::Continue => 0,
            ControlSignal::Terminate => 1,
        }
    }
}
