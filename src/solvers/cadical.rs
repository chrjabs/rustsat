//! # CaDiCaL Solver Interface
//!
//! Interface to the [CaDiCaL](https://github.com/arminbiere/cadical) incremental SAT solver.

use core::ffi::{c_int, c_void, CStr};
use std::{ffi::CString, fmt};

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
    avg_clause_len: f32,
    cpu_solve_time: f32,
}

impl<'a> CaDiCaL<'a> {
    /// Creates a new instance of CaDiCaL
    pub fn new() -> CaDiCaL<'a> {
        CaDiCaL {
            handle: unsafe { ffi::ccadical_init() },
            state: InternalSolverState::Configuring,
            terminate_cb: None,
            learner_cb: None,
            n_sat: 0,
            n_unsat: 0,
            n_terminated: 0,
            n_clauses: 0,
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

    /// Sets a pre-defined configuration for CaDiCaL's internal options
    pub fn set_configuration(&mut self, config: Config) -> Result<(), SolverError> {
        if self.state == InternalSolverState::Configuring {
            let config_name = match config {
                Config::Default => CString::new("default").unwrap(),
                Config::Plain => CString::new("plain").unwrap(),
                Config::SAT => CString::new("sat").unwrap(),
                Config::UNSAT => CString::new("unsat").unwrap(),
            };
            let ret = unsafe { ffi::ccadical_configure(self.handle, config_name.as_ptr()) };
            if ret {
                Ok(())
            } else {
                Err(SolverError::API(format!(
                    "ccadical_configure returned false"
                )))
            }
        } else {
            Err(SolverError::State(
                self.state.to_external(),
                SolverState::Configuring,
            ))
        }
    }

    /// Sets the value of a CaDiCaL option. For possible options, check CaDiCaL with `cadical --help`.
    /// Requires state [`SolverState::Configuring`].
    ///
    /// # CaDiCaL Documentation
    ///
    /// Explicit version of setting an option.  If the option `<name>` exists
    /// and `<val>` can be parsed then 'true' is returned.  If the option value
    /// is out of range the actual value is computed as the closest (minimum or
    /// maximum) value possible, but still `true` is returned.
    pub fn set_option(&mut self, name: &str, value: c_int) -> Result<(), SolverError> {
        let c_name = match CString::new(name) {
            Ok(cstr) => cstr,
            Err(_) => {
                return Err(SolverError::API(format!(
                    "CaDiCaL option {} cannot be converted to a C string",
                    name
                )))
            }
        };
        if unsafe { ffi::ccadical_set_option_ret(self.handle, c_name.as_ptr(), value) } {
            Ok(())
        } else {
            Err(SolverError::API(format!(
                "ccadical_set_option_ret returned false for option {}",
                name
            )))
        }
    }

    /// Gets the value of a CaDiCaL option. For possible options, check CaDiCaL with `cadical --help`.
    ///
    /// # CaDiCaL Documentation
    ///
    /// Get the current value of the option `name`.  If `name` is invalid then
    /// zero is returned.
    pub fn get_option(&self, name: &str) -> Result<c_int, SolverError> {
        let c_name = match CString::new(name) {
            Ok(cstr) => cstr,
            Err(_) => {
                return Err(SolverError::API(format!(
                    "CaDiCaL option {} cannot be converted to a C string",
                    name
                )))
            }
        };
        Ok(unsafe { ffi::ccadical_get_option(self.handle, c_name.as_ptr()) })
    }

    /// Sets an internal limit for CaDiCaL
    ///
    /// # CaDiCaL Documentation
    ///
    /// Specify search limits, where currently `name` can be "conflicts",
    /// "decisions", "preprocessing", or "localsearch".  The first two limits
    /// are unbounded by default.  Thus using a negative limit for conflicts or
    /// decisions switches back to the default of unlimited search (for that
    /// particular limit).  The preprocessing limit determines the number of
    /// preprocessing rounds, which is zero by default.  Similarly, the local
    /// search limit determines the number of local search rounds (also zero by
    /// default).  As with `set`, the return value denotes whether the limit
    /// `name` is valid.  These limits are only valid for the next `solve` or
    /// `simplify` call and reset to their default after `solve` returns (as
    /// well as overwritten and reset during calls to `simplify` and
    /// `lookahead`).  We actually also have an internal "terminate" limit
    /// which however should only be used for testing and debugging.
    pub fn set_limit(&mut self, limit: Limit) -> Result<(), SolverError> {
        let (name, val) = match limit {
            Limit::Terminate(val) => (CString::new("terminate").unwrap(), val),
            Limit::Conflicts(val) => (CString::new("conflicts").unwrap(), val),
            Limit::Decisions(val) => (CString::new("decisions").unwrap(), val),
            Limit::Preprocessing(val) => (CString::new("preprocessing").unwrap(), val),
            Limit::LocalSearch(val) => (CString::new("localsearch").unwrap(), val),
        };
        if unsafe { ffi::ccadical_limit_ret(self.handle, name.as_ptr(), val) } {
            Ok(())
        } else {
            Err(SolverError::API(format!(
                "ccadical_limit_ret returned false for limit {}",
                limit
            )))
        }
    }

    /// Gets the number of active variables
    pub fn get_active(&self) -> i64 {
        unsafe { ffi::ccadical_active(self.handle) }
    }

    /// Gets the number of active irredundant clauses
    pub fn get_irredundant(&self) -> i64 {
        unsafe { ffi::ccadical_irredundant(self.handle) }
    }

    /// Gets the number of active redundant clauses
    pub fn get_redundant(&self) -> i64 {
        unsafe { ffi::ccadical_redundant(self.handle) }
    }

    /// Gets the current literal value at the root level
    pub fn current_lit_val(&self, lit: Lit) -> TernaryVal {
        let int_val = unsafe { ffi::ccadical_fixed(self.handle, lit.to_ipasir()) };
        if int_val > 0 {
            TernaryVal::True
        } else if int_val < 0 {
            TernaryVal::False
        } else {
            TernaryVal::DontCare
        }
    }

    /// Asynchronously force the solver to terminate
    pub fn terminate(&mut self) {
        unsafe { ffi::ccadical_terminate(self.handle) }
    }

    /// Freezes a literal. See CaDiCaL documentation for more details.
    pub fn freeze_lit(&mut self, lit: Lit) {
        unsafe { ffi::ccadical_freeze(self.handle, lit.to_ipasir()) }
    }

    /// Melts a literal. See CaDiCaL documentation for more details.
    pub fn melt_lit(&mut self, lit: Lit) {
        unsafe { ffi::ccadical_melt(self.handle, lit.to_ipasir()) }
    }

    /// Checks if a literal is frozen. See CaDiCaL documentation for more details.
    pub fn is_frozen(&self, lit: Lit) -> bool {
        (unsafe { ffi::ccadical_frozen(self.handle, lit.to_ipasir()) }) != 0
    }

    /// Forces the default decision phase of a variable to a certain value
    pub fn phase_lit(&mut self, lit: Lit) {
        unsafe { ffi::ccadical_phase(self.handle, lit.to_ipasir()) }
    }

    /// Undoes the effect of a call to [`CaDiCaL::phase_lit`]
    pub fn unphase_lit(&mut self, lit: Lit) {
        unsafe { ffi::ccadical_unphase(self.handle, lit.to_ipasir()) }
    }

    /// Prints the solver statistics from the CaDiCaL backend
    pub fn print_stats(&self) {
        unsafe { ffi::ccadical_print_statistics(self.handle) }
    }

    pub fn simplify(&mut self, rounds: u32) -> Result<SolverResult, SolverError> {
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
        let rounds: c_int = match rounds.try_into() {
            Ok(val) => val,
            Err(_) => {
                return Err(SolverError::API(format!(
                    "rounds value {} does not fit into c_int",
                    rounds
                )))
            }
        };
        // Simplify with CaDiCaL backend
        match unsafe { ffi::ccadical_simplify_rounds(self.handle, rounds) } {
            0 => {
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.state = InternalSolverState::SAT;
                Ok(SolverResult::SAT)
            }
            20 => {
                self.state = InternalSolverState::UNSAT(vec![]);
                Ok(SolverResult::UNSAT)
            }
            invalid => Err(SolverError::API(format!(
                "ccadical_simplify returned invalid value: {}",
                invalid
            ))),
        }
    }

    pub fn simplify_assumps(
        &mut self,
        assumps: Vec<Lit>,
        rounds: u32,
    ) -> Result<SolverResult, SolverError> {
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
        let rounds: c_int = match rounds.try_into() {
            Ok(val) => val,
            Err(_) => {
                return Err(SolverError::API(format!(
                    "rounds value {} does not fit into c_int",
                    rounds
                )))
            }
        };
        // Simplify with CaDiCaL backend under assumptions
        for a in &assumps {
            unsafe { ffi::ccadical_assume(self.handle, a.to_ipasir()) }
        }
        match unsafe { ffi::ccadical_simplify_rounds(self.handle, rounds) } {
            0 => {
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.state = InternalSolverState::SAT;
                Ok(SolverResult::SAT)
            }
            20 => {
                self.state = InternalSolverState::UNSAT(vec![]);
                Ok(SolverResult::UNSAT)
            }
            invalid => Err(SolverError::API(format!(
                "ccadical_simplify returned invalid value: {}",
                invalid
            ))),
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
        let max_var_idx = unsafe { ffi::ccadical_vars(self.handle) };
        if max_var_idx > 0 {
            Some(Var::new((max_var_idx - 1) as usize))
        } else {
            None
        }
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

/// Possible CaDiCaL configurations
#[derive(Debug)]
pub enum Config {
    /// Set default advanced internal options
    Default,
    /// Disable all internal preprocessing options
    Plain,
    /// Set internal options to target satisfiable instances
    SAT,
    /// Set internal options to target unsatisfiable instances
    UNSAT,
}

impl fmt::Display for Config {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Config::Default => write!(f, "default"),
            Config::Plain => write!(f, "plain"),
            Config::SAT => write!(f, "sat"),
            Config::UNSAT => write!(f, "unsat"),
        }
    }
}

/// Possible CaDiCaL limits
#[derive(Debug)]
pub enum Limit {
    /// The number of calls to [`CaDiCaL::terminate`] before CaDiCaL terminates
    Terminate(c_int),
    /// A limit on the number of conflicts
    Conflicts(c_int),
    /// A limit on the number of decisions
    Decisions(c_int),
    /// A limit on the rounds of internal preprocessing
    Preprocessing(c_int),
    /// A limit on the internal local search
    LocalSearch(c_int),
}

impl fmt::Display for Limit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Limit::Terminate(val) => write!(f, "terminate ({})", val),
            Limit::Conflicts(val) => write!(f, "conflicts ({})", val),
            Limit::Decisions(val) => write!(f, "decisions ({})", val),
            Limit::Preprocessing(val) => write!(f, "preprocessing ({})", val),
            Limit::LocalSearch(val) => write!(f, "localsearch ({})", val),
        }
    }
}

#[cfg(test)]
mod test {
    use super::{CaDiCaL, Config, Limit};
    use crate::{
        lit,
        solvers::{ControlSignal, Solve, SolverError, SolverResult, SolverState},
        types::{Lit, TernaryVal},
    };

    #[test]
    fn build_destroy() {
        let _solver = CaDiCaL::new();
    }

    #[test]
    fn build_two() {
        let _solver1 = CaDiCaL::new();
        let _solver2 = CaDiCaL::new();
    }

    #[test]
    fn tiny_instance() {
        let mut solver = CaDiCaL::new();
        solver.add_binary(lit![0], !lit![1]);
        solver.add_binary(lit![1], !lit![2]);
        let ret = solver.solve();
        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::SAT),
        }
    }

    #[test]
    fn termination_callback() {
        let mut solver = CaDiCaL::new();
        solver.add_binary(lit![0], !lit![1]);
        solver.add_binary(lit![1], !lit![2]);
        solver.add_binary(lit![2], !lit![3]);
        solver.add_binary(lit![3], !lit![4]);
        solver.add_binary(lit![4], !lit![5]);
        solver.add_binary(lit![5], !lit![6]);
        solver.add_binary(lit![6], !lit![7]);
        solver.add_binary(lit![7], !lit![8]);
        solver.add_binary(lit![8], !lit![9]);

        solver.set_terminator(|| ControlSignal::Terminate);

        let ret = solver.solve();

        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::Interrupted),
        }

        // Note: since IPASIR doesn't specify _when_ the terminator callback needs
        // to be called, there is no guarantee that the callback is actually
        // called during solving. This might cause this test to fail with some solvers.
    }

    #[test]
    fn learner_callback() {
        let mut solver = CaDiCaL::new();
        solver.add_binary(lit![0], !lit![1]);
        solver.add_binary(lit![1], !lit![2]);
        solver.add_binary(lit![2], !lit![3]);
        solver.add_binary(lit![3], !lit![4]);
        solver.add_binary(lit![4], !lit![5]);
        solver.add_binary(lit![5], !lit![6]);
        solver.add_binary(lit![6], !lit![7]);
        solver.add_binary(lit![7], !lit![8]);
        solver.add_binary(lit![8], !lit![9]);
        solver.add_unit(lit![9]);
        solver.add_unit(!lit![0]);

        let mut cl_len = 0;
        let ret;

        solver.set_learner(
            |clause| {
                cl_len = clause.len();
            },
            10,
        );

        ret = solver.solve();

        drop(solver);

        // Note: it is hard to create a testing instance on which clause learning
        // actually happens and therefore it is not actually tested if the
        // callback is called

        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::UNSAT),
        }
    }

    #[test]
    fn configure() {
        let mut solver = CaDiCaL::new();
        solver.set_configuration(Config::Default).unwrap();
        solver.set_configuration(Config::Plain).unwrap();
        solver.set_configuration(Config::SAT).unwrap();
        solver.set_configuration(Config::UNSAT).unwrap();
        solver.add_unit(lit![0]);
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
        let mut solver = CaDiCaL::new();
        assert_eq!(solver.get_option("arena").unwrap(), 1);
        solver.set_option("arena", 0).unwrap();
        assert_eq!(solver.get_option("arena").unwrap(), 0);
    }

    #[test]
    fn limit() {
        let mut solver = CaDiCaL::new();
        solver.set_limit(Limit::Conflicts(100)).unwrap();
    }

    #[test]
    fn backend_stats() {
        let mut solver = CaDiCaL::new();
        solver.add_binary(lit![0], !lit![1]);
        solver.add_binary(lit![1], !lit![2]);
        solver.add_binary(lit![2], !lit![3]);
        solver.add_binary(lit![3], !lit![4]);
        solver.add_binary(lit![4], !lit![5]);
        solver.add_binary(lit![5], !lit![6]);
        solver.add_binary(lit![6], !lit![7]);
        solver.add_binary(lit![7], !lit![8]);
        solver.add_binary(lit![8], !lit![9]);

        assert_eq!(solver.get_active(), 10);
        assert_eq!(solver.get_irredundant(), 9);
        assert_eq!(solver.get_redundant(), 0);
        assert_eq!(solver.current_lit_val(lit![0]), TernaryVal::DontCare);
    }

    #[test]
    fn freezing() {
        let mut solver = CaDiCaL::new();
        solver.add_binary(lit![0], !lit![1]);

        solver.freeze_lit(lit![0]);

        assert_eq!(solver.is_frozen(lit![0]), true);

        solver.melt_lit(lit![0]);

        assert_eq!(solver.is_frozen(lit![0]), false);
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
        pub fn ccadical_set_option_ret(
            solver: *mut CaDiCaLHandle,
            name: *const c_char,
            val: c_int,
        ) -> bool;
        pub fn ccadical_get_option(solver: *mut CaDiCaLHandle, name: *const c_char) -> c_int;
        pub fn ccadical_limit_ret(
            solver: *mut CaDiCaLHandle,
            name: *const c_char,
            limit: c_int,
        ) -> bool;
        pub fn ccadical_print_statistics(solver: *mut CaDiCaLHandle);
        pub fn ccadical_active(solver: *mut CaDiCaLHandle) -> i64;
        pub fn ccadical_irredundant(solver: *mut CaDiCaLHandle) -> i64;
        pub fn ccadical_redundant(solver: *mut CaDiCaLHandle) -> i64;
        pub fn ccadical_fixed(solver: *mut CaDiCaLHandle, lit: c_int) -> c_int;
        pub fn ccadical_terminate(solver: *mut CaDiCaLHandle);
        pub fn ccadical_freeze(solver: *mut CaDiCaLHandle, lit: c_int);
        pub fn ccadical_frozen(solver: *mut CaDiCaLHandle, lit: c_int) -> c_int;
        pub fn ccadical_melt(solver: *mut CaDiCaLHandle, lit: c_int);
        pub fn ccadical_simplify_rounds(solver: *mut CaDiCaLHandle, rounds: c_int) -> c_int;
        pub fn ccadical_configure(solver: *mut CaDiCaLHandle, name: *const c_char) -> bool;
        pub fn ccadical_phase(solver: *mut CaDiCaLHandle, lit: c_int);
        pub fn ccadical_unphase(solver: *mut CaDiCaLHandle, lit: c_int);
        pub fn ccadical_vars(solver: *mut CaDiCaLHandle) -> c_int;
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
