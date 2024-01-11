//! # rustsat-cadical - Interface to the CaDiCaL SAT Solver for RustSAT
//!
//! Armin Biere's SAT solver [CaDiCaL](https://github.com/arminbiere/cadical) to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! **Note**: at the moment this crate is known to not work on Windows since CaDiCaL is non-trivial to get to work on Windows.
//!
//! ## Features
//!
//! - `debug`: if this feature is enables, the C++ library will be built with debug and check functionality if the Rust project is built in debug mode
//! - `safe`: disable writing through 'popen' for more safe usage of the library in applications
//! - `quiet`: exclude message and profiling code (logging too)
//! - `logging`: include logging code (but disabled by default)
//!
//! ## CaDiCaL Versions
//!
//! CaDiCaL versions can be selected via cargo crate features.
//! All CaDiCaL versions up to [Version 1.9.4](https://github.com/arminbiere/cadical/releases/tag/rel-1.9.4) are available.
//! For the full list of versions and the changelog see [the CaDiCaL releases](https://github.com/arminbiere/cadical/releases).
//!
//! Without any features selected, the newest version will be used.
//! If conflicting CaDiCaL versions are requested, the newest requested version will be selected.

use core::ffi::{c_int, c_void, CStr};
use std::{cmp::Ordering, ffi::CString, fmt};

use cpu_time::ProcessTime;
use ffi::CaDiCaLHandle;
use rustsat::solvers::{
    ControlSignal, FreezeVar, GetInternalStats, Interrupt, InterruptSolver, Learn, LimitConflicts,
    LimitDecisions, PhaseLit, Solve, SolveIncremental, SolveMightFail, SolveStats, SolverError,
    SolverResult, SolverState, SolverStats, Terminate,
};
use rustsat::types::{Clause, Lit, TernaryVal, Var};

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
type LearnCallbackPtr<'a> = Box<dyn FnMut(Clause) + 'a>;
/// Double boxing is necessary to get thin pointers for casting
type OptTermCallbackStore<'a> = Option<Box<TermCallbackPtr<'a>>>;
/// Double boxing is necessary to get thin pointers for casting
type OptLearnCallbackStore<'a> = Option<Box<LearnCallbackPtr<'a>>>;

/// The CaDiCaL solver type
pub struct CaDiCaL<'term, 'learn> {
    handle: *mut CaDiCaLHandle,
    state: InternalSolverState,
    terminate_cb: OptTermCallbackStore<'term>,
    learner_cb: OptLearnCallbackStore<'learn>,
    stats: SolverStats,
}

impl Default for CaDiCaL<'_, '_> {
    fn default() -> Self {
        let solver = Self {
            handle: unsafe { ffi::ccadical_init() },
            state: Default::default(),
            terminate_cb: Default::default(),
            learner_cb: Default::default(),
            stats: Default::default(),
        };
        let quiet = CString::new("quiet").unwrap();
        unsafe { ffi::ccadical_set_option_ret(solver.handle, quiet.as_ptr(), 1) };
        solver
    }
}

impl CaDiCaL<'_, '_> {
    fn get_core_assumps(&self, assumps: &[Lit]) -> Result<Vec<Lit>, SolverError> {
        let mut core = Vec::new();
        for a in assumps {
            match unsafe { ffi::ccadical_failed(self.handle, a.to_ipasir()) } {
                0 => (),
                1 => core.push(!*a),
                invalid => {
                    return Err(SolverError::Api(format!(
                        "ccadical_failed returned invalid value: {}",
                        invalid
                    )))
                }
            }
        }
        Ok(core)
    }

    /// Adds a clause that only exists for the next solver call. Only one such
    /// clause can exist, a new new clause replaces the old one.
    ///
    /// _Note_: If this is used, in addition to [`SolveIncremental::core`],
    /// [`CaDiCaL::tmp_clause_in_core`] needs to be checked to determine if the
    /// temporary clause is part of the core.
    pub fn add_tmp_clause(&mut self, clause: Clause) {
        // Update wrapper-internal state
        self.stats.n_clauses += 1;
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
        self.state = InternalSolverState::Input;
        // Call CaDiCaL backend
        for lit in &clause {
            unsafe { ffi::ccadical_constrain(self.handle, lit.to_ipasir()) }
        }
        unsafe { ffi::ccadical_constrain(self.handle, 0) }
    }

    /// Checks whether the temporary clause is part of the core if in
    /// unsatisfiable state. This needs to always be checked in addition to
    /// [`SolveIncremental::core`] if a [`CaDiCaL::add_tmp_clause`] is used.
    pub fn tmp_clause_in_core(&mut self) -> Result<bool, SolverError> {
        match &self.state {
            InternalSolverState::Unsat(_) => unsafe {
                Ok(ffi::ccadical_constraint_failed(self.handle) != 0)
            },
            state => Err(SolverError::State(state.to_external(), SolverState::Unsat)),
        }
    }

    /// Sets a pre-defined configuration for CaDiCaL's internal options
    pub fn set_configuration(&mut self, config: Config) -> SolveMightFail {
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
                Err(SolverError::Api(
                    "ccadical_configure returned false".to_string(),
                ))
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
    pub fn set_option(&mut self, name: &str, value: c_int) -> SolveMightFail {
        let c_name = match CString::new(name) {
            Ok(cstr) => cstr,
            Err(_) => {
                return Err(SolverError::Api(format!(
                    "CaDiCaL option {} cannot be converted to a C string",
                    name
                )))
            }
        };
        if unsafe { ffi::ccadical_set_option_ret(self.handle, c_name.as_ptr(), value) } {
            Ok(())
        } else {
            Err(SolverError::Api(format!(
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
                return Err(SolverError::Api(format!(
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
    pub fn set_limit(&mut self, limit: Limit) -> SolveMightFail {
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
            Err(SolverError::Api(format!(
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
        match int_val.cmp(&0) {
            Ordering::Greater => TernaryVal::True,
            Ordering::Less => TernaryVal::False,
            Ordering::Equal => TernaryVal::DontCare,
        }
    }

    /// Prints the solver statistics from the CaDiCaL backend
    pub fn print_stats(&self) {
        unsafe { ffi::ccadical_print_statistics(self.handle) }
    }

    pub fn simplify(&mut self, rounds: u32) -> Result<SolverResult, SolverError> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        } else if let InternalSolverState::Unsat(_) = self.state {
            return Ok(SolverResult::Unsat);
        }
        let rounds: c_int = match rounds.try_into() {
            Ok(val) => val,
            Err(_) => {
                return Err(SolverError::Api(format!(
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
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::Sat)
            }
            20 => {
                self.state = InternalSolverState::Unsat(vec![]);
                Ok(SolverResult::Unsat)
            }
            invalid => Err(SolverError::Api(format!(
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
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        } else if let InternalSolverState::Unsat(_) = self.state {
            return Ok(SolverResult::Unsat);
        }
        let rounds: c_int = match rounds.try_into() {
            Ok(val) => val,
            Err(_) => {
                return Err(SolverError::Api(format!(
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
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::Sat)
            }
            20 => {
                self.state = InternalSolverState::Unsat(vec![]);
                Ok(SolverResult::Unsat)
            }
            invalid => Err(SolverError::Api(format!(
                "ccadical_simplify returned invalid value: {}",
                invalid
            ))),
        }
    }
}

impl Extend<Clause> for CaDiCaL<'_, '_> {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"))
    }
}

impl Solve for CaDiCaL<'_, '_> {
    fn signature(&self) -> &'static str {
        let c_chars = unsafe { ffi::ccadical_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("CaDiCaL signature returned invalid UTF-8.")
    }

    fn reserve(&mut self, max_var: Var) -> SolveMightFail {
        self.state = InternalSolverState::Input;
        unsafe { ffi::ccadical_reserve(self.handle, max_var.to_ipasir()) };
        Ok(())
    }

    fn solve(&mut self) -> Result<SolverResult, SolverError> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        } else if let InternalSolverState::Unsat(core) = &self.state {
            if core.is_empty() {
                return Ok(SolverResult::Unsat);
            }
        }
        let start = ProcessTime::now();
        // Solve with CaDiCaL backend
        let res = unsafe { ffi::ccadical_solve(self.handle) };
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
            invalid => Err(SolverError::Api(format!(
                "ccadical_solve returned invalid value: {}",
                invalid
            ))),
        }
    }

    fn lit_val(&self, lit: Lit) -> Result<TernaryVal, SolverError> {
        match &self.state {
            InternalSolverState::Sat => {
                let lit = lit.to_ipasir();
                match unsafe { ffi::ccadical_val(self.handle, lit) } {
                    0 => Ok(TernaryVal::DontCare),
                    p if p == lit => Ok(TernaryVal::True),
                    n if n == -lit => Ok(TernaryVal::False),
                    // CaDiCaL returns -1 if variable is higher than max var
                    dc if dc == -1 => Ok(TernaryVal::DontCare),
                    invalid => Err(SolverError::Api(format!(
                        "ccadical_val returned invalid value: {}",
                        invalid
                    ))),
                }
            }
            other => Err(SolverError::State(other.to_external(), SolverState::Sat)),
        }
    }

    fn add_clause(&mut self, clause: Clause) -> SolveMightFail {
        // Update wrapper-internal state
        self.stats.n_clauses += 1;
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
        self.state = InternalSolverState::Input;
        // Call CaDiCaL backend
        clause
            .into_iter()
            .for_each(|l| unsafe { ffi::ccadical_add(self.handle, l.to_ipasir()) });
        unsafe { ffi::ccadical_add(self.handle, 0) };
        Ok(())
    }
}

impl SolveIncremental for CaDiCaL<'_, '_> {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> Result<SolverResult, SolverError> {
        let start = ProcessTime::now();
        // Solve with CaDiCaL backend
        for a in assumps {
            unsafe { ffi::ccadical_assume(self.handle, a.to_ipasir()) }
        }
        let res = unsafe { ffi::ccadical_solve(self.handle) };
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
            invalid => Err(SolverError::Api(format!(
                "ccadical_solve returned invalid value: {}",
                invalid
            ))),
        }
    }

    fn core(&mut self) -> Result<Vec<Lit>, SolverError> {
        match &self.state {
            InternalSolverState::Unsat(core) => Ok(core.clone()),
            other => Err(SolverError::State(other.to_external(), SolverState::Unsat)),
        }
    }
}

impl<'term> Terminate<'term> for CaDiCaL<'term, '_> {
    /// Sets a terminator callback that is regularly called during solving.
    ///
    /// # Examples
    ///
    /// Terminate solver after 10 callback calls.
    ///
    /// ```
    /// use rustsat::solvers::{ControlSignal, Solve, SolverResult, Terminate};
    /// use rustsat_cadical::CaDiCaL;
    ///
    /// let mut solver = CaDiCaL::default();
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
        unsafe {
            ffi::ccadical_set_terminate(self.handle, cb_ptr, Some(ffi::ccadical_terminate_cb))
        }
    }

    fn detach_terminator(&mut self) {
        self.terminate_cb = None;
        unsafe { ffi::ccadical_set_terminate(self.handle, std::ptr::null(), None) }
    }
}

impl<'learn> Learn<'learn> for CaDiCaL<'_, 'learn> {
    /// Sets a learner callback that gets passed clauses up to a certain length learned by the solver.
    ///
    /// The callback goes out of scope with the solver, afterwards captured variables become accessible.
    ///
    /// # Examples
    ///
    /// Count number of learned clauses up to length 10.
    ///
    /// ```
    /// use rustsat::solvers::{Solve, SolverResult, Learn};
    /// use rustsat_cadical::CaDiCaL;
    ///
    /// let mut cnt = 0;
    ///
    /// {
    ///     let mut solver = CaDiCaL::default();
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
        let cb_ptr = self.learner_cb.as_mut().unwrap().as_mut() as *const _ as *const c_void;
        unsafe {
            ffi::ccadical_set_learn(
                self.handle,
                cb_ptr,
                max_len.try_into().unwrap(),
                Some(ffi::ccadical_learn_cb),
            )
        }
    }

    fn detach_learner(&mut self) {
        self.terminate_cb = None;
        unsafe { ffi::ccadical_set_learn(self.handle, std::ptr::null(), 0, None) }
    }
}

impl Interrupt for CaDiCaL<'_, '_> {
    type Interrupter = Interrupter;
    fn interrupter(&mut self) -> Self::Interrupter {
        Interrupter {
            handle: self.handle,
        }
    }
}

/// An Interrupter for the CaDiCaL solver
pub struct Interrupter {
    /// The C API handle
    handle: *mut CaDiCaLHandle,
}

unsafe impl Send for Interrupter {}
unsafe impl Sync for Interrupter {}

impl InterruptSolver for Interrupter {
    fn interrupt(&self) {
        unsafe { ffi::ccadical_terminate(self.handle) }
    }
}

impl PhaseLit for CaDiCaL<'_, '_> {
    /// Forces the default decision phase of a variable to a certain value
    fn phase_lit(&mut self, lit: Lit) -> Result<(), SolverError> {
        unsafe { ffi::ccadical_phase(self.handle, lit.to_ipasir()) };
        Ok(())
    }

    /// Undoes the effect of a call to [`CaDiCaL::phase_lit`]
    fn unphase_var(&mut self, var: Var) -> Result<(), SolverError> {
        unsafe { ffi::ccadical_unphase(self.handle, var.to_ipasir()) };
        Ok(())
    }
}

impl FreezeVar for CaDiCaL<'_, '_> {
    fn freeze_var(&mut self, var: Var) -> Result<(), SolverError> {
        unsafe { ffi::ccadical_freeze(self.handle, var.pos_lit().to_ipasir()) };
        Ok(())
    }

    fn melt_var(&mut self, var: Var) -> Result<(), SolverError> {
        unsafe { ffi::ccadical_melt(self.handle, var.pos_lit().to_ipasir()) };
        Ok(())
    }

    fn is_frozen(&mut self, var: Var) -> Result<bool, SolverError> {
        Ok(unsafe { ffi::ccadical_frozen(self.handle, var.pos_lit().to_ipasir()) } != 0)
    }
}

// >= v1.5.4
#[cfg(any(
    feature = "v1-5-4",
    feature = "v1-5-5",
    feature = "v1-5-6",
    feature = "v1-6-0",
    feature = "v1-7-0",
    all(
        not(feature = "v1-5-3"),
        not(feature = "v1-5-2"),
        not(feature = "v1-5-1"),
        not(feature = "v1-5-0")
    )
))]
impl rustsat::solvers::FlipLit for CaDiCaL<'_, '_> {
    fn flip_lit(&mut self, lit: Lit) -> Result<bool, SolverError> {
        if self.state != InternalSolverState::Sat {
            return Err(SolverError::State(
                self.state.to_external(),
                SolverState::Sat,
            ));
        }
        Ok(unsafe { ffi::ccadical_flip(self.handle, lit.to_ipasir()) })
    }

    fn is_flippable(&mut self, lit: Lit) -> Result<bool, SolverError> {
        if self.state != InternalSolverState::Sat {
            return Err(SolverError::State(
                self.state.to_external(),
                SolverState::Sat,
            ));
        }
        Ok(unsafe { ffi::ccadical_flippable(self.handle, lit.to_ipasir()) })
    }
}

impl LimitConflicts for CaDiCaL<'_, '_> {
    fn limit_conflicts(&mut self, limit: Option<u32>) -> Result<(), SolverError> {
        self.set_limit(Limit::Conflicts(if let Some(limit) = limit {
            limit as c_int
        } else {
            -1
        }))
    }
}

impl LimitDecisions for CaDiCaL<'_, '_> {
    fn limit_decisions(&mut self, limit: Option<u32>) -> Result<(), SolverError> {
        self.set_limit(Limit::Decisions(if let Some(limit) = limit {
            limit as c_int
        } else {
            -1
        }))
    }
}

impl GetInternalStats for CaDiCaL<'_, '_> {
    fn propagations(&self) -> usize {
        unsafe { ffi::ccadical_propagations(self.handle) }
            .try_into()
            .unwrap()
    }

    fn decisions(&self) -> usize {
        unsafe { ffi::ccadical_decisions(self.handle) }
            .try_into()
            .unwrap()
    }

    fn conflicts(&self) -> usize {
        unsafe { ffi::ccadical_conflicts(self.handle) }
            .try_into()
            .unwrap()
    }
}

impl SolveStats for CaDiCaL<'_, '_> {
    fn stats(&self) -> SolverStats {
        let max_var_idx = unsafe { ffi::ccadical_vars(self.handle) };
        let max_var = if max_var_idx > 0 {
            Some(Var::new((max_var_idx - 1) as u32))
        } else {
            None
        };
        let mut stats = self.stats.clone();
        stats.max_var = max_var;
        stats
    }

    fn max_var(&self) -> Option<Var> {
        let max_var_idx = unsafe { ffi::ccadical_vars(self.handle) };
        if max_var_idx > 0 {
            Some(Var::new((max_var_idx - 1) as u32))
        } else {
            None
        }
    }
}

impl Drop for CaDiCaL<'_, '_> {
    fn drop(&mut self) {
        unsafe { ffi::ccadical_release(self.handle) }
    }
}

/// Possible CaDiCaL configurations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
    /// The number of calls to [`InterruptSolver::interrupt()`] before CaDiCaL terminates
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
    use rustsat::{
        lit,
        solvers::{
            ControlSignal, FreezeVar, Learn, Solve, SolverError, SolverResult, SolverState,
            Terminate,
        },
        types::TernaryVal,
        var,
    };

    #[test]
    fn build_destroy() {
        let _solver = CaDiCaL::default();
    }

    #[test]
    fn build_two() {
        let _solver1 = CaDiCaL::default();
        let _solver2 = CaDiCaL::default();
    }

    #[test]
    fn tiny_instance_sat() {
        let mut solver = CaDiCaL::default();
        solver.add_binary(lit![0], !lit![1]).unwrap();
        solver.add_binary(lit![1], !lit![2]).unwrap();
        let ret = solver.solve();
        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::Sat),
        }
    }

    #[test]
    fn tiny_instance_unsat() {
        let mut solver = CaDiCaL::default();
        solver.add_unit(!lit![0]).unwrap();
        solver.add_binary(lit![0], !lit![1]).unwrap();
        solver.add_binary(lit![1], !lit![2]).unwrap();
        solver.add_unit(lit![2]).unwrap();
        let ret = solver.solve();
        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::Unsat),
        }
    }

    #[test]
    fn termination_callback() {
        let mut solver = CaDiCaL::default();
        solver.add_binary(lit![0], !lit![1]).unwrap();
        solver.add_binary(lit![1], !lit![2]).unwrap();
        solver.add_binary(lit![2], !lit![3]).unwrap();
        solver.add_binary(lit![3], !lit![4]).unwrap();
        solver.add_binary(lit![4], !lit![5]).unwrap();
        solver.add_binary(lit![5], !lit![6]).unwrap();
        solver.add_binary(lit![6], !lit![7]).unwrap();
        solver.add_binary(lit![7], !lit![8]).unwrap();
        solver.add_binary(lit![8], !lit![9]).unwrap();

        solver.attach_terminator(|| ControlSignal::Terminate);

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
        let mut solver = CaDiCaL::default();
        solver.add_binary(lit![0], !lit![1]).unwrap();
        solver.add_binary(lit![1], !lit![2]).unwrap();
        solver.add_binary(lit![2], !lit![3]).unwrap();
        solver.add_binary(lit![3], !lit![4]).unwrap();
        solver.add_binary(lit![4], !lit![5]).unwrap();
        solver.add_binary(lit![5], !lit![6]).unwrap();
        solver.add_binary(lit![6], !lit![7]).unwrap();
        solver.add_binary(lit![7], !lit![8]).unwrap();
        solver.add_binary(lit![8], !lit![9]).unwrap();
        solver.add_unit(lit![9]).unwrap();
        solver.add_unit(!lit![0]).unwrap();

        let mut cl_len = 0;
        let ret;

        solver.attach_learner(
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
            Ok(res) => assert_eq!(res, SolverResult::Unsat),
        }
    }

    #[test]
    fn configure() {
        let mut solver = CaDiCaL::default();
        solver.set_configuration(Config::Default).unwrap();
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
        let mut solver = CaDiCaL::default();
        assert_eq!(solver.get_option("arena").unwrap(), 1);
        solver.set_option("arena", 0).unwrap();
        assert_eq!(solver.get_option("arena").unwrap(), 0);
    }

    #[test]
    fn limit() {
        let mut solver = CaDiCaL::default();
        solver.set_limit(Limit::Conflicts(100)).unwrap();
    }

    #[test]
    fn backend_stats() {
        let mut solver = CaDiCaL::default();
        solver.add_binary(lit![0], !lit![1]).unwrap();
        solver.add_binary(lit![1], !lit![2]).unwrap();
        solver.add_binary(lit![2], !lit![3]).unwrap();
        solver.add_binary(lit![3], !lit![4]).unwrap();
        solver.add_binary(lit![4], !lit![5]).unwrap();
        solver.add_binary(lit![5], !lit![6]).unwrap();
        solver.add_binary(lit![6], !lit![7]).unwrap();
        solver.add_binary(lit![7], !lit![8]).unwrap();
        solver.add_binary(lit![8], !lit![9]).unwrap();

        assert_eq!(solver.get_active(), 10);
        assert_eq!(solver.get_irredundant(), 9);
        assert_eq!(solver.get_redundant(), 0);
        assert_eq!(solver.current_lit_val(lit![0]), TernaryVal::DontCare);
    }

    #[test]
    fn freezing() {
        let mut solver = CaDiCaL::default();
        solver.add_binary(lit![0], !lit![1]).unwrap();

        solver.freeze_var(var![0]).unwrap();

        assert!(solver.is_frozen(var![0]).unwrap());

        solver.melt_var(var![0]).unwrap();

        assert!(!solver.is_frozen(var![0]).unwrap());
    }
}

mod ffi {
    use core::ffi::{c_char, c_int, c_void};
    use rustsat::{solvers::ControlSignal, types::Lit};
    use std::slice;

    use super::{LearnCallbackPtr, TermCallbackPtr};

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
            terminate: Option<extern "C" fn(state: *const c_void) -> c_int>,
        );
        pub fn ccadical_set_learn(
            solver: *mut CaDiCaLHandle,
            state: *const c_void,
            max_length: c_int,
            learn: Option<extern "C" fn(state: *const c_void, clause: *const c_int)>,
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
        pub fn ccadical_reserve(solver: *mut CaDiCaLHandle, min_max_var: c_int);
        pub fn ccadical_propagations(solver: *mut CaDiCaLHandle) -> i64;
        pub fn ccadical_decisions(solver: *mut CaDiCaLHandle) -> i64;
        pub fn ccadical_conflicts(solver: *mut CaDiCaLHandle) -> i64;
    }

    // >= v1.5.4
    #[cfg(any(
        feature = "v1-5-4",
        feature = "v1-5-5",
        feature = "v1-5-6",
        feature = "v1-6-0",
        feature = "v1-7-0",
        all(
            not(feature = "v1-5-3"),
            not(feature = "v1-5-2"),
            not(feature = "v1-5-1"),
            not(feature = "v1-5-0")
        )
    ))]
    extern "C" {
        pub fn ccadical_flip(solver: *mut CaDiCaLHandle, lit: c_int) -> bool;
        pub fn ccadical_flippable(solver: *mut CaDiCaLHandle, lit: c_int) -> bool;
    }

    // Raw callbacks forwarding to user callbacks
    pub extern "C" fn ccadical_terminate_cb(ptr: *const c_void) -> c_int {
        let cb = unsafe { &mut *(ptr as *mut TermCallbackPtr<'_>) };
        match cb() {
            ControlSignal::Continue => 0,
            ControlSignal::Terminate => 1,
        }
    }

    pub extern "C" fn ccadical_learn_cb(ptr: *const c_void, clause: *const c_int) {
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
                Lit::from_ipasir(*il).expect("Invalid literal in learned clause from CaDiCaL")
            })
            .collect();
        cb(clause)
    }
}
