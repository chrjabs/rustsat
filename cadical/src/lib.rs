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
//! All CaDiCaL versions up to [Version 2.1.0](https://github.com/arminbiere/cadical/releases/tag/rel-2.0.0) are available.
//! For the full list of versions and the changelog see [the CaDiCaL releases](https://github.com/arminbiere/cadical/releases).
//!
//! Without any features selected, the newest version will be used.
//! If conflicting CaDiCaL versions are requested, the newest requested version will be selected.
//!
//! ## Customization
//!
//! In order to build a custom version of CaDiCaL, this crate supports two environment variables to
//! customize the C++ source code that CaDiCaL is built from.
//!
//! - `CADICAL_PATCHES` allows to specify a list of colon-separated paths to patch files that will
//!     be applied to the CaDiCaL source repository before building it. These patches are applied
//!     in order of appearance _after_ the patches of this crate have been applied.
//! - `CADICAL_SRC_DIR` allows for overriding where the C++ library is built from. By default this
//!     crate fetches the appropriate code from [the GitHub
//!     repo](https://github.com/arminbiere/cadical). If this variable is set, the directory specified
//!     there is used instead. Note that when using this variable, the crate will not apply any
//!     patches, the user is responsible for applying the appropriate and necessary patches from the
//!     [`patches/`](https://github.com/chrjabs/rustsat/tree/main/cadical/patches) directory.

#![warn(clippy::pedantic)]
#![warn(missing_docs)]

use core::ffi::{c_int, c_void, CStr};
use std::{cmp::Ordering, ffi::CString, fmt};

use cpu_time::ProcessTime;
use rustsat::solvers::{
    ControlSignal, FreezeVar, GetInternalStats, Interrupt, InterruptSolver, Learn, LimitConflicts,
    LimitDecisions, PhaseLit, Propagate, PropagateResult, Solve, SolveIncremental, SolveStats,
    SolverResult, SolverState, SolverStats, StateError, Terminate,
};
use rustsat::types::{Cl, Clause, Lit, TernaryVal, Var};
use thiserror::Error;

macro_rules! handle_oom {
    ($val:expr) => {{
        let val = $val;
        if val == $crate::ffi::OUT_OF_MEM {
            return anyhow::Context::context(
                Err(rustsat::OutOfMemory::ExternalApi),
                "cadical out of memory",
            );
        }
        val
    }};
    ($val:expr, noanyhow) => {{
        let val = $val;
        if val == $crate::ffi::OUT_OF_MEM {
            return Err(rustsat::OutOfMemory::ExternalApi);
        }
        val
    }};
}
pub(crate) use handle_oom;

/// Fatal error returned if the CaDiCaL API returns an invalid value
#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("cadical c-api returned an invalid value: {api_call} -> {value}")]
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
type LearnCallbackPtr<'a> = Box<dyn FnMut(Clause) + 'a>;
/// Double boxing is necessary to get thin pointers for casting
type OptTermCallbackStore<'a> = Option<Box<TermCallbackPtr<'a>>>;
/// Double boxing is necessary to get thin pointers for casting
type OptLearnCallbackStore<'a> = Option<Box<LearnCallbackPtr<'a>>>;

/// The CaDiCaL solver type
pub struct CaDiCaL<'term, 'learn> {
    handle: *mut ffi::CCaDiCaL,
    state: InternalSolverState,
    terminate_cb: OptTermCallbackStore<'term>,
    learner_cb: OptLearnCallbackStore<'learn>,
    stats: SolverStats,
}

unsafe impl Send for CaDiCaL<'_, '_> {}

impl Default for CaDiCaL<'_, '_> {
    fn default() -> Self {
        let handle = unsafe { ffi::ccadical_init() };
        assert!(
            !handle.is_null(),
            "not enough memory to initialize CaDiCaL solver"
        );
        let solver = Self {
            handle,
            state: InternalSolverState::default(),
            terminate_cb: None,
            learner_cb: None,
            stats: SolverStats::default(),
        };
        let quiet = c"quiet";
        unsafe { ffi::ccadical_set_option_ret(solver.handle, quiet.as_ptr(), 1) };
        solver
    }
}

impl CaDiCaL<'_, '_> {
    fn get_core_assumps(&self, assumps: &[Lit]) -> Result<Vec<Lit>, InvalidApiReturn> {
        let mut core = Vec::new();
        for a in assumps {
            match unsafe { ffi::ccadical_failed(self.handle, a.to_ipasir()) } {
                0 => (),
                1 => core.push(!*a),
                value => {
                    return Err(InvalidApiReturn {
                        api_call: "ccadical_failed",
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

    /// Adds a clause that only exists for the next solver call. Only one such
    /// clause can exist, a new new clause replaces the old one.
    ///
    /// _Note_: If this is used, in addition to [`SolveIncremental::core`],
    /// [`CaDiCaL::tmp_clause_in_core`] needs to be checked to determine if the
    /// temporary clause is part of the core.
    ///
    /// # Errors
    ///
    /// Returns [`rustsat::OutOfMemory`] if CaDiCaL throws `std::bad_alloc`.
    pub fn add_tmp_clause<C>(&mut self, clause: &C) -> Result<(), rustsat::OutOfMemory>
    where
        C: AsRef<Cl> + ?Sized,
    {
        let clause = clause.as_ref();
        // Update wrapper-internal state
        self.stats.n_clauses += 1;
        self.update_avg_clause_len(clause);
        self.state = InternalSolverState::Input;
        // Call CaDiCaL backend
        for lit in clause {
            handle_oom!(
                unsafe { ffi::ccadical_constrain_mem(self.handle, lit.to_ipasir()) },
                noanyhow
            );
        }
        handle_oom!(
            unsafe { ffi::ccadical_constrain_mem(self.handle, 0) },
            noanyhow
        );
        Ok(())
    }

    /// Checks whether the temporary clause is part of the core if in
    /// unsatisfiable state. This needs to always be checked in addition to
    /// [`SolveIncremental::core`] if a [`CaDiCaL::add_tmp_clause`] is used.
    ///
    /// # Errors
    ///
    /// Returns [`StateError`] if the solver is not in [`SolverState::Unsat`].
    pub fn tmp_clause_in_core(&mut self) -> anyhow::Result<bool> {
        match &self.state {
            InternalSolverState::Unsat(_) => unsafe {
                Ok(ffi::ccadical_constraint_failed(self.handle) != 0)
            },
            state => Err(StateError {
                required_state: SolverState::Unsat,
                actual_state: state.to_external(),
            }
            .into()),
        }
    }

    /// Sets a pre-defined configuration for CaDiCaL's internal options
    ///
    /// # Errors
    ///
    /// - Returns [`StateError`] if the solver is not in [`SolverState::Configuring`]
    /// - Returns [`InvalidApiReturn`] if the C-API does not return `true`. This case can be
    ///   considered a bug in either the CaDiCaL library or this crate.
    pub fn set_configuration(&mut self, config: Config) -> anyhow::Result<()> {
        if self.state == InternalSolverState::Configuring {
            let config_name: &CStr = config.into();
            let ret = unsafe { ffi::ccadical_configure(self.handle, config_name.as_ptr()) };
            if ret != 0 {
                Ok(())
            } else {
                Err(InvalidApiReturn {
                    api_call: "ccadical_configure",
                    value: 0,
                }
                .into())
            }
        } else {
            Err(StateError {
                required_state: SolverState::Configuring,
                actual_state: self.state.to_external(),
            }
            .into())
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
    ///
    /// # Errors
    ///
    /// Returns [`InvalidApiReturn`] if the C-API does not return `true`. This is most likely due
    /// to a wrongly specified `name` or an invalid `value`.
    pub fn set_option(&mut self, name: &str, value: c_int) -> anyhow::Result<()> {
        let c_name = CString::new(name)?;
        if unsafe { ffi::ccadical_set_option_ret(self.handle, c_name.as_ptr(), value) } != 0 {
            Ok(())
        } else {
            Err(InvalidApiReturn {
                api_call: "ccadical_set_option_ret",
                value: 0,
            }
            .into())
        }
    }

    /// Gets the value of a CaDiCaL option. For possible options, check CaDiCaL with `cadical --help`.
    ///
    /// # CaDiCaL Documentation
    ///
    /// Get the current value of the option `name`.  If `name` is invalid then
    /// zero is returned.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidApiReturn`] if the C-API does not return `true`. This is most likely due
    /// to a wrongly specified `name`.
    pub fn get_option(&self, name: &str) -> anyhow::Result<c_int> {
        let c_name = CString::new(name)?;
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
    ///
    /// # Errors
    ///
    /// Returns [`InvalidApiReturn`] if the C-API does not return `true`. This case can be
    /// considered a bug in either the CaDiCaL library or this crate.
    pub fn set_limit(&mut self, limit: Limit) -> anyhow::Result<()> {
        let (name, val) = limit.into();
        if unsafe { ffi::ccadical_limit_ret(self.handle, name.as_ptr(), val) } != 0 {
            Ok(())
        } else {
            Err(InvalidApiReturn {
                api_call: "ccadical_limit_ret",
                value: 0,
            }
            .into())
        }
    }

    /// Gets the number of active variables
    #[must_use]
    pub fn get_active(&self) -> i64 {
        unsafe { ffi::ccadical_active(self.handle) }
    }

    /// Gets the number of active irredundant clauses
    #[must_use]
    pub fn get_irredundant(&self) -> i64 {
        unsafe { ffi::ccadical_irredundant(self.handle) }
    }

    /// Gets the number of active redundant clauses
    #[must_use]
    pub fn get_redundant(&self) -> i64 {
        unsafe { ffi::ccadical_redundant(self.handle) }
    }

    /// Gets the current literal value at the root level
    #[must_use]
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

    /// Executes the given number of preprocessing rounds
    ///
    /// # CaDiCaL Documentation
    ///
    /// This function executes the given number of preprocessing rounds. It is
    /// similar to 'solve' with 'limits ("preprocessing", rounds)' except that
    /// no CDCL nor local search, nor lucky phases are executed.  The result
    /// values are also the same: 0=UNKNOWN, 10=SATISFIABLE, 20=UNSATISFIABLE.
    /// As 'solve' it resets current assumptions and limits before returning.
    /// The numbers of rounds should not be negative.  If the number of rounds
    /// is zero only clauses are restored (if necessary) and top level unit
    /// propagation is performed, which both take some time.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidApiReturn`] if the C-API returns an unexpected value. This case can be
    /// considered a bug in the CaDiCaL library or this crate.
    pub fn simplify(&mut self, rounds: u32) -> anyhow::Result<SolverResult> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        }
        if let InternalSolverState::Unsat(_) = self.state {
            return Ok(SolverResult::Unsat);
        }
        let rounds: c_int = rounds.try_into()?;
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
            value => Err(InvalidApiReturn {
                api_call: "ccadical_simplify",
                value,
            }
            .into()),
        }
    }

    /// Executes the given number of preprocessing rounds under assumptions
    ///
    /// # CaDiCaL Documentation
    ///
    /// This function executes the given number of preprocessing rounds. It is
    /// similar to 'solve' with 'limits ("preprocessing", rounds)' except that
    /// no CDCL nor local search, nor lucky phases are executed.  The result
    /// values are also the same: 0=UNKNOWN, 10=SATISFIABLE, 20=UNSATISFIABLE.
    /// As 'solve' it resets current assumptions and limits before returning.
    /// The numbers of rounds should not be negative.  If the number of rounds
    /// is zero only clauses are restored (if necessary) and top level unit
    /// propagation is performed, which both take some time.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidApiReturn`] if the C-API returns an unexpected value. This case can be
    /// considered a bug in the CaDiCaL library or this crate.
    pub fn simplify_assumps(
        &mut self,
        assumps: &[Lit],
        rounds: u32,
    ) -> anyhow::Result<SolverResult> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        }
        if let InternalSolverState::Unsat(_) = self.state {
            return Ok(SolverResult::Unsat);
        }
        let rounds: c_int = rounds.try_into()?;
        // Simplify with CaDiCaL backend under assumptions
        for a in assumps {
            handle_oom!(unsafe { ffi::ccadical_assume_mem(self.handle, a.to_ipasir()) });
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
            value => Err(InvalidApiReturn {
                api_call: "ccadical_simplify",
                value,
            }
            .into()),
        }
    }
}

impl Extend<Clause> for CaDiCaL<'_, '_> {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"));
    }
}

impl<'a, C> Extend<&'a C> for CaDiCaL<'_, '_>
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

impl Solve for CaDiCaL<'_, '_> {
    fn signature(&self) -> &'static str {
        let c_chars = unsafe { ffi::ccadical_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("CaDiCaL signature returned invalid UTF-8.")
    }

    fn reserve(&mut self, max_var: Var) -> anyhow::Result<()> {
        self.state = InternalSolverState::Input;
        handle_oom!(unsafe { ffi::ccadical_reserve(self.handle, max_var.to_ipasir()) });
        Ok(())
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
        // Solve with CaDiCaL backend
        let res = handle_oom!(unsafe { ffi::ccadical_solve_mem(self.handle) });
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
                api_call: "ccadical_solve",
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
        match unsafe { ffi::ccadical_val(self.handle, lit) } {
            0 => Ok(TernaryVal::DontCare),
            p if p == lit => Ok(TernaryVal::True),
            n if n == -lit => Ok(TernaryVal::False),
            // CaDiCaL returns -1 if variable is higher than max var
            -1 => Ok(TernaryVal::DontCare),
            value => Err(InvalidApiReturn {
                api_call: "ccadical_val",
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
        self.update_avg_clause_len(clause);
        self.state = InternalSolverState::Input;
        // Call CaDiCaL backend
        for &l in clause {
            handle_oom!(unsafe { ffi::ccadical_add_mem(self.handle, l.to_ipasir()) });
        }
        handle_oom!(unsafe { ffi::ccadical_add_mem(self.handle, 0) });
        Ok(())
    }
}

impl SolveIncremental for CaDiCaL<'_, '_> {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult> {
        let start = ProcessTime::now();
        // Solve with CaDiCaL backend
        for a in assumps {
            handle_oom!(unsafe { ffi::ccadical_assume_mem(self.handle, a.to_ipasir()) });
        }
        let res = handle_oom!(unsafe { ffi::ccadical_solve_mem(self.handle) });
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
                api_call: "ccadical_solve",
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
        let cb_ptr =
            std::ptr::from_mut(self.terminate_cb.as_mut().unwrap().as_mut()).cast::<c_void>();
        unsafe {
            ffi::ccadical_set_terminate(
                self.handle,
                cb_ptr,
                Some(ffi::rustsat_ccadical_terminate_cb),
            );
        }
    }

    fn detach_terminator(&mut self) {
        self.terminate_cb = None;
        unsafe { ffi::ccadical_set_terminate(self.handle, std::ptr::null_mut(), None) }
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
        let cb_ptr =
            std::ptr::from_mut(self.learner_cb.as_mut().unwrap().as_mut()).cast::<c_void>();
        unsafe {
            ffi::ccadical_set_learn(
                self.handle,
                cb_ptr,
                max_len.try_into().unwrap(),
                Some(ffi::rustsat_ccadical_learn_cb),
            );
        }
    }

    fn detach_learner(&mut self) {
        self.terminate_cb = None;
        unsafe { ffi::ccadical_set_learn(self.handle, std::ptr::null_mut(), 0, None) }
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
    handle: *mut ffi::CCaDiCaL,
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
    fn phase_lit(&mut self, lit: Lit) -> anyhow::Result<()> {
        unsafe { ffi::ccadical_phase(self.handle, lit.to_ipasir()) };
        Ok(())
    }

    /// Undoes the effect of a call to [`CaDiCaL::phase_lit`]
    fn unphase_var(&mut self, var: Var) -> anyhow::Result<()> {
        unsafe { ffi::ccadical_unphase(self.handle, var.to_ipasir()) };
        Ok(())
    }
}

impl FreezeVar for CaDiCaL<'_, '_> {
    fn freeze_var(&mut self, var: Var) -> anyhow::Result<()> {
        unsafe { ffi::ccadical_freeze(self.handle, var.to_ipasir()) };
        Ok(())
    }

    fn melt_var(&mut self, var: Var) -> anyhow::Result<()> {
        unsafe { ffi::ccadical_melt(self.handle, var.to_ipasir()) };
        Ok(())
    }

    fn is_frozen(&mut self, var: Var) -> anyhow::Result<bool> {
        Ok(unsafe { ffi::ccadical_frozen(self.handle, var.to_ipasir()) } != 0)
    }
}

// >= v1.5.4
#[cfg(all(
    not(feature = "v1-5-3"),
    not(feature = "v1-5-2"),
    not(feature = "v1-5-1"),
    not(feature = "v1-5-0")
))]
impl rustsat::solvers::FlipLit for CaDiCaL<'_, '_> {
    fn flip_lit(&mut self, lit: Lit) -> anyhow::Result<bool> {
        if self.state != InternalSolverState::Sat {
            return Err(StateError {
                required_state: SolverState::Sat,
                actual_state: self.state.to_external(),
            }
            .into());
        }
        Ok(unsafe { ffi::ccadical_flip(self.handle, lit.to_ipasir()) } != 0)
    }

    fn is_flippable(&mut self, lit: Lit) -> anyhow::Result<bool> {
        if self.state != InternalSolverState::Sat {
            return Err(StateError {
                required_state: SolverState::Sat,
                actual_state: self.state.to_external(),
            }
            .into());
        }
        Ok(unsafe { ffi::ccadical_flippable(self.handle, lit.to_ipasir()) } != 0)
    }
}

impl LimitConflicts for CaDiCaL<'_, '_> {
    fn limit_conflicts(&mut self, limit: Option<u32>) -> anyhow::Result<()> {
        self.set_limit(Limit::Conflicts(if let Some(limit) = limit {
            limit.try_into()?
        } else {
            -1
        }))
    }
}

impl LimitDecisions for CaDiCaL<'_, '_> {
    fn limit_decisions(&mut self, limit: Option<u32>) -> anyhow::Result<()> {
        self.set_limit(Limit::Decisions(if let Some(limit) = limit {
            limit.try_into()?
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

impl Propagate for CaDiCaL<'_, '_> {
    fn propagate(
        &mut self,
        assumps: &[Lit],
        phase_saving: bool,
    ) -> anyhow::Result<PropagateResult> {
        let start = ProcessTime::now();
        self.state = InternalSolverState::Input;
        // Propagate with cadical backend
        let assumps: Vec<_> = assumps.iter().map(|l| l.to_ipasir()).collect();
        let assump_ptr: *const c_int = &assumps[0];
        let mut props = Vec::new();
        let prop_ptr: *mut Vec<Lit> = &mut props;
        let res = handle_oom!(unsafe {
            ffi::ccadical_propcheck(
                self.handle,
                assump_ptr,
                assumps.len(),
                c_int::from(phase_saving),
                Some(ffi::rustsat_cadical_collect_lits),
                prop_ptr.cast::<std::os::raw::c_void>(),
            )
        });
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            10 => Ok(PropagateResult {
                propagated: props,
                conflict: false,
            }),
            20 => Ok(PropagateResult {
                propagated: props,
                conflict: true,
            }),
            value => Err(InvalidApiReturn {
                api_call: "ccadical_propcheck",
                value,
            }
            .into()),
        }
    }
}

impl SolveStats for CaDiCaL<'_, '_> {
    fn stats(&self) -> SolverStats {
        let max_var_idx = unsafe { ffi::ccadical_vars(self.handle) };
        let max_var = if max_var_idx > 0 {
            Some(Var::new(
                (max_var_idx - 1)
                    .try_into()
                    .expect("got negative number of vars from CaDiCaL"),
            ))
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
            Some(Var::new(
                (max_var_idx - 1)
                    .try_into()
                    .expect("got negative number of vars from CaDiCaL"),
            ))
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
    Sat,
    /// Set internal options to target unsatisfiable instances
    Unsat,
}

impl From<Config> for &'static CStr {
    fn from(value: Config) -> Self {
        (&value).into()
    }
}

impl From<&Config> for &'static CStr {
    fn from(value: &Config) -> Self {
        match value {
            Config::Default => c"default",
            Config::Plain => c"plain",
            Config::Sat => c"sat",
            Config::Unsat => c"unsat",
        }
    }
}

impl fmt::Display for Config {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let str = match self {
            Config::Default => "default",
            Config::Plain => "plain",
            Config::Sat => "sat",
            Config::Unsat => "unsat",
        };
        write!(f, "{str}")
    }
}

/// Possible CaDiCaL limits
#[derive(Debug, Clone, Copy)]
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

impl From<&Limit> for (&'static CStr, c_int) {
    fn from(val: &Limit) -> Self {
        match val {
            Limit::Terminate(val) => (c"terminate", *val),
            Limit::Conflicts(val) => (c"conflicts", *val),
            Limit::Decisions(val) => (c"decisions", *val),
            Limit::Preprocessing(val) => (c"preprocessing", *val),
            Limit::LocalSearch(val) => (c"localsearch", *val),
        }
    }
}

impl From<Limit> for (&'static CStr, c_int) {
    fn from(val: Limit) -> Self {
        (&val).into()
    }
}

impl fmt::Display for Limit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Limit::Terminate(val) => write!(f, "terminate ({val})"),
            Limit::Conflicts(val) => write!(f, "conflicts ({val})"),
            Limit::Decisions(val) => write!(f, "decisions ({val})"),
            Limit::Preprocessing(val) => write!(f, "preprocessing ({val})"),
            Limit::LocalSearch(val) => write!(f, "localsearch ({val})"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::{CaDiCaL, Config, Limit};
    use rustsat::{
        lit,
        solvers::{Solve, SolverState, StateError},
        types::TernaryVal,
        var,
    };

    rustsat_solvertests::basic_unittests!(CaDiCaL);
    rustsat_solvertests::termination_unittests!(CaDiCaL);
    rustsat_solvertests::learner_unittests!(CaDiCaL);
    rustsat_solvertests::freezing_unittests!(CaDiCaL);
    rustsat_solvertests::propagating_unittests!(CaDiCaL);

    #[test]
    fn configure() {
        let mut solver = CaDiCaL::default();
        solver.set_configuration(Config::Default).unwrap();
        solver.set_configuration(Config::Plain).unwrap();
        solver.set_configuration(Config::Sat).unwrap();
        solver.set_configuration(Config::Unsat).unwrap();
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
}

mod ffi {
    #![allow(non_upper_case_globals)]
    #![allow(non_camel_case_types)]
    #![allow(non_snake_case)]

    use core::ffi::{c_int, c_void};
    use std::slice;

    use rustsat::{solvers::ControlSignal, types::Lit};

    use super::{LearnCallbackPtr, TermCallbackPtr};

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

    // Raw callbacks forwarding to user callbacks
    pub extern "C" fn rustsat_ccadical_terminate_cb(ptr: *mut c_void) -> c_int {
        let cb = unsafe { &mut *ptr.cast::<TermCallbackPtr<'_>>() };
        match cb() {
            ControlSignal::Continue => 0,
            ControlSignal::Terminate => 1,
        }
    }

    pub extern "C" fn rustsat_ccadical_learn_cb(ptr: *mut c_void, clause: *mut c_int) {
        let cb = unsafe { &mut *ptr.cast::<LearnCallbackPtr<'_>>() };

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
        cb(clause);
    }

    pub extern "C" fn rustsat_cadical_collect_lits(vec: *mut c_void, lit: c_int) {
        let vec = vec.cast::<Vec<Lit>>();
        let lit = Lit::from_ipasir(lit).expect("got invalid IPASIR lit from CaDiCaL");
        unsafe { (*vec).push(lit) };
    }
}
