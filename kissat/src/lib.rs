//! # rustsat-kissat - Interface to the Kissat SAT Solver for RustSAT
//!
//! Armin Biere's SAT solver [Kissat](https://github.com/arminbiere/kissat) to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! **Note**: at the moment this crate is known to not work on Windows since Kissat is non-trivial to get to work on Windows.
//!
//! ## Features
//!
//! - `debug`: if this feature is enables, the C library will be built with debug functionality if the Rust project is built in debug mode
//! - `safe`: disable writing through `popen` for more safe usage of the library in applications
//! - `quiet`: exclude message and profiling code (logging too)
//!
//! ## Kissat Versions
//!
//! Kissat versions can be selected via cargo crate features.
//! The following Kissat versions are available:
//! - `v4-0-4`: [Version 4.0.4](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.4)
//! - `v4-0-3`: [Version 4.0.3](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.3)
//! - `v4-0-2`: [Version 4.0.2](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.2)
//! - `v4-0-1`: [Version 4.0.1](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.1)
//! - `v4-0-0`: [Version 4.0.0](https://github.com/arminbiere/kissat/releases/tag/rel-4.0.0)
//! - `v3-1-0`: [Version 3.1.0](https://github.com/arminbiere/kissat/releases/tag/rel-3.1.0)
//! - `v3-0-0`: [Version 3.0.0](https://github.com/arminbiere/kissat/releases/tag/rel-3.0.0)
//! - `sc2022-light`: [SAT Competition 2022 Light](https://github.com/arminbiere/kissat/releases/tag/sc2022-light)
//! - `sc2022-hyper`: [SAT Competition 2022 Hyper](https://github.com/arminbiere/kissat/releases/tag/sc2022-hyper)
//! - `sc2022-bulky`: [SAT Competition 2022 Bulky](https://github.com/arminbiere/kissat/releases/tag/sc2022-bulky)
//!
//! Without any features selected, the newest version will be used.
//! If conflicting Kissat versions are requested, the newest requested version will be selected.
//!
//! If the determined version is _not_ the newest available, and no custom source directory is
//! specified (see customization below), the Kissat source code is downloaded at compile time,
//! which requires network access.
//!
//! ## Customization
//!
//! In order to build a custom version of Kissat, this crate supports the `KISSAT_SRC_DIR`
//! environment variable.
//! If this is set, Kissat will be built from the path specified there.
//!
//! ## Minimum Supported Rust Version (MSRV)
//!
//! Currently, the MSRV is 1.87.0, the plan is to always support an MSRV that is at least a year
//! old.
//!
//! Bumps in the MSRV will _not_ be considered breaking changes. If you need a specific MSRV, make
//! sure to pin a precise version of RustSAT.
//!
//! Note that the specified minimum-supported Rust version only applies if the _newest_ version of
//! Kissat is build.
//! Older versions are pulled down via the [`git2`](https://crates.io/crates/git2) crate, which has
//! transitive dependencies that have a higher MSRV.

#![warn(clippy::pedantic)]
#![warn(missing_docs)]
#![warn(missing_debug_implementations)]

use core::ffi::{c_int, c_uint, c_void, CStr};
use std::{ffi::CString, fmt};

use rustsat::{
    solvers::{
        sat, ControlSignal, Interrupt, InterruptSolver, Solve, SolveStats, SolverResult,
        SolverState, SolverStats, StateError, Terminate,
    },
    types::{Cl, Clause, Lit, TernaryVal, Var},
    utils::Timer,
};
use thiserror::Error;

/// Fatal error returned if the Kissat API returns an invalid value
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
    handle: *mut ffi::kissat,
    state: InternalSolverState,
    terminate_cb: OptTermCallbackStore<'term>,
    stats: SolverStats,
}

impl fmt::Debug for Kissat<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Kissat")
            .field("handle", &self.handle)
            .field("state", &self.state)
            .field(
                "terminate_cb",
                if self.terminate_cb.is_some() {
                    &"some callback"
                } else {
                    &"no callback"
                },
            )
            .field("stats", &self.stats)
            .finish()
    }
}

unsafe impl Send for Kissat<'_> {}

impl Default for Kissat<'_> {
    fn default() -> Self {
        let solver = Self {
            handle: unsafe { ffi::kissat_init() },
            state: InternalSolverState::default(),
            terminate_cb: None,
            stats: SolverStats::default(),
        };
        let quiet = CString::new("quiet").unwrap();
        unsafe { ffi::kissat_set_option(solver.handle, quiet.as_ptr(), 1) };
        solver
    }
}

impl Kissat<'_> {
    #[expect(clippy::cast_precision_loss)]
    #[inline]
    fn update_avg_clause_len(&mut self, clause: &Cl) {
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
    }

    /// Gets the commit ID that Kissat was built from
    ///
    /// # Panics
    ///
    /// If the Kissat library returns an id that is invalid UTF-8.
    #[must_use]
    pub fn commit_id() -> &'static str {
        let c_chars = unsafe { ffi::kissat_id() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str.to_str().expect("Kissat id returned invalid UTF-8.")
    }

    /// Gets the Kissat version
    ///
    /// # Panics
    ///
    /// If the Kissat library returns a version that is invalid UTF-8.
    #[must_use]
    pub fn version() -> &'static str {
        let c_chars = unsafe { ffi::kissat_version() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Kissat version returned invalid UTF-8.")
    }

    /// Gets the compiler Kissat was built with
    ///
    /// # Panics
    ///
    /// If the Kissat library returns a compiler that is invalid UTF-8.
    #[must_use]
    pub fn compiler() -> &'static str {
        let c_chars = unsafe { ffi::kissat_compiler() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Kissat compiler returned invalid UTF-8.")
    }

    /// Sets a pre-defined configuration for Kissat's internal options
    ///
    /// # Errors
    ///
    /// - Returns [`StateError`] if the solver is not in [`SolverState::Configuring`]
    /// - Returns [`InvalidApiReturn`] if the C-API does not return `true`. This case can be
    ///   considered a bug in either the Kissat library or this crate.
    pub fn set_configuration(&mut self, config: Config) -> anyhow::Result<()> {
        if self.state != InternalSolverState::Configuring {
            return Err(StateError {
                required_state: SolverState::Configuring,
                actual_state: self.state.to_external(),
            }
            .into());
        }
        let config_name: &CStr = config.into();
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
    ///
    /// # Errors
    ///
    /// Returns [`InvalidApiReturn`] if the C-API does not return `true`. This is most likely due
    /// to a wrongly specified `name` or an invalid `value`.
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
    ///
    /// # Errors
    ///
    /// Returns [`InvalidApiReturn`] if the C-API does not return `true`. This is most likely due
    /// to a wrongly specified `name`.
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
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"));
    }
}

impl<'a, C> Extend<&'a C> for Kissat<'_>
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
        let start = Timer::now();
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

    fn add_clause_ref<C>(&mut self, clause: &C) -> anyhow::Result<()>
    where
        C: AsRef<Cl> + ?Sized,
    {
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
        let clause = clause.as_ref();
        // Update wrapper-internal state
        self.stats.n_clauses += 1;
        self.update_avg_clause_len(clause);
        clause.iter().for_each(|l| match self.stats.max_var {
            None => self.stats.max_var = Some(l.var()),
            Some(var) => {
                if l.var() > var {
                    self.stats.max_var = Some(l.var());
                }
            }
        });
        self.state = InternalSolverState::Input;
        // Call Kissat backend
        clause
            .iter()
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
        let cb_ptr =
            std::ptr::from_mut(self.terminate_cb.as_mut().unwrap().as_mut()).cast::<c_void>();
        unsafe { ffi::kissat_set_terminate(self.handle, cb_ptr, Some(ffi::kissat_terminate_cb)) }
    }

    fn detach_terminator(&mut self) {
        self.terminate_cb = None;
        unsafe { ffi::kissat_set_terminate(self.handle, std::ptr::null_mut(), None) }
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
#[derive(Debug)]
pub struct Interrupter {
    /// The C API handle
    handle: *mut ffi::kissat,
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

/// Interface to the Kissat solver
#[derive(Debug)]
pub struct KissatNewApi();

impl KissatNewApi {
    /// Gets the commit ID that Kissat was built from
    ///
    /// # Panics
    ///
    /// If the Kissat library returns an id that is invalid UTF-8.
    #[must_use]
    pub fn commit_id() -> &'static str {
        let c_chars = unsafe { ffi::kissat_id() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str.to_str().expect("Kissat id returned invalid UTF-8.")
    }

    /// Gets the Kissat version
    ///
    /// # Panics
    ///
    /// If the Kissat library returns a version that is invalid UTF-8.
    #[must_use]
    pub fn version() -> &'static str {
        let c_chars = unsafe { ffi::kissat_version() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Kissat version returned invalid UTF-8.")
    }

    /// Gets the compiler Kissat was built with
    ///
    /// # Panics
    ///
    /// If the Kissat library returns a compiler that is invalid UTF-8.
    #[must_use]
    pub fn compiler() -> &'static str {
        let c_chars = unsafe { ffi::kissat_compiler() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Kissat compiler returned invalid UTF-8.")
    }
}

/// Wrapper around the kissat handle that if it is dropped, releases the solver
#[derive(Debug)]
struct Handle(*mut ffi::kissat);

impl From<*mut ffi::kissat> for Handle {
    fn from(value: *mut ffi::kissat) -> Self {
        Self(value)
    }
}

impl Drop for Handle {
    fn drop(&mut self) {
        unsafe { ffi::kissat_release(self.0) }
    }
}

/// A Kissat Solver in different States
#[derive(Debug)]
pub struct KissatState<State> {
    handle: Handle,
    _state: State,
}

unsafe impl<State> Send for KissatState<State> where State: Send {}
unsafe impl<State> Sync for KissatState<State> where State: Sync {}

impl sat::Solve for KissatNewApi {
    type Init = KissatState<Init>;

    type Input = KissatState<Input>;

    type Sat = KissatState<Sat>;

    type Unsat = KissatState<Unsat>;

    type Unknown = KissatState<Unknown>;

    fn signature() -> &'static str {
        let c_chars = unsafe { ffi::kissat_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Kissat signature returned invalid UTF-8.")
    }
}

/// Kissat in the initialization state
#[derive(Debug)]
pub struct Init();

impl sat::Init for KissatState<Init> {
    type Config = Config;

    type Option = ();

    fn set_option(&mut self, _option: Self::Option) -> &mut Self {
        todo!()
    }
}

impl Default for KissatState<Init> {
    fn default() -> Self {
        let handle = unsafe { ffi::kissat_init() };
        assert!(
            !handle.is_null(),
            "kissat_init should never return a nullptr"
        );
        Self {
            handle: handle.into(),
            _state: Init(),
        }
    }
}

impl From<Config> for KissatState<Init> {
    fn from(value: Config) -> Self {
        let handle = unsafe { ffi::kissat_init() };
        assert!(
            !handle.is_null(),
            "kissat_init should never return a nullptr"
        );
        let config_name: &CStr = value.into();
        let ret = unsafe { ffi::kissat_set_configuration(handle, config_name.as_ptr()) };
        assert_eq!(ret, 0, "kissat_configure should always return 0");
        Self {
            handle: handle.into(),
            _state: Init(),
        }
    }
}

/// Kissat in the input state
#[derive(Debug)]
pub struct Input();

impl KissatState<Input> {
    /// Sets an internal limit for Kissat
    pub fn set_limit(&mut self, limit: Limit) {
        match limit {
            Limit::Conflicts(val) => unsafe { ffi::kissat_set_conflict_limit(self.handle.0, val) },
            Limit::Decisions(val) => unsafe { ffi::kissat_set_decision_limit(self.handle.0, val) },
        }
    }

    /// Prints the solver statistics from the Kissat backend
    pub fn print_stats(&self) {
        unsafe { ffi::kissat_print_statistics(self.handle.0) }
    }
}

impl sat::Input<KissatNewApi> for KissatState<Input> {
    type Option = ();

    fn set_option(&mut self, option: Self::Option) -> &mut Self {
        todo!();
        self
    }

    fn reserve(&mut self, max_var: Var) -> rustsat::MightMemout<&Self> {
        unsafe { ffi::kissat_reserve(self.handle.0, max_var.to_ipasir()) };
        Ok(self)
    }

    fn add_clause<C>(&mut self, clause: &C) -> rustsat::MightMemout<&Self>
    where
        C: AsRef<rustsat::types::Cl> + ?Sized,
    {
        let clause = clause.as_ref();
        for lit in clause {
            unsafe { ffi::kissat_add(self.handle.0, lit.to_ipasir()) };
        }
        unsafe { ffi::kissat_add(self.handle.0, 0) };
        Ok(self)
    }

    fn solve(self) -> rustsat::MightMemout<sat::SolveResult<KissatNewApi>> {
        let res = unsafe { ffi::kissat_solve(self.handle.0) };
        Ok(match res {
            0 => sat::SolveResult::Unknown(KissatState {
                handle: self.handle,
                _state: Unknown(),
            }),
            10 => sat::SolveResult::Sat(KissatState {
                handle: self.handle,
                _state: Sat(),
            }),
            20 => sat::SolveResult::Unsat(KissatState {
                handle: self.handle,
                _state: Unsat(),
            }),
            value => {
                unreachable!("kissat_solve call should never return {value}")
            }
        })
    }
}

impl rustsat::encodings::CollectClauses for KissatState<crate::Input> {
    fn n_clauses(&self) -> usize {
        todo!()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>,
    {
        use rustsat::solvers::sat::Input;
        for clause in cl_iter {
            self.move_clause(clause)?;
        }
        Ok(())
    }
}

impl From<KissatState<Init>> for KissatState<Input> {
    fn from(value: KissatState<Init>) -> Self {
        Self {
            handle: value.handle,
            _state: Input(),
        }
    }
}

impl Default for KissatState<Input> {
    fn default() -> Self {
        let handle = unsafe { ffi::kissat_init() };
        assert!(
            !handle.is_null(),
            "kissat_init should never return a nullptr"
        );
        Self {
            handle: handle.into(),
            _state: Input(),
        }
    }
}

impl FromIterator<Clause> for KissatState<Input> {
    fn from_iter<T: IntoIterator<Item = Clause>>(iter: T) -> Self {
        use rustsat::solvers::sat::Input;
        let mut slf = Self::default();
        for clause in iter {
            slf.move_clause(clause).expect("out of memory");
        }
        slf
    }
}

impl<'a> FromIterator<&'a Cl> for KissatState<Input> {
    fn from_iter<T: IntoIterator<Item = &'a Cl>>(iter: T) -> Self {
        use rustsat::solvers::sat::Input;
        let mut slf = Self::default();
        for clause in iter {
            slf.add_clause(clause).expect("out of memory");
        }
        slf
    }
}

impl TryFrom<rustsat::instances::Cnf> for KissatState<Input> {
    type Error = rustsat::OutOfMemory;

    fn try_from(value: rustsat::instances::Cnf) -> Result<Self, Self::Error> {
        use rustsat::solvers::sat::Input;
        let mut slf = Self::default();
        for clause in value {
            slf.move_clause(clause)?;
        }
        Ok(slf)
    }
}

impl Extend<Clause> for KissatState<Input> {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        use rustsat::solvers::sat::Input;
        for clause in iter {
            self.move_clause(clause).expect("out of memory");
        }
    }
}

impl<'a> Extend<&'a Cl> for KissatState<Input> {
    fn extend<T: IntoIterator<Item = &'a Cl>>(&mut self, iter: T) {
        use rustsat::solvers::sat::Input;
        for clause in iter {
            self.add_clause(clause).expect("out of memory");
        }
    }
}

/// Kissat in the sat state
#[derive(Debug)]
pub struct Sat();

impl sat::Sat for KissatState<crate::Sat> {
    fn variable_value(&self, var: Var) -> TernaryVal {
        let lit = var.pos_lit().to_ipasir();
        match unsafe { ffi::kissat_value(self.handle.0, lit) } {
            0 => TernaryVal::DontCare,
            p if p == lit => TernaryVal::True,
            n if n == -lit => TernaryVal::False,
            value => unreachable!("kissat_value should never return {value}"),
        }
    }

    fn literal_value(&self, lit: Lit) -> TernaryVal {
        let lit = lit.to_ipasir();
        match unsafe { ffi::kissat_value(self.handle.0, lit) } {
            0 => TernaryVal::DontCare,
            p if p == lit => TernaryVal::True,
            n if n == -lit => TernaryVal::False,
            value => unreachable!("kissat_value should never return {value}"),
        }
    }
}

/// Kissat in the unsat state
#[derive(Debug)]
pub struct Unsat();

/// Kissat in the unknown state
#[derive(Debug)]
pub struct Unknown();

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
    Sat,
    /// Target unsatisfiable instances
    Unsat,
}

impl From<&Config> for &'static CStr {
    fn from(value: &Config) -> Self {
        match value {
            Config::Default => c"default",
            Config::Basic => c"basic",
            Config::Plain => c"plain",
            Config::Sat => c"sat",
            Config::Unsat => c"unsat",
        }
    }
}

impl From<Config> for &'static CStr {
    fn from(value: Config) -> Self {
        (&value).into()
    }
}

impl fmt::Display for Config {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Config::Default => write!(f, "default"),
            Config::Basic => write!(f, "basic"),
            Config::Plain => write!(f, "plain"),
            Config::Sat => write!(f, "sat"),
            Config::Unsat => write!(f, "unsat"),
        }
    }
}

/// Possible Kissat limits
#[derive(Debug, Clone, Copy)]
pub enum Limit {
    /// A limit on the number of conflicts
    Conflicts(c_uint),
    /// A limit on the number of decisions
    Decisions(c_uint),
}

impl fmt::Display for Limit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Limit::Conflicts(val) => write!(f, "conflicts ({val})"),
            Limit::Decisions(val) => write!(f, "decisions ({val})"),
        }
    }
}

extern "C" fn rustsat_kissat_panic_instead_of_abort() {
    panic!("kissat called kissat_abort");
}

/// Changes Kissat's abort behavior to cause a Rust panic instead
pub fn panic_instead_of_abort() {
    unsafe {
        ffi::kissat_call_function_instead_of_abort(Some(rustsat_kissat_panic_instead_of_abort));
    };
}

/// Changes Kissat's abort behavior to call the given function instead
pub fn call_instead_of_abort(abort: Option<unsafe extern "C" fn()>) {
    unsafe { ffi::kissat_call_function_instead_of_abort(abort) };
}

#[cfg(test)]
mod test {
    use super::{Config, Kissat, Limit};
    use rustsat::{
        lit,
        solvers::{Solve, SolverState, StateError},
    };

    rustsat_solvertests::basic_unittests!(
        Kissat,
        "kissat-(sc2022-(light|hyper|bulky)|[major].[minor].[patch])"
    );

    mod new {
        use crate::KissatNewApi;
        rustsat_solvertests::new_basic_unittests!(
            KissatNewApi,
            "kissat-(sc2022-(light|hyper|bulky)|[major].[minor].[patch])"
        );
    }

    #[test]
    fn configure() {
        let mut solver = Kissat::default();
        solver.set_configuration(Config::Default).unwrap();
        solver.set_configuration(Config::Basic).unwrap();
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
    use core::ffi::{c_int, c_void};

    use rustsat::solvers::ControlSignal;

    use super::TermCallbackPtr;

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

    // Raw callbacks forwarding to user callbacks
    pub extern "C" fn kissat_terminate_cb(ptr: *mut c_void) -> c_int {
        let cb = unsafe { &mut *ptr.cast::<TermCallbackPtr>() };
        match cb() {
            ControlSignal::Continue => 0,
            ControlSignal::Terminate => 1,
        }
    }
}
