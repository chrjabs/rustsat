//! # rustsat-cryptominisat - Interface to the CryptoMiniSat SAT Solver for RustSAT
//!
//! The CryptoMiniSat SAT solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! ## Features
//!
//! - `debug`: if this feature is enables, the Cpp library will be built with debug and check
//!     functionality if the Rust project is built in debug mode
//!
//! ## CryptoMiniSat Versions
//!
//! CryptoMiniSat versions can be selected via cargo crate features.
//! All CryptoMiniSat versions from
//! [Version 5.8.0](https://github.com/msoos/cryptominisat/releases/tag/5.8.0)
//! up to
//! [Version 5.11.21](https://github.com/msoos/cryptominisat/releases/tag/5.12.1)
//! are available. For the full list of versions and the changelog see
//! [the CryptoMiniSat releases](https://github.com/msoos/cryptominisat/releases).
//!
//! Without any features selected, the newest version will be used.
//! If conflicting CryptoMiniSat versions are requested, the newest requested version will be selected.
//!
//! If the determined version is _not_ the newest available, and no custom source directory is
//! specified (see customization below), the CryptoMiniSat source code is downloaded at compile time,
//! which requires network access.
//!
//! ## Customization
//!
//! In order to build a custom version of CaDiCaL, this crate supports two environment variables to
//! customize the Cpp source code that CaDiCaL is built from.
//!
//! - `CRYPTOMINISAT_SRC_DIR` allows for overriding where the Cpp library is built from. By default this
//!     crate fetches the appropriate code from [the GitHub
//!     repository](https://github.com/msoos/cryptominisat). If this variable is set, the directory specified
//!     there is used instead. Note that when using this variable, the crate will not apply any
//!     patches, the user is responsible for applying the appropriate and necessary patches from the
//!     [`patches/`](https://github.com/chrjabs/rustsat/tree/main/cadical/patches) directory.

#![warn(clippy::pedantic)]
#![warn(missing_docs)]

use std::cmp;

use cpu_time::ProcessTime;
use rustsat::{
    solvers::{
        Solve, SolveIncremental, SolveStats, SolverResult, SolverState, SolverStats, StateError,
    },
    types::{Cl, Clause, Lit, TernaryVal, Var},
};

#[derive(Debug, PartialEq, Eq, Default)]
enum InternalSolverState {
    #[default]
    Configuring,
    Input,
    Sat,
    Unsat,
}

impl InternalSolverState {
    fn to_external(&self) -> SolverState {
        match self {
            InternalSolverState::Configuring => SolverState::Configuring,
            InternalSolverState::Input => SolverState::Input,
            InternalSolverState::Sat => SolverState::Sat,
            InternalSolverState::Unsat => SolverState::Unsat,
        }
    }
}

/// The CryptoMiniSat solver type
pub struct CryptoMiniSat {
    handle: *mut ffi::SATSolver,
    state: InternalSolverState,
    stats: SolverStats,
}

unsafe impl Send for CryptoMiniSat {}

impl Default for CryptoMiniSat {
    fn default() -> Self {
        Self {
            handle: unsafe { ffi::cmsat_new() },
            state: InternalSolverState::default(),
            stats: SolverStats::default(),
        }
    }
}

impl CryptoMiniSat {
    #[allow(clippy::cast_precision_loss)]
    #[inline]
    fn update_avg_clause_len(&mut self, clause: &Cl) {
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
    }

    /// Set CryptoMiniSat options
    pub fn set_option(&mut self, option: Options) {
        match option {
            Options::NumThreads(n) => unsafe { ffi::cmsat_set_num_threads(self.handle, n) },
            Options::Verbosity(n) => unsafe { ffi::cmsat_set_verbosity(self.handle, n) },
            Options::DefaultPolarity(pol) => unsafe {
                ffi::cmsat_set_default_polarity(self.handle, i32::from(pol));
            },
            Options::NoSimplify => unsafe { ffi::cmsat_set_no_simplify(self.handle) },
            Options::NoSimplifyAtStartup => unsafe {
                ffi::cmsat_set_no_simplify_at_startup(self.handle);
            },
            Options::NoEquivalentLitReplacement => unsafe {
                ffi::cmsat_set_no_equivalent_lit_replacement(self.handle);
            },
            Options::NoBva => unsafe { ffi::cmsat_set_no_bva(self.handle) },
            Options::NoBve => unsafe { ffi::cmsat_set_no_bve(self.handle) },
            Options::MaxTime(max_time) => unsafe { ffi::cmsat_set_max_time(self.handle, max_time) },
        }
    }

    /// Adds an XOR clause to the solver
    ///
    /// # Errors
    ///
    /// If reserving variables fails
    pub fn add_xor_clause(&mut self, vars: &[Var], rhs: bool) -> anyhow::Result<()> {
        self.state = InternalSolverState::Input;
        if !vars.is_empty() {
            let max_var = vars
                .iter()
                .fold(Var::new(0), |max, var| cmp::max(max, *var));
            self.reserve(max_var)?;
        }
        let n_vars = vars.len();
        if !unsafe { ffi::cmsat_add_xor_clause(self.handle, vars.as_ptr().cast(), n_vars, rhs) } {
            self.state = InternalSolverState::Unsat;
        }
        Ok(())
    }
}

impl Solve for CryptoMiniSat {
    fn signature(&self) -> &'static str {
        "cryptominisat 5.11.21"
    }

    fn reserve(&mut self, max_var: Var) -> anyhow::Result<()> {
        let n_new = if let Some(solver_max) = self.max_var() {
            if solver_max > max_var {
                return Ok(());
            }
            max_var.idx() - solver_max.idx()
        } else {
            max_var.idx() + 1
        };
        unsafe { ffi::cmsat_new_vars(self.handle, n_new) };
        Ok(())
    }

    fn solve(&mut self) -> anyhow::Result<SolverResult> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        }
        if let InternalSolverState::Unsat = self.state {
            return Ok(SolverResult::Unsat);
        }
        let start = ProcessTime::now();
        // Solve with CryptoMiniSat backend
        let res: TernaryVal = unsafe { ffi::cmsat_solve(self.handle) }.into();
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            TernaryVal::True => {
                self.stats.n_sat += 1;
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::Sat)
            }
            TernaryVal::False => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::Unsat)
            }
            TernaryVal::DontCare => {
                self.stats.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
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
        Ok(ffi::lbool_slice(unsafe { ffi::cmsat_get_model(self.handle) })[lit.vidx()].into())
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
        if let Some(max_var) = clause.max_var() {
            self.reserve(max_var)?;
        }
        let clause = ffi::cms_lit_slice(clause.as_ref());
        if !unsafe { ffi::cmsat_add_clause(self.handle, clause.vals, clause.num_vals) } {
            self.state = InternalSolverState::Unsat;
        }
        Ok(())
    }
}

impl SolveIncremental for CryptoMiniSat {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult> {
        let start = ProcessTime::now();
        // Solve with CryptoMiniSat backend
        let assumps = ffi::cms_lit_slice(assumps);
        let res: TernaryVal = unsafe {
            ffi::cmsat_solve_with_assumptions(self.handle, assumps.vals, assumps.num_vals)
        }
        .into();
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            TernaryVal::True => {
                self.stats.n_sat += 1;
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::Sat)
            }
            TernaryVal::False => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::Unsat)
            }
            TernaryVal::DontCare => {
                self.stats.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
        }
    }

    fn core(&mut self) -> anyhow::Result<Vec<Lit>> {
        match &self.state {
            InternalSolverState::Unsat => Ok(Vec::from(ffi::lit_slice(unsafe {
                ffi::cmsat_get_conflict(self.handle)
            }))),
            other => Err(StateError {
                required_state: SolverState::Unsat,
                actual_state: other.to_external(),
            }
            .into()),
        }
    }
}

impl Extend<Clause> for CryptoMiniSat {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"));
    }
}

impl<'a, C> Extend<&'a C> for CryptoMiniSat
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

impl SolveStats for CryptoMiniSat {
    fn stats(&self) -> SolverStats {
        let max_var_idx = unsafe { ffi::cmsat_nvars(self.handle) };
        let max_var = if max_var_idx > 0 {
            Some(Var::new(max_var_idx - 1))
        } else {
            None
        };
        let mut stats = self.stats.clone();
        stats.max_var = max_var;
        stats
    }

    fn max_var(&self) -> Option<Var> {
        let max_var_idx = unsafe { ffi::cmsat_nvars(self.handle) };
        if max_var_idx > 0 {
            Some(Var::new(max_var_idx - 1))
        } else {
            None
        }
    }
}

impl Drop for CryptoMiniSat {
    fn drop(&mut self) {
        unsafe { ffi::cmsat_free(self.handle) }
    }
}

/// CryptoMiniSat configuration options
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Options {
    /// The number of threads
    NumThreads(u32),
    /// Verbosity
    Verbosity(u32),
    /// Default polarity
    DefaultPolarity(bool),
    /// No simplify
    NoSimplify,
    /// No simplify at start-up
    NoSimplifyAtStartup,
    /// No equivalent literal replacement
    NoEquivalentLitReplacement,
    /// No bounded variable addition
    NoBva,
    /// No bounded variable elimination
    NoBve,
    /// Maximum time
    MaxTime(f64),
}

#[cfg(test)]
mod test {
    rustsat_solvertests::basic_unittests!(super::CryptoMiniSat);

    #[test]
    fn options() {
        let mut solver = super::CryptoMiniSat::default();
        solver.set_option(super::Options::NumThreads(4));
        solver.set_option(super::Options::Verbosity(2));
        solver.set_option(super::Options::DefaultPolarity(false));
        solver.set_option(super::Options::NoSimplify);
        solver.set_option(super::Options::NoSimplifyAtStartup);
        solver.set_option(super::Options::NoEquivalentLitReplacement);
        solver.set_option(super::Options::NoBva);
        solver.set_option(super::Options::NoBve);
        solver.set_option(super::Options::MaxTime(100.));
    }
}

mod ffi {
    #![allow(non_upper_case_globals)]
    #![allow(non_camel_case_types)]
    #![allow(non_snake_case)]

    use rustsat::types::{Lit, TernaryVal};

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

    impl From<c_lbool> for TernaryVal {
        fn from(val: c_lbool) -> Self {
            match u32::from(val.x) {
                L_TRUE => TernaryVal::True,
                L_FALSE => TernaryVal::False,
                L_UNDEF => TernaryVal::DontCare,
                _ => unreachable!("invalid CryptoMiniSat c_lbool"),
            }
        }
    }

    pub fn lbool_slice<'a>(ffi_slice: slice_lbool) -> &'a [c_lbool] {
        unsafe { std::slice::from_raw_parts(ffi_slice.vals, ffi_slice.num_vals) }
    }

    pub fn lit_slice<'a>(ffi_slice: slice_Lit) -> &'a [Lit] {
        unsafe { std::slice::from_raw_parts(ffi_slice.vals.cast(), ffi_slice.num_vals) }
    }

    pub fn cms_lit_slice(cl: &[Lit]) -> slice_Lit {
        let num_vals = cl.len();
        let vals = cl.as_ptr();
        slice_Lit {
            vals: vals.cast(),
            num_vals,
        }
    }
}
