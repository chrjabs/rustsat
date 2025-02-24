//! # Interfaces to SAT Solvers
//!
//! This module holds types and functions regarding SAT solvers. The main
//! element is the [`Solve`] trait that every SAT solver in this library
//! implements.
//!
//! ## Available Solvers
//!
//! Solvers are available through separate crates.
//!
//! ### CaDiCaL
//!
//! [CaDiCaL](https://github.com/arminbiere/cadical) is a fully incremental SAT
//! solver by Armin Biere implemented in Cpp. It includes incremental
//! inprocessing. It is available through the
//! [`rustsat-cadical`](https://crates.io/crates/rustsat-cadical) crate.
//!
//! #### References
//!
//! - Armin Biere and Katalin Fazekas and Mathias Fleury and Maximillian
//!   Heisinger: _CaDiCaL, Kissat, Paracooba, Plingeling and Treengeling
//!   Entering the SAT Competition 2020_, SAT Competition 2020.
//! - Original Repository:
//!   [`https://github.com/arminbiere/cadical`](https://github.com/arminbiere/cadical)
//! - Solver crate:
//!   [`https://crates.io/crates/rustsat-cadical`](https://crates.io/crates/rustsat-cadical)
//!
//! ### Kissat
//!
//! [Kissat](https://github.com/arminbiere/kissat) is a non-incremental SAT
//! solver by Armin Biere implemented in C. It is available through the
//! [`rustsat-kissat`](https://crates.io/crates/rustsat-kissat) crate.
//!
//! #### References
//!
//! - Armin Biere and Katalin Fazekas and Mathias Fleury and Maximillian
//!   Heisinger: _CaDiCaL, Kissat, Paracooba, Plingeling and Treengeling
//!   Entering the SAT Competition 2020_, SAT Competition 2020.
//! - Repository:
//!   [`https://github.com/arminbiere/kissat`](https://github.com/arminbiere/kissat)
//! - Solver crate:
//!   [`https://github.com/chrjabs/rustsat-kissat`](https://github.com/chrjabs/rustsat-kissat)
//!
//! ### Minisat
//!
//! [Minisat](https://github.com/niklasso/minisat) is an incremental SAT solver
//! by Niklas Eén and Niklas Sörensson. It is available through the
//! [`rustsat-minisat`](https://crates.io/crates/rustsat-minisat) crate.
//!
//! #### References
//!
//! - Niklas Eén and Niklas Sörensson (2003): _An Extensible SAT-solver_, SAT
//!   2003.
//! - Repository:
//!   [`https://github.com/niklasso/minisat`](https://github.com/niklasso/minisat)
//! - Solver crate:
//!   [`https://crates.io/crates/rustsat-minisat`](https://crates.io/crates/rustsat-minisat)
//! - Fork used in solver crate:
//!   [`https://github.com/chrjabs/minisat`](https://github.com/chrjabs/minisat)
//!
//! ### Glucose
//!
//! [Glucose](https://www.labri.fr/perso/lsimon/research/glucose/) is a SAT
//! solver based on Minisat and developed by Gilles Audemard and Laurent Simon.
//! It is available through the
//! [`rustsat-glucose`](https://crates.io/crates/rustsat-glucose) crate.
//!
//! #### References
//!
//! - Gilles Audemard and Laurent Simon: _Predicting Learnt Clauses Quality in
//!   Modern SAT Solvers_, IJCAI 2009.
//! - More references at the [Glucose
//!   web-page](https://www.labri.fr/perso/lsimon/research/glucose/)
//! - Solver crate:
//!   [`https://crates.io/crates/rustsat-glucose`](https://crates.io/crates/rustsat-glucose)
//! - Fork used in solver crate:
//!   [`https://github.com/chrjabs/glucose4`](https://github.com/chrjabs/glucose4)
//!
//! ### BatSat
//!
//! [BatSat](https://github.com/c-cube/batsat) is a SAT solver based on Minisat but fully
//! implemented in Rust. Because it is fully implemented in Rust, it is a good choice for
//! restricted compilation scenarios like WebAssembly. BatSat is available through the
//! [`rustsat-batsat`](httpe://crates.io/crates/rustsat-batsat) crate.
//!
//! #### References
//!
//! - Solver interface crate:
//!   [`https://crates.io/crates/rustsat-batsat`](https://crates.io/crate/rustsat-batsat)
//! - BatSat crate:
//!   [`https://crates.io/crates/batsat`](https://crates.io/crate/batsat)
//! - BatSat repository:
//!   [`https://github.com/c-cube/batsat`](https://github.com/c-cube/batsat)
//!
//! ### External Solvers
//!
//! RustSAT provides an interface for calling external solver binaries by passing them DIMACS input
//! and parsing their output written to `<stdout>`. For more details, see the [`ExternalSolver`]
//! type.
//!
//! ### IPASIR
//!
//! [IPASIR](https://github.com/biotomas/ipasir) is a C API for incremental SAT
//! solvers. IPASIR bindings for RustSAT are provided in the
//! [`rustsat-ipasir`](https://crates.io/crates/rustsat-ipasir) crate.

use crate::{
    clause,
    encodings::CollectClauses,
    instances::Cnf,
    lit,
    types::{Assignment, Cl, Clause, Lit, TernaryVal, Var},
};
use core::time::Duration;
use std::fmt;
use thiserror::Error;

pub mod external;
pub use external::Solver as ExternalSolver;

/// Trait for all SAT solvers in this library.
/// Solvers outside of this library can also implement this trait to be able to
/// use them with this library.
///
/// **Note**: the [`Extend`] implementations call [`Solve::add_clause`] or
/// [`Solve::add_clause_ref`] internally but _convert errors to panics_.
pub trait Solve: Extend<Clause> + for<'a> Extend<&'a Clause> {
    /// Gets a signature of the solver implementation
    #[must_use]
    fn signature(&self) -> &'static str;
    /// Reserves memory in the solver until a maximum variables, if the solver
    /// supports it
    ///
    /// # Errors
    ///
    /// A solver may return any error. One typical option might be [`crate::OutOfMemory`].
    fn reserve(&mut self, _max_var: Var) -> anyhow::Result<()> {
        Ok(())
    }
    /// Solves the internal CNF formula without any assumptions.
    ///
    /// # Example
    ///
    /// ```
    /// # use rustsat::{lit, solvers::{SolverResult, Solve}};
    /// // any other solver crate works the same way
    /// let mut solver = rustsat_minisat::core::Minisat::default();
    /// solver.add_unit(lit![0]).unwrap();
    /// let res = solver.solve().unwrap();
    /// debug_assert_eq!(res, SolverResult::Sat);
    /// ```
    ///
    /// # Errors
    ///
    /// A solver may return any error. One typical option might be [`crate::OutOfMemory`].
    fn solve(&mut self) -> anyhow::Result<SolverResult>;
    /// Gets a solution found by the solver up to a specified highest variable.
    ///
    /// # Errors
    ///
    /// - If the solver is not in the satisfied state, returns [`StateError`]
    /// - A specific implementation might return other errors
    fn solution(&self, high_var: Var) -> anyhow::Result<Assignment> {
        let mut assignment = Vec::new();
        let len = high_var.idx32() + 1;
        assignment.reserve(len as usize);
        for idx in 0..len {
            let lit = Lit::positive(idx);
            assignment.push(self.lit_val(lit)?);
        }
        Ok(Assignment::from(assignment))
    }
    /// Gets a solution found by the solver up to the highest variable known
    /// to the solver.
    ///
    /// # Errors
    ///
    /// - If the solver is not in the satisfied state, returns [`StateError`]
    /// - A specific implementation might return other errors
    fn full_solution(&self) -> anyhow::Result<Assignment>
    where
        Self: SolveStats,
    {
        if let Some(high_var) = self.max_var() {
            self.solution(high_var)
        } else {
            // throw error if in incorrect state
            self.lit_val(lit![0])?;
            Ok(Assignment::default())
        }
    }
    /// Same as [`Solve::lit_val`], but for variables.
    ///
    /// # Errors
    ///
    /// - If the solver is not in the satisfied state, returns [`StateError`]
    /// - A specific implementation might return other errors
    fn var_val(&self, var: Var) -> anyhow::Result<TernaryVal> {
        self.lit_val(var.pos_lit())
    }
    /// Gets an assignment of a variable in the solver.
    ///
    /// # Example
    ///
    /// ```
    /// # use rustsat::{lit, solvers::Solve, types::TernaryVal};
    /// // any other solver crate works the same way
    /// let mut solver = rustsat_minisat::core::Minisat::default();
    /// solver.add_unit(lit![0]).unwrap();
    /// let res = solver.solve().unwrap();
    /// debug_assert_eq!(solver.lit_val(lit![0]).unwrap(), TernaryVal::True);
    /// ```
    ///
    /// # Errors
    ///
    /// - If the solver is not in the satisfied state return [`StateError`]
    /// - A specific implementation might return other errors
    fn lit_val(&self, lit: Lit) -> anyhow::Result<TernaryVal>;
    /// Adds a clause to the solver.
    /// If the solver is in the satisfied or unsatisfied state before, it is in
    /// the input state afterwards.
    ///
    /// This method can be implemented by solvers that can truly take ownership of the clause.
    /// Otherwise, it will fall back to the mandatory [`Solve::add_clause_ref`] method.
    ///
    /// # Errors
    ///
    /// - If the solver is in an invalid state, returns [`StateError`]
    /// - A specific implementation might return other errors
    fn add_clause(&mut self, clause: Clause) -> anyhow::Result<()> {
        self.add_clause_ref(&clause)
    }
    /// Adds a clause to the solver by reference.
    /// If the solver is in the satisfied or unsatisfied state before, it is in
    /// the input state afterwards.
    ///
    /// # Errors
    ///
    /// - If the solver is in an invalid state, returns [`StateError`]
    /// - A specific implementation might return other errors
    // TODO: Maybe rename this to `add_clause` in the future and deprecate the version taking by
    // value
    fn add_clause_ref<C>(&mut self, clause: &C) -> anyhow::Result<()>
    where
        C: AsRef<Cl> + ?Sized;
    /// Like [`Solve::add_clause`] but for unit clauses (clauses with one literal).
    ///
    /// # Errors
    ///
    /// See [`Solve::add_clause`]
    fn add_unit(&mut self, lit: Lit) -> anyhow::Result<()> {
        self.add_clause(clause![lit])
    }
    /// Like [`Solve::add_clause`] but for clauses with two literals.
    ///
    /// # Errors
    ///
    /// See [`Solve::add_clause`]
    fn add_binary(&mut self, lit1: Lit, lit2: Lit) -> anyhow::Result<()> {
        self.add_clause(clause![lit1, lit2])
    }
    /// Like [`Solve::add_clause`] but for clauses with three literals.
    ///
    /// # Errors
    ///
    /// See [`Solve::add_clause`]
    fn add_ternary(&mut self, lit1: Lit, lit2: Lit, lit3: Lit) -> anyhow::Result<()> {
        self.add_clause(clause![lit1, lit2, lit3])
    }
    /// Adds all clauses from a [`Cnf`] instance.
    ///
    /// # Errors
    ///
    /// See [`Solve::add_clause`]
    fn add_cnf(&mut self, cnf: Cnf) -> anyhow::Result<()> {
        cnf.into_iter().try_for_each(|cl| self.add_clause(cl))
    }
    /// Adds all clauses from a [`Cnf`] instance by reference.
    ///
    /// # Errors
    ///
    /// See [`Solve::add_clause`]
    fn add_cnf_ref(&mut self, cnf: &Cnf) -> anyhow::Result<()> {
        cnf.iter().try_for_each(|cl| self.add_clause_ref(cl))
    }
}

/// Trait for all SAT solvers in this library.
/// Solvers outside of this library can also implement this trait to be able to
/// use them with this library.
pub trait SolveIncremental: Solve {
    /// Solves the internal CNF formula under assumptions.
    ///
    /// # Errors
    ///
    /// A solver may return any error. One typical option might be [`crate::OutOfMemory`].
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult>;
    /// Gets a core found by an unsatisfiable query.
    /// A core is a clause entailed by the formula that contains only inverted
    /// literals of the assumptions.
    ///
    /// # Errors
    ///
    /// - If the solver is not in the unsatisfied state, returns [`StateError`]
    /// - A specific implementation might return other errors
    fn core(&mut self) -> anyhow::Result<Vec<Lit>>;
}

/// Trait for all solvers that can be terminated by a termination callback.
pub trait Terminate<'term> {
    /// Attaches a termination callback to the solver. During solving this
    /// callback is regularly called and the solver terminates if the callback
    /// returns [`ControlSignal::Terminate`]. Only a single callback can be
    /// attached at any time, attaching a second callback drops the first one.
    fn attach_terminator<CB>(&mut self, cb: CB)
    where
        CB: FnMut() -> ControlSignal + 'term;
    /// Detaches the terminator
    fn detach_terminator(&mut self);
}

/// Trait for all solvers that can pass out learned clauses via a callback.
pub trait Learn<'learn> {
    /// Attaches a learner callback to the solver. This callback is called every
    /// time a clause of length up to `max_len` is learned.
    fn attach_learner<CB>(&mut self, cb: CB, max_len: usize)
    where
        CB: FnMut(Clause) + 'learn;
    /// Detaches the learner
    fn detach_learner(&mut self);
}

/// Trait for all solvers that can be asynchronously interrupt.
pub trait Interrupt {
    /// The interrupter of the solver
    type Interrupter: InterruptSolver + Send + 'static;
    /// Gets a thread safe interrupter object that can be used to terminate the solver
    #[must_use]
    fn interrupter(&mut self) -> Self::Interrupter;
}

/// A thread safe interrupter for a solver
pub trait InterruptSolver: Sync {
    /// Interrupts the solver asynchronously
    fn interrupt(&self);
}

/// Trait for all solvers that can force a face for a literal
pub trait PhaseLit {
    /// Forces the default decision phase of a variable to a certain value
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn phase_lit(&mut self, lit: Lit) -> anyhow::Result<()>;
    /// Undoes the effect of a call to [`PhaseLit::phase_lit`]
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn unphase_var(&mut self, var: Var) -> anyhow::Result<()>;
    /// Undoes the effect of a call to [`PhaseLit::phase_lit`]
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn unphase_lit(&mut self, lit: Lit) -> anyhow::Result<()> {
        self.unphase_var(lit.var())
    }
}

/// Trait for freezing and melting variables in solvers with pre-/inprocessing.
pub trait FreezeVar {
    /// Freezes a variable so that it is not removed in pre-/inprocessing
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn freeze_var(&mut self, var: Var) -> anyhow::Result<()>;
    /// Melts a variable after it had been frozen
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn melt_var(&mut self, var: Var) -> anyhow::Result<()>;
    /// Checks if a variable is frozen
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn is_frozen(&mut self, var: Var) -> anyhow::Result<bool>;
}

/// Trait for all solvers that can flip a literal in the current assignment
pub trait FlipLit {
    /// Attempts flipping the literal in the given assignment and returns `true` if successful
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn flip_lit(&mut self, lit: Lit) -> anyhow::Result<bool>;
    /// Checks if the literal can be flipped in the given assignment without flipping it
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn is_flippable(&mut self, lit: Lit) -> anyhow::Result<bool>;
}

/// Trait for all solvers that can limit the number of conflicts
pub trait LimitConflicts {
    /// Sets or removes a limit on the number of conflicts
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn limit_conflicts(&mut self, limit: Option<u32>) -> anyhow::Result<()>;
}

/// Trait for all solvers that can limit the number of decisions
pub trait LimitDecisions {
    /// Sets or removes a limit on the number of decisions
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn limit_decisions(&mut self, limit: Option<u32>) -> anyhow::Result<()>;
}

/// Trait for all solvers that can limit the number of propagations
pub trait LimitPropagations {
    /// Sets or removes a limit on the number of propagations
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn limit_propagations(&mut self, limit: Option<u32>) -> anyhow::Result<()>;
}

/// Trait for all solvers allowing access to internal search statistics
pub trait GetInternalStats {
    /// Gets the number of propagations
    #[must_use]
    fn propagations(&self) -> usize;
    /// Gets the number of decisions
    #[must_use]
    fn decisions(&self) -> usize;
    /// Gets the number of conflicts
    #[must_use]
    fn conflicts(&self) -> usize;
}

/// Trait for propagating a set of assumptions and getting all propagated literals
pub trait Propagate {
    /// Propagates the given assumptions and returns all propagated literals, as well as whether a
    /// conflict was encountered
    ///
    /// # Errors
    ///
    /// A solver may return any error.
    fn propagate(&mut self, assumps: &[Lit], phase_saving: bool)
        -> anyhow::Result<PropagateResult>;
}

/// A result returned from the [`Propagate`] trait
#[must_use]
pub struct PropagateResult {
    /// The list of propagated literals
    pub propagated: Vec<Lit>,
    /// Whether a conflict was encountered
    pub conflict: bool,
}

#[allow(dead_code)]
type TermCallbackPtr<'a> = Box<dyn FnMut() -> ControlSignal + 'a>;
#[allow(dead_code)]
type LearnCallbackPtr<'a> = Box<dyn FnMut(Clause) + 'a>;
#[allow(dead_code)]
/// Double boxing is necessary to get thin pointers for casting
type OptTermCallbackStore<'a> = Option<Box<TermCallbackPtr<'a>>>;
#[allow(dead_code)]
/// Double boxing is necessary to get thin pointers for casting
type OptLearnCallbackStore<'a> = Option<Box<LearnCallbackPtr<'a>>>;

/// Solver statistics
#[derive(Clone, PartialEq, Default)]
pub struct SolverStats {
    /// The number of satisfiable queries executed
    pub n_sat: usize,
    /// The number of unsatisfiable queries executed
    pub n_unsat: usize,
    /// The number of terminated queries executed
    pub n_terminated: usize,
    /// The number of clauses in the solver
    pub n_clauses: usize,
    /// The highest variable in the solver
    pub max_var: Option<Var>,
    /// The average length of the clauses added to the solver
    pub avg_clause_len: f32,
    /// The total CPU time spent solving
    pub cpu_solve_time: Duration,
}

/// Trait for solvers that track certain statistics.
pub trait SolveStats {
    /// Gets the available statistics from the solver
    #[must_use]
    fn stats(&self) -> SolverStats;
    /// Gets the number of satisfiable queries executed.
    #[must_use]
    fn n_sat_solves(&self) -> usize {
        self.stats().n_sat
    }
    /// Gets the number of unsatisfiable queries executed.
    #[must_use]
    fn n_unsat_solves(&self) -> usize {
        self.stats().n_unsat
    }
    /// Gets the number of queries that were prematurely terminated.
    #[must_use]
    fn n_terminated(&self) -> usize {
        self.stats().n_terminated
    }
    /// Gets the total number of queries executed.
    #[must_use]
    fn n_solves(&self) -> usize {
        self.n_sat_solves() + self.n_unsat_solves() + self.n_terminated()
    }
    /// Gets the number of clauses in the solver.
    #[must_use]
    fn n_clauses(&self) -> usize {
        self.stats().n_clauses
    }
    /// Gets the variable with the highest index in the solver, if any.
    ///
    /// If all variables below have been used, the index of this variable plus one is the number of
    /// variables in the solver.
    #[must_use]
    fn max_var(&self) -> Option<Var> {
        self.stats().max_var
    }
    /// Get number of variables.
    /// Note: this is only correct if all variables are used in order!
    #[must_use]
    fn n_vars(&self) -> usize {
        match self.max_var() {
            Some(var) => var.idx() + 1,
            None => 0,
        }
    }
    /// Gets the average length of all clauses in the solver.
    #[must_use]
    fn avg_clause_len(&self) -> f32 {
        self.stats().avg_clause_len
    }
    /// Gets the total CPU time spent solving.
    #[must_use]
    fn cpu_solve_time(&self) -> Duration {
        self.stats().cpu_solve_time
    }
}

/// States that the solver can be in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverState {
    /// Configuration of the solver must be done in this state, before any clauses are added
    Configuring,
    /// Input state, while adding clauses.
    Input,
    /// The query was found satisfiable.
    Sat,
    /// The query was found unsatisfiable.
    Unsat,
    /// Solving was terminated before a conclusion was reached
    Unknown,
}

impl fmt::Display for SolverState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverState::Configuring => write!(f, "CONFIGURING"),
            SolverState::Input => write!(f, "INPUT"),
            SolverState::Sat => write!(f, "SAT"),
            SolverState::Unsat => write!(f, "UNSAT"),
            SolverState::Unknown => write!(f, "UNKNOWN"),
        }
    }
}

/// Return value for solving queries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolverResult {
    /// The query was found satisfiable.
    Sat,
    /// The query was found unsatisfiable.
    Unsat,
    /// The query was prematurely interrupted.
    Interrupted,
}

impl fmt::Display for SolverResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverResult::Sat => write!(f, "SAT"),
            SolverResult::Unsat => write!(f, "UNSAT"),
            SolverResult::Interrupted => write!(f, "Interrupted"),
        }
    }
}

/// Return type for solver terminator callbacks
#[derive(Debug, PartialEq, Eq)]
pub enum ControlSignal {
    /// Variant for the solver to continue
    Continue,
    /// Variant for the solver to terminate
    Terminate,
}

/// A solver state error
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub struct StateError {
    /// The state required for the operation
    pub required_state: SolverState,
    /// The state that the solver is actually in
    pub actual_state: SolverState,
}

impl fmt::Display for StateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "action requires {} state, but solver is in state {}",
            self.required_state, self.actual_state
        )
    }
}

macro_rules! pass_oom_or_panic {
    ($result:expr) => {{
        match $result {
            Ok(res) => res,
            Err(err) => match err.downcast::<crate::OutOfMemory>() {
                Ok(oom) => return Err(oom),
                Err(err) => panic!("unexpected error in clause collector: {err}"),
            },
        }
    }};
}

impl<S: Solve + SolveStats> CollectClauses for S {
    fn n_clauses(&self) -> usize {
        self.n_clauses()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), crate::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>,
    {
        for cl in cl_iter {
            pass_oom_or_panic!(self.add_clause(cl));
        }
        Ok(())
    }

    fn add_clause(&mut self, cl: Clause) -> Result<(), crate::OutOfMemory> {
        pass_oom_or_panic!(self.add_clause(cl));
        Ok(())
    }
}
