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
//! solver by Armin Biere implemented in C++. It includes incremental
//! inprocessing. It is available through the
//! [`rustsat-cadical`](https://crates.io/crates/rustsat-cadical) crate.
//!
//! #### References
//!
//! - Armin Biere and Katalin Fazekas and Mathias Fleury and Maximillian
//!   Heisinger: _CaDiCaL, Kissat, Paracooba, Plingeling and Treengeling
//!   Entering the SAT Competition 2020_, SAT Competition 2020.
//! - Original Repository:
//!   [https://github.com/arminbiere/cadical](https://github.com/arminbiere/cadical)
//! - Solver crate:
//!   [https://crates.io/crates/rustsat-cadical](https://crates.io/crates/rustsat-cadical)
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
//!   [https://github.com/arminbiere/kissat](https://github.com/arminbiere/kissat)
//! - Solver crate:
//!   [https://github.com/chrjabs/rustsat-kissat](https://github.com/chrjabs/rustsat-kissat)
//!
//! ### Minisat
//!
//! [Minisat](https://github.com/niklasso/minisat) is an incremental SAT solver
//! by Niklas Een and Niklas Sörensson. It is available through the
//! [`rustsat-minisat`](https://crates.io/crates/rustsat-minisat) crate.
//!
//! #### References
//!
//! - Niklas Een and Niklas Sörensson (2003): _An Extensible SAT-solver_, SAT
//!   2003.
//! - Repository:
//!   [https://github.com/niklasso/minisat](https://github.com/niklasso/minisat)
//! - Solver crate:
//!   [https://crates.io/crates/rustsat-minisat](https://crates.io/crates/rustsat-minisat)
//! - Fork used in solver crate:
//!   [https://github.com/chrjabs/minisat](https://github.com/chrjabs/minisat)
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
//!   webpage](https://www.labri.fr/perso/lsimon/research/glucose/)
//! - Solver crate:
//!   [https://crates.io/crates/rustsat-glucose](https://crates.io/crates/rustsat-glucose)
//! - Fork used in solver crate:
//!   [https://github.com/chrjabs/glucose4](https://github.com/chrjabs/glucose4)
//!
//! ### IPASIR
//!
//! [IPASIR](https://github.com/biotomas/ipasir) is a C API for incremental SAT
//! solvers. RustSAT's IPASIR interface is disabled by default since linking to
//! multiple solvers implementing IPASIR at the same time is not possible. The
//! main reason for including the IPASIR interface in RustSAT is to make it
//! easier to include solvers that don't have Rust interface crates. For this,
//! make sure to not depend on any other SAT solver crate to avoid potential
//! namespace conflicts. Then enable the `ipasir` feature and modify the
//! following lines in the build script `build.rs` accordingly.
//!
//! ```text
//! // Link to custom IPASIR solver
//! // Modify this for linking to your static library
//! // Uncomment and modify this for linking to your static library
//! // The name of the library should be _without_ the prefix 'lib' and the suffix '.a'
//! //println!("cargo:rustc-link-lib=static=<path-to-your-static-lib>");
//! //println!("cargo:rustc-link-search=<name-of-your-static-lib>");
//! // If your IPASIR solver links to the C++ stdlib, uncomment the next four lines
//! //#[cfg(target_os = "macos")]
//! //println!("cargo:rustc-flags=-l dylib=c++");
//! //#[cfg(not(target_os = "macos"))]
//! //println!("cargo:rustc-flags=-l dylib=stdc++");
//! ```

use crate::{
    clause,
    encodings::CollectClauses,
    instances::Cnf,
    types::{Assignment, Clause, Lit, TernaryVal, Var},
};
use core::time::Duration;
use std::fmt;

#[cfg(feature = "ipasir")]
mod ipasir;
#[cfg(feature = "ipasir")]
pub use ipasir::IpasirSolver;
use thiserror::Error;

/// Trait for all SAT solvers in this library.
/// Solvers outside of this library can also implement this trait to be able to
/// use them with this library.
pub trait Solve: Extend<Clause> {
    /// Gets a signature of the solver implementation
    fn signature(&self) -> &'static str;
    /// Reserves memory in the solver until a maximum variables, if the solver
    /// supports it
    fn reserve(&mut self, _max_var: Var) -> SolveMightFail {
        Ok(())
    }
    /// Solves the internal CNF formula without any assumptions.
    fn solve(&mut self) -> Result<SolverResult, SolverError>;
    /// Gets a solution found by the solver.
    ///
    /// # Errors
    ///
    /// - If the solver is not in the satisfied state
    /// - A specific implementation might return other errors
    fn solution(&self, high_var: Var) -> Result<Assignment, SolverError> {
        let mut assignment = Vec::new();
        let len = high_var.idx32() + 1;
        assignment.reserve(len as usize);
        for idx in 0..len {
            let lit = Lit::positive(idx);
            assignment.push(self.lit_val(lit)?);
        }
        Ok(Assignment::from(assignment))
    }
    /// Same as [`Solve::lit_val`], but for variables.
    fn var_val(&self, var: Var) -> Result<TernaryVal, SolverError> {
        self.lit_val(var.pos_lit())
    }
    /// Gets an assignment of a variable in the solver.
    ///
    /// # Errors
    ///
    /// - If the solver is not in the satisfied state
    /// - A specific implementation might return other errors
    fn lit_val(&self, lit: Lit) -> Result<TernaryVal, SolverError>;
    /// Adds a clause to the solver
    /// If the solver is in the satisfied or unsatisfied state before, it is in
    /// the input state afterwards.
    fn add_clause(&mut self, clause: Clause) -> SolveMightFail;
    /// Like [`Solve::add_clause`] but for unit clauses (clauses with one literal).
    fn add_unit(&mut self, lit: Lit) -> SolveMightFail {
        self.add_clause(clause![lit])
    }
    /// Like [`Solve::add_clause`] but for clauses with two literals.
    fn add_binary(&mut self, lit1: Lit, lit2: Lit) -> SolveMightFail {
        self.add_clause(clause![lit1, lit2])
    }
    /// Like [`Solve::add_clause`] but for clauses with three literals.
    fn add_ternary(&mut self, lit1: Lit, lit2: Lit, lit3: Lit) -> SolveMightFail {
        self.add_clause(clause![lit1, lit2, lit3])
    }
    /// Adds all clauses from a [`Cnf`] instance.
    fn add_cnf(&mut self, cnf: Cnf) -> SolveMightFail {
        cnf.into_iter().try_for_each(|cl| self.add_clause(cl))
    }
}

/// Trait for all SAT solvers in this library.
/// Solvers outside of this library can also implement this trait to be able to
/// use them with this library.
pub trait SolveIncremental: Solve {
    /// Solves the internal CNF formula under assumptions.
    fn solve_assumps(&mut self, assumps: &[Lit]) -> Result<SolverResult, SolverError>;
    /// Gets a core found by an unsatisfiable query.
    /// A core is a clause entailed by the formula that contains only inverted
    /// literals of the assumptions.
    fn core(&mut self) -> Result<Vec<Lit>, SolverError>;
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
    type Interrupter: InterruptSolver + Send + 'static;
    /// Gets a thread safe interrupter object that can be used to terminate the solver
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
    fn phase_lit(&mut self, lit: Lit) -> Result<(), SolverError>;
    /// Undoes the effect of a call to [`PhaseLit::phase_lit`]
    fn unphase_var(&mut self, var: Var) -> Result<(), SolverError>;
    /// Undoes the effect of a call to [`PhaseLit::phase_lit`]
    fn unphase_lit(&mut self, lit: Lit) -> Result<(), SolverError> {
        self.unphase_var(lit.var())
    }
}

/// Trait for freezing and melting variables in solvers with pre-/inprocessing.
pub trait FreezeVar {
    /// Freezes a variable so that it is not removed in pre-/inprocessing
    fn freeze_var(&mut self, var: Var) -> Result<(), SolverError>;
    /// Melts a variable after it had been frozen
    fn melt_var(&mut self, var: Var) -> Result<(), SolverError>;
    /// Checks if a variable is frozen
    fn is_frozen(&mut self, var: Var) -> Result<bool, SolverError>;
}

/// Trait for all solvers that can flip a literal in the current assignment
pub trait FlipLit {
    /// Attempts flipping the literal in the given assignment and returns `true` if successful
    fn flip_lit(&mut self, lit: Lit) -> Result<bool, SolverError>;
    /// Checks if the literal can be flipped in the given assignment without flipping it
    fn is_flippable(&mut self, lit: Lit) -> Result<bool, SolverError>;
}

/// Trait for all solvers that can limit the number of conflicts
pub trait LimitConflicts {
    /// Sets or removes a limit on the number of conflicts
    fn limit_conflicts(&mut self, limit: Option<u32>) -> Result<(), SolverError>;
}

/// Trait for all solvers that can limit the number of decisions
pub trait LimitDecisions {
    /// Sets or removes a limit on the number of decisions
    fn limit_decisions(&mut self, limit: Option<u32>) -> Result<(), SolverError>;
}

/// Trait for all solvers that can limit the number of propagations
pub trait LimitPropagations {
    /// Sets or removes a limit on the number of propagations
    fn limit_propagations(&mut self, limit: Option<u32>) -> Result<(), SolverError>;
}

/// Trait for all solvers allowing access to internal search statistics
pub trait GetInternalStats {
    /// Gets the number of propagations
    fn propagations(&self) -> usize;
    /// Gets the number of decisions
    fn decisions(&self) -> usize;
    /// Gets the number of conflicts
    fn conflicts(&self) -> usize;
}

/// Return type of solver calls that don't return but might fail
pub type SolveMightFail = Result<(), SolverError>;

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
    fn stats(&self) -> SolverStats;
    /// Gets the number of satisfiable queries executed.
    fn n_sat_solves(&self) -> usize {
        self.stats().n_sat
    }
    /// Gets the number of unsatisfiable queries executed.
    fn n_unsat_solves(&self) -> usize {
        self.stats().n_unsat
    }
    /// Gets the number of queries that were prematurely terminated.
    fn n_terminated(&self) -> usize {
        self.stats().n_terminated
    }
    /// Gets the total number of queries executed.
    fn n_solves(&self) -> usize {
        self.n_sat_solves() + self.n_unsat_solves() + self.n_terminated()
    }
    /// Gets the number of clauses in the solver.
    fn n_clauses(&self) -> usize {
        self.stats().n_clauses
    }
    /// Gets the variable with the highest index in the solver, if any.
    /// If all variables below have been used, the index of this variable +1 is
    /// the number of variables in the solver.
    fn max_var(&self) -> Option<Var> {
        self.stats().max_var
    }
    /// Get number of variables.
    /// Note: this is only correct if all variables are used in order!
    fn n_vars(&self) -> usize {
        match self.max_var() {
            Some(var) => var.idx() + 1,
            None => 0,
        }
    }
    /// Gets the average length of all clauses in the solver.
    fn avg_clause_len(&self) -> f32 {
        self.stats().avg_clause_len
    }
    /// Gets the total CPU time spent solving.
    fn cpu_solve_time(&self) -> Duration {
        self.stats().cpu_solve_time
    }
}

/// States that the solver can be in.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverState {
    /// Configuration of the solver must be done in this state, before any clauses are added
    Configuring,
    /// Input state, while adding clauses.
    Input,
    /// The query was found satisfiable.
    Sat,
    /// The query was found unsatisfiable.
    Unsat,
    /// Solver is in error state.
    /// For example after trying to add a clause to a non-incremental solver after solving.
    Error(String),
}

impl fmt::Display for SolverState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverState::Configuring => write!(f, "CONFIGURING"),
            SolverState::Input => write!(f, "INPUT"),
            SolverState::Sat => write!(f, "SAT"),
            SolverState::Unsat => write!(f, "UNSAT"),
            SolverState::Error(desc) => write!(f, "Error: {}", desc),
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

/// Type representing solver errors
#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum SolverError {
    /// An API with a description
    #[error("API error: {0}")]
    Api(String),
    /// The solver was expected to be in the second [`SolverState`], but it is in the first.
    #[error("solvers needs to be in state {1} but was in state {0}")]
    State(SolverState, SolverState),
}

impl<S: Solve + SolveStats> CollectClauses for S {
    fn n_clauses(&self) -> usize {
        self.n_clauses()
    }
}
