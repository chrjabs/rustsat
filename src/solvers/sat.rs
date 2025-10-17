//! # Interface to SAT Solvers
//!
//! This module holds traits and types defining the interface to SAT solvers.
//! The API follows the [typestate](https://en.wikipedia.org/wiki/Typestate_analysis) pattern,
//! meaning that state transitions are encoded into Rust's typesystem, which makes calls in invalid
//! stats (e.g., attempting to obtain a solution from a solver in the UNSAT state) impossible.
//!
//! ## Non-Incremental Solving
//!
//! Non-incremental or single-shot solving is the process where, for given formula, the SAT solver
//! determines whether a solution exists or not.
//! Afterwards, the solver can not be used further.
//!
//! Non-incremental solving is modeled via the [`Solve`] trait, which defines a type for the solver
//! in each state.
//! The state diagram with possible transitions looks as follows:
//! ```txt
//! ┌──────┐   ┌───────┐      ┌─────┐    
//! │ Init ├──►│ Input ├─┬───►│ Sat │    
//! └──────┘   └───────┘ │    └─────┘    
//!                      │    ┌───────┐  
//!                      ├───►│ Unsat │  
//!                      │    └───────┘  
//!                      │    ┌─────────┐
//!                      └───►│ Unknown │
//!                           └─────────┘
//! ```
//! Most states have a corresponding trait in this module, that defines which operations are valid
//! in this state.
//! - [`Init`]: The initialization state of the solver where no clauses are added yet, but certain
//!   options can that can not be altered after the first clause has been added, can be set
//! - [`Input`]: The state in which clauses are added
//! - [`Sat`]: A solution to the input formula has been found
//! - `Unsat`: The formula has been determined to not have a solution
//! - `Unknown`: The search has been terminated early
//!
//! ## Incremental Solving
//!
//! In incremental solving, additional clauses can be added to the SAT solver after previous solve
//! calls, and the instance can be resolved.
//! Additionally, so-called _assumptions_ can be set for a solve call, which is a partial
//! assignment that the solver is supposed to extend.
//! If the solver determines that a set of assumptions cannot be extended to a solution, the solver
//! can provide a so-called _core_, a clause over the variables in the assumptions that is implied
//! by the formula.
//!
//! Incremental solving is captured by the [`SolveIncremental`] trait.
//! The state diagram for incremental solving looks as follows:
//!
//! ```txt
//! ┌──────┐   ┌───────┐      ┌─────┐       
//! │ Init ├──►│ Input ├─┬───►│ Sat ├──────┐
//! └──────┘   └───────┘ │    └─────┘      │
//!                ▲     │    ┌───────┐    │
//!                │     ├───►│ Unsat ├────┤
//!                │     │    └───────┘    │
//!                │     │    ┌─────────┐  │
//!                │     └───►│ Unknown ├──┤
//!                │          └─────────┘  │
//!                └───────────────────────┘
//! ```
//!
//! For the input state, the [`SolveAssumptions`] trait captures the state transitions as the
//! [`Input`] trait does (moving ownership of the state).
//! Alternatively, the [`SolveGuarded`] trait provides an API based on guard types (similar to
//! [`std::sync::Mutex`]), which allows for keeping ownership of the input state in place.
//!
//! ## Available Solvers
//!
//! Interfaces to concrete solvers are available through separate crates, where the traits defined
//! in this module (e.g., [`Solve`]) are implemented.
//! For more details on a solver, please refer to the documentation of the respective solver crate.
//!
//! ### CaDiCaL
//!
//! [CaDiCaL](https://github.com/arminbiere/cadical) is a fully incremental SAT solver by Armin
//! Biere implemented in Cpp. It includes incremental inprocessing.
//! It is available through the [`rustsat-cadical`](https://crates.io/crates/rustsat-cadical)
//! crate.
//!
//! #### References
//!
//! - Armin Biere and Tobias Faller and Katalin Fazekas and Mathias Fleury and Nils Froleyks and
//!   Florian Pollitt: _CaDiCaL 2.0_, CAV 2024.
//! - Armin Biere and Katalin Fazekas and Mathias Fleury and Maximillian Heisinger: _CaDiCaL,
//!   Kissat, Paracooba, Plingeling and Treengeling Entering the SAT Competition 2020_, SAT
//!   Competition 2020.
//! - Original Repository:
//!   [`https://github.com/arminbiere/cadical`](https://github.com/arminbiere/cadical)
//! - Solver crate:
//!   [`https://crates.io/crates/rustsat-cadical`](https://crates.io/crates/rustsat-cadical)
//!
//! ### Kissat
//!
//! [Kissat](https://github.com/arminbiere/kissat) is a non-incremental SAT solver by Armin Biere
//! implemented in C.
//! It is available through the [`rustsat-kissat`](https://crates.io/crates/rustsat-kissat) crate.
//!
//! #### References
//!
//! - Armin Biere and Katalin Fazekas and Mathias Fleury and Maximillian Heisinger: _CaDiCaL,
//!   Kissat, Paracooba, Plingeling and Treengeling Entering the SAT Competition 2020_, SAT
//!   Competition 2020.
//! - Repository:
//!   [`https://github.com/arminbiere/kissat`](https://github.com/arminbiere/kissat)
//! - Solver crate:
//!   [`https://github.com/chrjabs/rustsat-kissat`](https://github.com/chrjabs/rustsat-kissat)
//!
//! ### Minisat
//!
//! [Minisat](https://github.com/niklasso/minisat) is an incremental SAT solver by Niklas Eén and
//! Niklas Sörensson.
//! It is available through the [`rustsat-minisat`](https://crates.io/crates/rustsat-minisat)
//! crate.
//!
//! #### References
//!
//! - Niklas Eén and Niklas Sörensson (2003): _An Extensible SAT-solver_, SAT 2003.
//! - Repository:
//!   [`https://github.com/niklasso/minisat`](https://github.com/niklasso/minisat)
//! - Solver crate:
//!   [`https://crates.io/crates/rustsat-minisat`](https://crates.io/crates/rustsat-minisat)
//! - Fork used in solver crate:
//!   [`https://github.com/chrjabs/rustsat/tree/main/minisat/cppsrc`](https://github.com/chrjabs/rustsat/tree/main/minisat/cppsrc)
//!
//! ### Glucose
//!
//! [Glucose](https://www.labri.fr/perso/lsimon/research/glucose/) is a SAT solver based on Minisat
//! and developed by Gilles Audemard and Laurent Simon.
//! It is available through the [`rustsat-glucose`](https://crates.io/crates/rustsat-glucose)
//! crate.
//!
//! #### References
//!
//! - Gilles Audemard and Laurent Simon: _Predicting Learnt Clauses Quality in Modern SAT Solvers_,
//!   IJCAI 2009.
//! - More references at the [Glucose
//!   web-page](https://www.labri.fr/perso/lsimon/research/glucose/)
//! - Solver crate:
//!   [`https://crates.io/crates/rustsat-glucose`](https://crates.io/crates/rustsat-glucose)
//! - Fork used in solver crate:
//!   [`https://github.com/chrjabs/rustsat/tree/main/glucose/cppsrc`](https://github.com/chrjabs/rustsat/tree/main/glucose/cppsrc)
//!
//! ### BatSat
//!
//! [BatSat](https://github.com/c-cube/batsat) is a SAT solver based on Minisat but fully
//! implemented in Rust.
//! Because it is fully implemented in Rust, it is a good choice for restricted compilation
//! scenarios like WebAssembly. BatSat is available through the
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
//! and parsing their output written to `<stdout>`.
//! For more details, see the [`ExternalSolver`] type.
//!
//! ### IPASIR
//!
//! [IPASIR](https://github.com/biotomas/ipasir) is a C API for incremental SAT solvers.
//! IPASIR bindings for RustSAT are provided in the
//! [`rustsat-ipasir`](https://crates.io/crates/rustsat-ipasir) crate.

use crate::{
    encodings::CollectClauses,
    instances::Cnf,
    types::{Assignment, Cl, Clause, Lit, TernaryVal, Var},
    MightMemout,
};

/// The main trait implemented by any SAT solver for non-incremental solving
///
/// The main elements specified by this trait are the types the solver takes in any given state.
/// The possible states and transitions are illustrated by the following diagram.
///
/// ```txt
/// ┌──────┐   ┌───────┐      ┌─────┐    
/// │ Init ├──►│ Input ├─┬───►│ Sat │    
/// └──────┘   └───────┘ │    └─────┘    
///                      │    ┌───────┐  
///                      ├───►│ Unsat │  
///                      │    └───────┘  
///                      │    ┌─────────┐
///                      └───►│ Unknown │
///                           └─────────┘
/// ```
pub trait Solve: Sized {
    /// The initialization state of the solver
    ///
    /// In this state, configuration parameters that cannot be changed after the first clause has
    /// been added can be set.
    type Init: Init;

    /// The input state of the solver
    ///
    /// In this state clauses can be added to the formula in the SAT solver
    type Input: Input<Self> + CollectClauses;

    /// The state after the solver determined the formula to be satisfiable
    ///
    /// In this state the found solution can be queried.
    type Sat: Sat;

    /// The state of the solver after the formula was determined to be unsatisfiable
    type Unsat;

    /// The state of the solver after search was prematurely terminated
    type Unknown;

    /// Obtains the signature of the solver
    #[must_use]
    fn signature() -> &'static str;
}

/// Operations that can be performed in the initialization state of the solver
pub trait Init: From<Self::Config> {
    /// A specification of a preset configuration of the solver
    ///
    /// This can be used with the [`From`] trait to create a solver.
    type Config;

    /// An option that can be set for the solver
    ///
    /// Typically this will have constructors for possible options and values.
    type Option;

    /// Sets an option
    fn set_option(&mut self, option: Self::Option) -> &mut Self;
}

/// The return type of a call to [`Input::solve`] or
/// [`SolveAssumptions::solve_under_assumptions`].
#[derive(Debug)]
pub enum SolveResult<Solver: Solve> {
    /// The formula was determined to be satisfiable
    Sat(Solver::Sat),
    /// The formula was determined to be unsatisfiable
    Unsat(Solver::Unsat),
    /// Search was terminated prematurely
    Unknown(Solver::Unknown),
}

/// Operations that can be performed in the input state of the solver
///
/// # Out of Memory Errors
///
/// This trait's design intends for memouts in the solver to be caught and returned as an error.
/// However, not all solver implementations support this, and some might panic instead.
///
/// When using the trait implementations, such as [`Extend`] and [`FromIterator`], memout errors
/// are converted to panics.
pub trait Input<Solver>: From<Solver::Init>
where
    Solver: Solve,
{
    /// An option that can be set for the solver during the input state
    ///
    /// Typically this will have constructors for possible options and values.
    type Option;

    /// Sets an option
    fn set_option(&mut self, option: Self::Option) -> &mut Self;

    /// Reserves memory in the solver until a maximum variables
    ///
    /// **Note**: not all solvers support this, and the default implementation is a no-op.
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn reserve(&mut self, _max_var: Var) -> MightMemout<&Self> {
        Ok(self)
    }

    /// Adds a clause to the solver by reference
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn add_clause<C>(&mut self, clause: &C) -> MightMemout<&Self>
    where
        C: AsRef<Cl> + ?Sized;

    /// Adds a clause to the solver by value
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn move_clause(&mut self, clause: Clause) -> MightMemout<&Self> {
        self.add_clause(&clause)
    }

    /// Adds a unit clause (a clause with a single literal) to the solver
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn add_unit(&mut self, lit: Lit) -> MightMemout<&Self> {
        self.add_clause(&[lit])
    }

    /// Adds a binary clause (a clause with a two literal) to the solver
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn add_binary(&mut self, lit1: Lit, lit2: Lit) -> MightMemout<&Self> {
        self.add_clause(&[lit1, lit2])
    }

    /// Adds a ternary clause (a clause with a three literal) to the solver
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn add_ternary(&mut self, lit1: Lit, lit2: Lit, lit3: Lit) -> MightMemout<&Self> {
        self.add_clause(&[lit1, lit2, lit3])
    }

    /// Adds a formula in conjunctive normal form (CNF) to the solver by reference
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn add_cnf(&mut self, cnf: &Cnf) -> MightMemout<&Self> {
        for cl in cnf {
            self.add_clause(cl)?;
        }
        Ok(self)
    }

    /// Adds a formula in conjunctive normal form (CNF) to the solver by value
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn move_cnf(&mut self, cnf: Cnf) -> MightMemout<&Self> {
        for cl in cnf {
            self.move_clause(cl)?;
        }
        Ok(self)
    }

    /// Determines whether the internal formula is satisfiable
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn solve(self) -> MightMemout<SolveResult<Solver>>;
}

/// Operations that can be performed in the "satisfiable" state of the solver
pub trait Sat {
    /// Gets the value of a variable in the found solution
    fn variable_value(&self, var: Var) -> TernaryVal;

    /// Gets the value of a literal in the found solution
    fn literal_value(&self, lit: Lit) -> TernaryVal {
        if lit.is_pos() {
            self.variable_value(lit.var())
        } else {
            !self.variable_value(lit.var())
        }
    }

    /// Gets the of the solver up to a maximum variable
    fn solution(&self, max_var: Var) -> Assignment {
        (0..=max_var.idx32())
            .map(|idx| self.variable_value(Var::new(idx)))
            .collect()
    }
}

/// The main trait implemented by any SAT solver for incremental solving
///
/// This adds additional restrictions over the [`Solve`] trait that allows for solving with
/// assumptions, getting cores, and returning to the input state after solving.
/// The resulting state transition diagram is the following:
///
/// ```txt
/// ┌──────┐   ┌───────┐      ┌─────┐       
/// │ Init ├──►│ Input ├─┬───►│ Sat ├──────┐
/// └──────┘   └───────┘ │    └─────┘      │
///                ▲     │    ┌───────┐    │
///                │     ├───►│ Unsat ├────┤
///                │     │    └───────┘    │
///                │     │    ┌─────────┐  │
///                │     └───►│ Unknown ├──┤
///                │          └─────────┘  │
///                └───────────────────────┘
/// ```
///
/// For the input state, the [`SolveAssumptions`] trait captures the state transitions as the
/// [`Input`] trait does (moving ownership of the state).
/// Alternatively, the [`SolveGuarded`] trait provides an API based on guard types (similar to
/// [`std::sync::Mutex`]), which allows for keeping ownership of the input state in place.
pub trait SolveIncremental: Solve + Sized
where
    Self::Input: SolveAssumptions<Self>
        + SolveGuarded<Self>
        + From<Self::Sat>
        + From<Self::Unsat>
        + From<Self::Unknown>,
    Self::Unsat: UnsatIncremental,
{
    /// The SAT state guard for [`SolveGuarded`]
    type SatGuard<'a>: Sat;

    /// The UNSAT state guard for [`SolveGuarded`]
    type UnsatGuard<'a>: UnsatIncremental;

    /// The unknown state guard for [`SolveGuarded`]
    type UnknownGuard<'a>;
}

/// Functionality for solving under assumption, implemented by the input state of incremental
/// solvers
///
/// This trait uses the type state design.
/// For a guard-based API, see [`SolveGuarded`].
pub trait SolveAssumptions<Solver>: Input<Solver>
where
    Solver: Solve,
{
    /// Determines whether the internal formula is satisfiable under given assumptions
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn solve_under_assumptions(self, assumptions: &[Lit]) -> MightMemout<SolveResult<Solver>>;
}

/// Guard-based solving API for incremental solvers
///
/// This is an alternative API to [`SolveAssumptions`] that does not require transferring
/// ownership.
pub trait SolveGuarded<Solver>: Input<Solver>
where
    Solver: SolveIncremental,
    Solver::Input: SolveAssumptions<Solver>
        + SolveGuarded<Solver>
        + From<Solver::Sat>
        + From<Solver::Unsat>
        + From<Solver::Unknown>,
    Solver::Unsat: UnsatIncremental,
{
    /// Determines whether the internal formula is satisfiable
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn solve(&mut self) -> MightMemout<SolveGuard<'_, Solver>>;

    /// Determines whether the internal formula is satisfiable under given assumptions
    ///
    /// # Errors
    ///
    /// If not enough memory is available.
    fn solve_under_assumptions(
        &mut self,
        assumptions: &[Lit],
    ) -> MightMemout<SolveGuard<'_, Solver>>;
}

/// The return type of a call to [`SolveGuarded::solve`] or
/// [`SolveGuarded::solve_under_assumptions`].
#[derive(Debug)]
pub enum SolveGuard<'a, Solver>
where
    Solver: SolveIncremental,
    Solver::Input: SolveAssumptions<Solver>
        + SolveGuarded<Solver>
        + From<Solver::Sat>
        + From<Solver::Unsat>
        + From<Solver::Unknown>,
    Solver::Unsat: UnsatIncremental,
{
    /// The formula was determined to be satisfiable
    Sat(Solver::SatGuard<'a>),
    /// The formula was determined to be unsatisfiable
    Unsat(Solver::UnsatGuard<'a>),
    /// Search was terminated prematurely
    Unknown(Solver::UnknownGuard<'a>),
}

/// Functionality for getting a core in the unsat state of incremental solvers
pub trait UnsatIncremental {
    /// Gets a core found by an unsatisfiable query
    ///
    /// A core is a clause entailed by the formula that contains only negated literals from the
    /// assumptions.
    fn core(&mut self) -> &[Lit];

    /// Checks whether an assumption is failed, meaning that its negation is included in the found
    /// core
    fn failed(&mut self, assumption: Lit) -> bool;
}
