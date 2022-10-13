//! # Interfaces to SAT Solvers
//!
//! This module holds types and functions regarding SAT solvers.
//! The main element is the [`Solve`] trait that every SAT solver in this library implements.

#[cfg(feature = "ipasir")]
pub mod ipasir;

use crate::{
    clause,
    instances::CNF,
    types::{Clause, Error, Lit, Solution, TernaryVal, Var},
};
use std::fmt;

use self::ipasir::IpasirSolver;

/// Trait for all SAT solvers in this library.
/// Solvers outside of this library can also implement this trait to be able to
/// use them with this library.
pub trait Solve {
    /// Solves the internal CNF formula without any assumptions.
    fn solve(&mut self) -> Result<SolverResult, Error>;
    /// Gets a solution found by the solver.
    ///
    /// # Errors
    ///
    /// - If the solver is not in the satisfied state
    /// - A specific implementation might return other errors
    fn get_solution(&self, high_var: &Var) -> Result<Solution, Error> {
        let mut assignment = Vec::new();
        let len = high_var.index() + 1;
        assignment.reserve(len);
        for idx in 0..len {
            let lit = Lit::positive(idx);
            assignment.push(self.lit_val(&lit)?);
        }
        Ok(Solution::from_vec(assignment))
    }
    /// Same as [`Solve::lit_val`], but for variables.
    fn var_val(&self, var: &Var) -> Result<TernaryVal, Error> {
        self.lit_val(&var.pos_lit())
    }
    /// Gets an assignment of a variable in the solver.
    ///
    /// # Errors
    ///
    /// - If the solver is not in the satisfied state
    /// - A specific implementation might return other errors
    fn lit_val(&self, lit: &Lit) -> Result<TernaryVal, Error>;
    /// Adds a clause to the solver
    /// If the solver is in the satisfied or unsatisfied state before, it is in
    /// the input state afterwards.
    fn add_clause(&mut self, clause: Clause);
    /// Like [`Solve::add_clause`] but for unit clauses (clauses with one literal).
    fn add_unit(&mut self, lit: Lit) {
        self.add_clause(clause![lit])
    }
    /// Like [`Solve::add_clause`] but for clauses with two literals.
    fn add_pair(&mut self, lit1: Lit, lit2: Lit) {
        self.add_clause(clause![lit1, lit2])
    }
    /// Like [`Solve::add_clause`] but for clauses with three literals.
    fn add_ternary(&mut self, lit1: Lit, lit2: Lit, lit3: Lit) {
        self.add_clause(clause![lit1, lit2, lit3])
    }
    /// Adds all clauses from a [`CNF`] instance.
    fn add_cnf(&mut self, cnf: CNF) {
        cnf.into_iter().for_each(|cl| self.add_clause(cl));
    }
}

/// Trait for all SAT solvers in this library.
/// Solvers outside of this library can also implement this trait to be able to
/// use them with this library.
pub trait IncrementalSolve: Solve {
    /// Solves the internal CNF formula under assumptions.
    /// Even though assumptions should be unique and theoretically the order shouldn't matter,
    /// in practice it does for some solvers, therefore the assumptions are a vector rather than a set.
    fn solve_assumps(&mut self, assumps: Vec<Lit>) -> Result<SolverResult, Error>;
    /// Gets a core found by an unsatisfiable query.
    /// A core is a clause entailed by the formula that contains only inverted
    /// literals of the assumptions.
    fn get_core(&mut self) -> Result<Vec<Lit>, Error>;
}

/// Trait for solvers that track certain statistics.
pub trait SolveStats {
    /// Gets the number of satisfiable queries executed.
    fn get_n_sat_solves(&self) -> u32;
    /// Gets the number of unsatisfiable queries executed.
    fn get_n_unsat_solves(&self) -> u32;
    /// Gets the number of queries that were prematurely terminated.
    fn get_n_terminated(&self) -> u32;
    /// Gets the total number of queries executed.
    fn get_n_solves(&self) -> u32 {
        self.get_n_sat_solves() + self.get_n_unsat_solves() + self.get_n_terminated()
    }
    /// Gets the number of clauses in the solver.
    fn get_n_clauses(&self) -> u32;
    /// Gets the variable with the highest index in the solver, if any.
    /// If all variables below have been used, the index of this variable +1 is
    /// the number of variables in the solver.
    fn get_max_var(&self) -> Option<Var>;
    /// Get number of variables.
    /// Note: this is only correct if all variables are used in order!
    fn get_n_vars(&self) -> usize {
        match self.get_max_var() {
            Some(var) => var.index() + 1,
            None => 0,
        }
    }
    /// Gets the average length of all clauses in the solver.
    fn get_avg_clause_len(&self) -> f32;
    /// Gets the total CPU time spent solving.
    fn get_cpu_solve_time(&self) -> f32;
}

enum InternalSolverState {
    Input,
    SAT,
    UNSAT(Vec<Lit>),
    #[allow(dead_code)] // Variant will be used in the future
    Error(String),
}

impl InternalSolverState {
    fn to_external(&self) -> SolverState {
        match self {
            InternalSolverState::Input => SolverState::Input,
            InternalSolverState::SAT => SolverState::SAT,
            InternalSolverState::UNSAT(_) => SolverState::UNSAT,
            InternalSolverState::Error(desc) => SolverState::Error(desc.clone()),
        }
    }
}

/// States that the solver can be in.
#[derive(Debug, PartialEq, Eq)]
pub enum SolverState {
    /// Input state, while adding clauses.
    Input,
    /// The query was found satisfiable.
    SAT,
    /// The query was found unsatisfiable.
    UNSAT,
    /// Solver is in error state.
    /// For example after trying to add a clause to a non-incremental solver after solving.
    Error(String),
}

impl fmt::Display for SolverState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverState::Input => write!(f, "INPUT"),
            SolverState::SAT => write!(f, "SAT"),
            SolverState::UNSAT => write!(f, "UNSAT"),
            SolverState::Error(desc) => write!(f, "Error: {}", desc),
        }
    }
}

/// Return value for solving queries.
#[derive(Debug, PartialEq, Eq)]
pub enum SolverResult {
    /// The query was found satisfiable.
    SAT,
    /// The query was found unsatisfiable.
    UNSAT,
    /// The query was prematurely interrupted.
    Interrupted,
}

/// Return type for solver terminator callbacks
#[derive(Debug, PartialEq, Eq)]
pub enum ControlSignal {
    /// Variant for the solver to continue
    Continue,
    /// Variant for the solver to terminate
    Terminate,
}

impl fmt::Display for SolverResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolverResult::SAT => write!(f, "SAT"),
            SolverResult::UNSAT => write!(f, "UNSAT"),
            SolverResult::Interrupted => write!(f, "Interrupted"),
        }
    }
}

/// Constructs a default non-incremental solver. Since the return value cannot
/// be upcast, it might be necessary to directly instantiate a solver. For now
/// the default is an IPASIR solver.
pub fn new_default_solver() -> Box<dyn Solve> {
    Box::new(IpasirSolver::new())
}

/// Constructs a default incremental solver. Since the return value cannot be
/// upcast, it might be necessary to directly instantiate a solver. For now the
/// default is an IPASIR solver.
pub fn new_default_inc_solver() -> Box<dyn IncrementalSolve> {
    Box::new(IpasirSolver::new())
}
