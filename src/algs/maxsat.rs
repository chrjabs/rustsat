//! # MaxSAT Algorithms
//!
//! This module contains simple implementations of some MaxSAT algorithms.
//! Note that these implementations do not form competitive MaxSAT solvers and are not optimized
//! for maximum performance.

use std::marker::PhantomData;

use crate::{
    encodings::pb,
    instances::BasicVarManager,
    solvers::{SolveIncremental, SolveStats, SolverResult},
    types::{Assignment, Lit, TernaryVal},
};

/// Trait for SAT-based MaxSAT solving algorithms
pub trait Solve {
    /// The SAT solver used in solving
    type Solver: SolveIncremental + SolveStats;

    /// Solves the MaxSAT instance
    ///
    /// The constraints need to all be in the [`Self::Solver`] instance already.
    fn solve(solver: &mut Self::Solver, objective: &[(Lit, usize)]) -> Option<(Assignment, usize)>;
}

fn objective_value(obj: &[(Lit, usize)], sol: &Assignment) -> usize {
    obj.iter().fold(0, |sum, (l, w)| {
        if sol.lit_value(*l) == TernaryVal::True {
            sum + w
        } else {
            sum
        }
    })
}

/// Abstract type for solution-improving MaxSAT algorithm
///
/// The generic `Solver` is the SAT solver to be used. The generic `PbEnc` is the pseudo-Boolean
/// encoding to be used for encoding the objective.
///
/// # References
///
/// - Fahiem Bacchus and Matti Järvisalo and Ruben Martins: _Maximum Satisfiability_, in Handbook
///     of Satisfiability 2021.
///
/// # Panics
///
/// - If any interaction with the solver errors
/// - If the objective value overflows [`isize::MAX`]
pub struct SolutionImprovingSearch<Solver, PbEnc> {
    slv: PhantomData<Solver>,
    enc: PhantomData<PbEnc>,
}

impl<Solver, PbEnc> Solve for SolutionImprovingSearch<Solver, PbEnc>
where
    Solver: SolveIncremental + SolveStats,
    PbEnc: FromIterator<(Lit, usize)> + pb::BoundUpperIncremental,
{
    type Solver = Solver;

    fn solve(solver: &mut Self::Solver, objective: &[(Lit, usize)]) -> Option<(Assignment, usize)> {
        let Some(max_var) = solver.max_var() else {
            return Some((Assignment::default(), 0));
        };
        let mut vm = BasicVarManager::from_next_free(max_var + 1);
        let mut enc: PbEnc = objective.iter().copied().collect();

        let mut sol = None;

        loop {
            match solver.solve().expect("solver error while solving") {
                SolverResult::Sat => {
                    let assign = solver.solution(max_var).expect("failed getting solution");
                    let val = objective_value(objective, &assign);
                    sol = Some((assign, val));
                    if val == 0 {
                        return sol;
                    }
                    enc.encode_ub(val - 1..val, solver, &mut vm)
                        .expect("error adding clauses to solver");
                    for unit in enc.enforce_ub(val - 1).expect("invalid encoding usage") {
                        solver
                            .add_unit(unit)
                            .expect("error adding clause to solver");
                    }
                }
                SolverResult::Unsat => return sol,
                SolverResult::Interrupted => unreachable!(),
            }
        }
    }
}
