//! # MaxSAT Algorithms
//!
//! This module contains simple implementations of some MaxSAT algorithms.
//! Note that these implementations do not form competitive MaxSAT solvers and are not optimized
//! for maximum performance.

use crate::{
    encodings::pb,
    instances::{BasicVarManager, ManageVars, Objective},
    solvers::{SolveIncremental, SolveStats, SolverResult},
    types::{Assignment, Clause, Lit},
};

/// Performs solution-improving search on an optimization instance
///
/// The generic `S` is the SAT solver to be used. The generic `PBE` is the pseudo-Boolean encoding
/// to be used for encoding the objective.
///
/// # References
///
/// - Fahiem Bacchus and Matti Järvisalo and Ruben Martins: _Maximum Satisfiability_, in Handbook
/// of Satisfiability 2021.
///
/// # Panics
///
/// - If any interaction with the solver errors
/// - If the objective value overflows [`isize::MAX`]
pub fn solution_improving_search<S, PBE>(
    solver: &mut S,
    objective: &Objective,
) -> Option<(Assignment, isize)>
where
    S: SolveIncremental + SolveStats,
    PBE: FromIterator<(Lit, usize)> + pb::BoundUpperIncremental,
{
    let Some(max_var) = std::cmp::max(solver.max_var(), objective.max_var()) else {
        return Some((Assignment::default(), objective.offset()));
    };
    let mut vm = BasicVarManager::from_next_free(max_var + 1);
    let handle_soft_cls = |(mut cl, w): (Clause, usize)| {
        debug_assert!(!cl.is_empty());
        if cl.len() == 1 {
            return Some((!cl[0], w));
        }
        let blit = vm.new_lit();
        cl.add(blit);
        solver
            .add_clause(cl)
            .expect("error adding clause to solver");
        Some((!blit, w))
    };
    let mut enc: PBE = objective
        .iter_soft_cls()
        .into_iter()
        .filter_map(handle_soft_cls)
        .collect();

    let mut sol = None;

    loop {
        match solver.solve().expect("solver error while solving") {
            SolverResult::Sat => {
                let assign = solver.solution(max_var).expect("failed getting solution");
                let val = objective.evaluate_no_offset(&assign);
                sol = Some((
                    assign,
                    objective.offset() + isize::try_from(val).expect("objective value overflow"),
                ));
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
