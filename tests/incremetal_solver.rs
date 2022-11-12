#![allow(dead_code, unused)]

use rustsat::{
    instances::{BasicVarManager, SatInstance},
    lit, solvers,
    solvers::{IncrementalSolve, SolverResult},
    types::Lit,
};

fn assumption_sequence<S: IncrementalSolve>(mut solver: S) {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/small.cnf").unwrap();
    solver.add_cnf(inst.as_cnf().0);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);
    let res = solver.solve_assumps(vec![!lit![0], !lit![1]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![lit![0], lit![1], lit![2], lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![lit![0], lit![1], lit![2], !lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![lit![0], lit![1], !lit![2], lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![lit![0], lit![1], !lit![2], !lit![3]]).unwrap();
    assert_eq!(res, SolverResult::SAT);
    let res = solver.solve_assumps(vec![lit![0], !lit![1], lit![2], lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![lit![0], !lit![1], lit![2], !lit![3]]).unwrap();
    assert_eq!(res, SolverResult::SAT);
    let res = solver.solve_assumps(vec![lit![0], !lit![1], !lit![2], lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![lit![0], !lit![1], !lit![2], !lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![!lit![0], lit![1], lit![2], lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![!lit![0], lit![1], lit![2], !lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![!lit![0], lit![1], !lit![2], lit![3]]).unwrap();
    assert_eq!(res, SolverResult::SAT);
    let res = solver.solve_assumps(vec![!lit![0], lit![1], !lit![2], !lit![3]]).unwrap();
    assert_eq!(res, SolverResult::SAT);
    let res = solver.solve_assumps(vec![!lit![0], !lit![1], lit![2], lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![!lit![0], !lit![1], lit![2], !lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![!lit![0], !lit![1], !lit![2], lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
    let res = solver.solve_assumps(vec![!lit![0], !lit![1], !lit![2], !lit![3]]).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
}

#[test]
#[cfg(feature = "ipasir")]
fn ipasir_small_sat() {
    let solver = solvers::IpasirSolver::default();
    assumption_sequence(solver);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_assumption_sequence() {
    let solver = solvers::CaDiCaL::default();
    assumption_sequence(solver);
}
