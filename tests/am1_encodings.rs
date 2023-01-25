#![cfg(incsolver)]

use rustsat::{
    encodings::am1::{Encode, Pairwise},
    instances::{BasicVarManager, ManageVars},
    lit,
    solvers::{self, IncrementalSolve, Solve, SolverResult},
    types::{Lit, Var},
    var,
};

fn test_am1<AM1: Encode>(mut enc: AM1) {
    let mut solver = solvers::new_default_inc_solver();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![3]);

    enc.extend(vec![lit![0], lit![1], lit![2]]);
    solver
        .add_cnf(enc.encode(&mut var_manager).unwrap())
        .unwrap();

    let res = solver
        .solve_assumps(vec![lit![0], lit![1], lit![2]])
        .unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let res = solver
        .solve_assumps(vec![lit![0], lit![1], !lit![2]])
        .unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let res = solver
        .solve_assumps(vec![lit![0], !lit![1], lit![2]])
        .unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let res = solver
        .solve_assumps(vec![lit![0], !lit![1], !lit![2]])
        .unwrap();
    assert_eq!(res, SolverResult::SAT);

    let res = solver
        .solve_assumps(vec![!lit![0], lit![1], lit![2]])
        .unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let res = solver
        .solve_assumps(vec![!lit![0], lit![1], !lit![2]])
        .unwrap();
    assert_eq!(res, SolverResult::SAT);

    let res = solver
        .solve_assumps(vec![!lit![0], !lit![1], lit![2]])
        .unwrap();
    assert_eq!(res, SolverResult::SAT);

    let res = solver
        .solve_assumps(vec![!lit![0], !lit![1], !lit![2]])
        .unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
fn pairwise() {
    let pairwise = Pairwise::default();
    test_am1(pairwise);
}
