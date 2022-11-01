#![cfg(incsolver)]

use rustsat::{
    clause,
    encodings::card::{
        simulators::{DoubleCard, InvertedCard},
        BothBCard, EncodeCard, IncBothBCard, Totalizer,
    },
    instances::{BasicVarManager, ManageVars},
    lit,
    solvers::{new_default_inc_solver, IncrementalSolve, Solve, SolverResult},
    types::{Clause, Lit, Var},
    var,
};

fn test_inc_both_card<'a, CE: IncBothBCard<'a>>(mut enc: CE) {
    // Set up instance
    let mut solver = new_default_inc_solver();
    solver.add_clause(clause![lit![0], lit![1]]).unwrap();
    solver.add_clause(clause![lit![1]]).unwrap();
    solver.add_clause(clause![lit![1], lit![2]]).unwrap();
    solver.add_clause(clause![lit![2], lit![3]]).unwrap();
    solver.add_clause(clause![lit![3], lit![4]]).unwrap();
    solver.add_clause(clause![lit![4]]).unwrap();
    solver.add_clause(clause![lit![5]]).unwrap();
    solver.add_clause(clause![lit![6], lit![7]]).unwrap();
    solver.add_clause(clause![lit![7]]).unwrap();
    solver.add_clause(clause![lit![7], lit![8]]).unwrap();
    solver.add_clause(clause![lit![8], lit![9]]).unwrap();
    solver.add_clause(clause![lit![9], lit![10]]).unwrap();
    solver.add_clause(clause![lit![10]]).unwrap();
    let mut var_manager = BasicVarManager::new();
    var_manager.increase_next_free(var![11]);

    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);

    enc.add(vec![lit![0], lit![1], lit![2], lit![3], lit![4]]);

    solver
        .add_cnf(enc.encode_both(2, 2, &mut var_manager).unwrap())
        .unwrap();
    let assumps = enc.enforce_lb(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    solver
        .add_cnf(enc.encode_both_change(0, 3, &mut var_manager).unwrap())
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    enc.add(vec![lit![5]]);

    solver
        .add_cnf(enc.encode_both_change(0, 3, &mut var_manager).unwrap())
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    solver
        .add_cnf(enc.encode_both_change(0, 4, &mut var_manager).unwrap())
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    enc.add(vec![lit![6], lit![7], lit![8], lit![9], lit![10]]);

    solver
        .add_cnf(enc.encode_both_change(0, 4, &mut var_manager).unwrap())
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    solver
        .add_cnf(enc.encode_both_change(0, 7, &mut var_manager).unwrap())
        .unwrap();
    let assumps = enc.enforce_ub(7).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);
}

fn test_both_card<'a, CE: BothBCard<'a>>(mut enc: CE) {
    // Set up instance
    let mut solver = new_default_inc_solver();
    solver.add_clause(clause![lit![0], lit![1]]).unwrap();
    solver.add_clause(clause![lit![1]]).unwrap();
    solver.add_clause(clause![lit![1], lit![2]]).unwrap();
    solver.add_clause(clause![lit![2], lit![3]]).unwrap();
    solver.add_clause(clause![lit![3], lit![4]]).unwrap();
    solver.add_clause(clause![lit![4]]).unwrap();
    let mut var_manager = BasicVarManager::new();
    var_manager.increase_next_free(var![5]);

    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);

    // Set up totalizer
    enc.add(vec![!lit![0], !lit![1], !lit![2], !lit![3], !lit![4]]);

    solver
        .add_cnf(enc.encode_both(2, 3, &mut var_manager).unwrap())
        .unwrap();
    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let assumps = enc.enforce_lb(3).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let assumps = enc.enforce_lb(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);
}

/// Requires a cardinality encoding with upper and lower bounding functionality
fn test_both_card_min_enc<'a, CE: BothBCard<'a>>(mut enc: CE) {
    // Set up instance
    let mut solver = new_default_inc_solver();
    let mut var_manager = BasicVarManager::new();
    var_manager.increase_next_free(var![4]);

    enc.add(vec![lit![0], lit![1], lit![2], lit![3]]);

    solver
        .add_cnf(enc.encode_both(3, 3, &mut var_manager).unwrap())
        .unwrap();
    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], lit![1], lit![2], !lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], lit![1], !lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2], !lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], !lit![1], !lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2], !lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2], !lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);
}

#[test]
fn tot_positive_lits() {
    let tot = Totalizer::new();
    test_inc_both_card(tot);
}

#[test]
fn tot_negative_lits() {
    let tot = Totalizer::new();
    test_both_card(tot);
}

#[test]
fn tot_min_enc() {
    let tot = Totalizer::new();
    test_both_card_min_enc(tot);
}

#[test]
fn double_invertet_tot() {
    let double_inv_tot: DoubleCard<InvertedCard<Totalizer>, InvertedCard<Totalizer>> =
        DoubleCard::new();
    test_inc_both_card(double_inv_tot)
}
