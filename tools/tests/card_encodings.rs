use rustsat::{
    clause,
    encodings::card::{
        simulators::{Double, Inverted},
        BoundBoth, BoundBothIncremental, Totalizer,
    },
    instances::{BasicVarManager, ManageVars},
    lit,
    solvers::{Solve, SolveIncremental, SolverResult},
    types::{Clause, Lit, Var},
    var,
};
use rustsat_cadical::CaDiCaL;

fn test_inc_both_card<CE: BoundBothIncremental>(mut enc: CE) {
    // Set up instance
    let mut solver = CaDiCaL::default();
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
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![11]);

    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);

    enc.extend(vec![lit![0], lit![1], lit![2], lit![3], lit![4]]);

    solver
        .add_cnf(enc.encode_both(2..3, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_lb(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    solver
        .add_cnf(enc.encode_both_change(0..4, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    enc.extend(vec![lit![5]]);

    solver
        .add_cnf(enc.encode_both_change(0..4, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    solver
        .add_cnf(enc.encode_both_change(0..5, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    enc.extend(vec![lit![6], lit![7], lit![8], lit![9], lit![10]]);

    solver
        .add_cnf(enc.encode_both_change(0..5, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    solver
        .add_cnf(enc.encode_both_change(0..8, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(7).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn test_both_card<CE: BoundBoth>(mut enc: CE) {
    // Set up instance
    let mut solver = CaDiCaL::default();
    solver.add_clause(clause![lit![0], lit![1]]).unwrap();
    solver.add_clause(clause![lit![1]]).unwrap();
    solver.add_clause(clause![lit![1], lit![2]]).unwrap();
    solver.add_clause(clause![lit![2], lit![3]]).unwrap();
    solver.add_clause(clause![lit![3], lit![4]]).unwrap();
    solver.add_clause(clause![lit![4]]).unwrap();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![5]);

    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);

    // Set up totalizer
    enc.extend(vec![!lit![0], !lit![1], !lit![2], !lit![3], !lit![4]]);

    solver
        .add_cnf(enc.encode_both(2..4, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let assumps = enc.enforce_lb(3).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let assumps = enc.enforce_lb(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

/// Requires a cardinality encoding with upper and lower bounding functionality
fn test_both_card_min_enc<CE: BoundBoth>(mut enc: CE) {
    // Set up instance
    let mut solver = CaDiCaL::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    enc.extend(vec![lit![0], lit![1], lit![2], lit![3]]);

    solver
        .add_cnf(enc.encode_both(3..4, &mut var_manager))
        .unwrap();
    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], lit![1], lit![2], !lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], lit![1], !lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2], !lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], !lit![1], !lit![2], lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2], !lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2], !lit![3]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);
}

#[test]
fn tot_positive_lits() {
    let tot = Totalizer::default();
    test_inc_both_card(tot);
}

#[test]
fn tot_negative_lits() {
    let tot = Totalizer::default();
    test_both_card(tot);
}

#[test]
fn tot_min_enc() {
    let tot = Totalizer::default();
    test_both_card_min_enc(tot);
}

#[test]
fn invertet_tot() {
    let inv_tot: Inverted<Totalizer> = Inverted::default();
    test_inc_both_card(inv_tot)
}

#[test]
fn double_invertet_tot() {
    let double_inv_tot: Double<Inverted<Totalizer>, Inverted<Totalizer>> = Double::default();
    test_inc_both_card(double_inv_tot)
}
