#![cfg(incsolver)]

use rustsat::{
    clause,
    encodings::{
        card::Totalizer,
        pb::{
            simulators::Card, BoundBoth, DoubleGeneralizedTotalizer, GeneralizedTotalizer, BoundBothIncremental,
            BoundUpperIncremental, InvertedGeneralizedTotalizer, BoundLower, BoundUpper,
        },
    },
    instances::{BasicVarManager, ManageVars},
    lit,
    solvers::{new_default_inc_solver, SolveIncremental, Solve, SolverResult},
    types::{Clause, Lit, RsHashMap, Var},
    var,
};

fn test_inc_pb_ub<PBE: BoundUpperIncremental>(mut enc: PBE) {
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
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![11]);

    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    lits.insert(lit![3], 3);
    lits.insert(lit![4], 2);
    enc.extend(lits);

    solver
        .add_cnf(enc.encode_ub(0..3, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    solver
        .add_cnf(enc.encode_ub_change(0..5, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    solver
        .add_cnf(enc.encode_ub_change(0..6, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut lits = RsHashMap::default();
    lits.insert(lit![5], 4);
    enc.extend(lits);

    solver
        .add_cnf(enc.encode_ub_change(0..6, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    solver
        .add_cnf(enc.encode_ub_change(0..10, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut lits = RsHashMap::default();
    lits.insert(lit![6], 1);
    lits.insert(lit![7], 2);
    lits.insert(lit![8], 1);
    lits.insert(lit![9], 3);
    lits.insert(lit![10], 2);
    enc.extend(lits);

    solver
        .add_cnf(enc.encode_ub_change(0..10, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    solver
        .add_cnf(enc.encode_ub_change(0..15, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_ub(14).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn test_pb_eq<PBE: BoundBothIncremental>(mut enc: PBE) {
    // Set up instance
    let mut solver = new_default_inc_solver();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![3]);

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 4);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 2);
    enc.extend(lits);

    solver
        .add_cnf(enc.encode_both(4..5, &mut var_manager))
        .unwrap();

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![!lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);
}

fn test_pb_lb<PBE: BoundLower>(mut enc: PBE) {
    // Set up instance
    let mut solver = new_default_inc_solver();
    solver
        .add_clause(clause![!lit![0], !lit![1], !lit![2]])
        .unwrap();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![3]);

    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 3);
    lits.insert(lit![1], 6);
    lits.insert(lit![2], 3);
    enc.extend(lits);

    solver
        .add_cnf(enc.encode_lb(0..11, &mut var_manager))
        .unwrap();
    let assumps = enc.enforce_lb(10).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let assumps = enc.enforce_lb(9).unwrap();
    println!("{:?}", assumps);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn test_pb_ub_min_enc<PBE: BoundUpper>(mut enc: PBE) {
    // Set up instance
    let mut solver = new_default_inc_solver();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    enc.extend(lits);

    solver
        .add_cnf(enc.encode_ub(2..3, &mut var_manager))
        .unwrap();
    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

#[test]
fn gte_ub() {
    let gte = GeneralizedTotalizer::default();
    test_inc_pb_ub(gte);
}

#[test]
fn gte_lb() {
    let gte = InvertedGeneralizedTotalizer::default();
    test_pb_lb(gte);
}

#[test]
fn gte_min_enc() {
    let gte = GeneralizedTotalizer::default();
    test_pb_ub_min_enc(gte);
}

#[test]
fn gte_eq() {
    let gte = DoubleGeneralizedTotalizer::default();
    test_pb_eq(gte);
}

#[test]
fn tot_pb_sim_eq() {
    let sim: Card<Totalizer> = Card::default();
    test_pb_eq(sim);
}
