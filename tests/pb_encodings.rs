use rustsat::{
    clause,
    encodings::{
        pb::{EncodePB, GeneralizedTotalizer, IncEncodePB},
        BoundType,
    },
    instances::{BasicVarManager, ManageVars},
    lit,
    solvers::{ipasir::IpasirSolver, IncrementalSolve, Solve, SolverResult},
    types::{Clause, Lit, Var},
    var,
};
use std::collections::HashMap;

/// Requires an incremental PB encoding with upper bounding functionality
fn test_pb_ub<PBE: IncEncodePB>(mut enc: PBE) {
    // Set up instance
    let mut solver = IpasirSolver::new();
    solver.add_clause(clause![lit![0], lit![1]]);
    solver.add_clause(clause![lit![1]]);
    solver.add_clause(clause![lit![1], lit![2]]);
    solver.add_clause(clause![lit![2], lit![3]]);
    solver.add_clause(clause![lit![3], lit![4]]);
    solver.add_clause(clause![lit![4]]);
    solver.add_clause(clause![lit![5]]);
    solver.add_clause(clause![lit![6], lit![7]]);
    solver.add_clause(clause![lit![7]]);
    solver.add_clause(clause![lit![7], lit![8]]);
    solver.add_clause(clause![lit![8], lit![9]]);
    solver.add_clause(clause![lit![9], lit![10]]);
    solver.add_clause(clause![lit![10]]);
    let mut var_manager = BasicVarManager::new();
    var_manager.increase_next_free(var![11]);

    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut lits = HashMap::new();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    lits.insert(lit![3], 3);
    lits.insert(lit![4], 2);
    enc.add(lits);

    enc.encode(0, 2, &mut var_manager)
        .unwrap()
        .add_to_solver(&mut solver);
    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    enc.encode_change(0, 4, &mut var_manager)
        .unwrap()
        .add_to_solver(&mut solver);
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    enc.encode_change(0, 5, &mut var_manager)
        .unwrap()
        .add_to_solver(&mut solver);
    let assumps = enc.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut lits = HashMap::new();
    lits.insert(lit![5], 4);
    enc.add(lits);

    enc.encode_change(0, 5, &mut var_manager)
        .unwrap()
        .add_to_solver(&mut solver);
    let assumps = enc.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    enc.encode_change(0, 9, &mut var_manager)
        .unwrap()
        .add_to_solver(&mut solver);
    let assumps = enc.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut lits = HashMap::new();
    lits.insert(lit![6], 1);
    lits.insert(lit![7], 2);
    lits.insert(lit![8], 1);
    lits.insert(lit![9], 3);
    lits.insert(lit![10], 2);
    enc.add(lits);

    enc.encode_change(0, 9, &mut var_manager)
        .unwrap()
        .add_to_solver(&mut solver);
    let assumps = enc.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    enc.encode_change(0, 14, &mut var_manager)
        .unwrap()
        .add_to_solver(&mut solver);
    let assumps = enc.enforce_ub(14).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);
}

/// Requires a PB encoding with lower bounding functionality
fn test_pb_lb<PBE: EncodePB>(mut enc: PBE) {
    // Set up instance
    let mut solver = IpasirSolver::new();
    solver.add_clause(clause![!lit![0], !lit![1], !lit![2]]);
    let mut var_manager = BasicVarManager::new();
    var_manager.increase_next_free(var![3]);

    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut lits = HashMap::new();
    lits.insert(lit![0], 3);
    lits.insert(lit![1], 6);
    lits.insert(lit![2], 3);
    enc.add(lits);

    enc.encode(0, 10, &mut var_manager)
        .unwrap()
        .add_to_solver(&mut solver);
    let assumps = enc.enforce_lb(10).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let assumps = enc.enforce_lb(9).unwrap();
    println!("{:?}", assumps);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);
}

/// Requires a PB encoding with upper bounding functionality
fn test_pb_min_enc<PBE: EncodePB>(mut enc: PBE) {
    // Set up instance
    let mut solver = IpasirSolver::new();
    let mut var_manager = BasicVarManager::new();
    var_manager.increase_next_free(var![4]);

    let mut lits = HashMap::new();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    enc.add(lits);

    enc.encode(2, 2, &mut var_manager)
        .unwrap()
        .add_to_solver(&mut solver);
    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
fn gte_ub() {
    let gte = GeneralizedTotalizer::new(BoundType::UB).unwrap();
    test_pb_ub(gte);
}

#[test]
fn gte_lb() {
    let gte = GeneralizedTotalizer::new(BoundType::LB).unwrap();
    test_pb_lb(gte);
}

#[test]
fn gte_min_enc() {
    let gte = GeneralizedTotalizer::new(BoundType::UB).unwrap();
    test_pb_min_enc(gte);
}
