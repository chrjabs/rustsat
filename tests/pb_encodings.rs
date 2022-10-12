use rustsat::{
    clause,
    encodings::{
        card::{EncodeCard, Totalizer},
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

#[test]
fn gte_ub() {
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

    // Set up GTE
    let mut gte = GeneralizedTotalizer::new(BoundType::UB).unwrap();
    let mut lits = HashMap::new();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    lits.insert(lit![3], 3);
    lits.insert(lit![4], 2);
    gte.add(lits);

    gte.encode(0, 2, &mut var_manager)
        .add_to_solver(&mut solver);
    let assumps = gte.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    gte.encode_change(0, 4, &mut var_manager)
        .add_to_solver(&mut solver);
    let assumps = gte.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    gte.encode_change(0, 5, &mut var_manager)
        .add_to_solver(&mut solver);
    let assumps = gte.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut lits = HashMap::new();
    lits.insert(lit![5], 4);
    gte.add(lits);

    gte.encode_change(0, 5, &mut var_manager)
        .add_to_solver(&mut solver);
    let assumps = gte.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    gte.encode_change(0, 9, &mut var_manager)
        .add_to_solver(&mut solver);
    let assumps = gte.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut lits = HashMap::new();
    lits.insert(lit![6], 1);
    lits.insert(lit![7], 2);
    lits.insert(lit![8], 1);
    lits.insert(lit![9], 3);
    lits.insert(lit![10], 2);
    gte.add(lits);

    gte.encode_change(0, 9, &mut var_manager)
        .add_to_solver(&mut solver);
    let assumps = gte.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    gte.encode_change(0, 14, &mut var_manager)
        .add_to_solver(&mut solver);
    let assumps = gte.enforce_ub(14).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
fn gte_lb() {
    // Set up instance
    let mut solver = IpasirSolver::new();
    solver.add_clause(clause![!lit![0], !lit![1], !lit![2]]);
    let mut var_manager = BasicVarManager::new();
    var_manager.increase_next_free(var![3]);

    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);

    // Set up GTE
    let mut gte = GeneralizedTotalizer::new(BoundType::LB).unwrap();
    let mut lits = HashMap::new();
    lits.insert(lit![0], 3);
    lits.insert(lit![1], 6);
    lits.insert(lit![2], 3);
    gte.add(lits);

    let cnf = gte.encode(0, 10, &mut var_manager);
    println!("{:?}", cnf);
    cnf.add_to_solver(&mut solver);
    let assumps = gte.enforce_lb(10).unwrap();
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let assumps = gte.enforce_lb(9).unwrap();
    println!("{:?}", assumps);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
fn gte_min_enc() {
    // Set up instance
    let mut solver = IpasirSolver::new();
    let mut var_manager = BasicVarManager::new();
    var_manager.increase_next_free(var![4]);

    // Set up totalizer
    let mut gte = GeneralizedTotalizer::new(BoundType::UB).unwrap();
    let mut lits = HashMap::new();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    gte.add(lits);

    gte.encode_change(2, 2, &mut var_manager)
        .add_to_solver(&mut solver);
    let mut assumps = gte.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = gte.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = gte.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = gte.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = gte.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::UNSAT);

    let mut assumps = gte.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = gte.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);

    let mut assumps = gte.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(assumps).unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
fn gte_equals_tot() {
    let mut var_manager_gte = BasicVarManager::new();
    var_manager_gte.increase_next_free(var![7]);
    let mut var_manager_tot = var_manager_gte.clone();
    // Set up GTE
    let mut gte = GeneralizedTotalizer::new(BoundType::UB).unwrap();
    let mut lits = HashMap::new();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 1);
    lits.insert(lit![2], 1);
    lits.insert(lit![3], 1);
    lits.insert(lit![4], 1);
    lits.insert(lit![5], 1);
    lits.insert(lit![6], 1);
    gte.add(lits);
    let gte_cnf = gte.encode(3, 7, &mut var_manager_gte);
    // Set up Tot
    let mut tot = Totalizer::new(BoundType::UB).unwrap();
    tot.add(vec![
        lit![0],
        lit![1],
        lit![2],
        lit![3],
        lit![4],
        lit![5],
        lit![6],
    ]);
    let tot_cnf = tot.encode(3, 7, &mut var_manager_tot);
    println!("{:?}", gte_cnf);
    println!("{:?}", tot_cnf);
    assert_eq!(var_manager_gte.next_free(), var_manager_tot.next_free());
    assert_eq!(gte_cnf.n_clauses(), tot_cnf.n_clauses());
}
