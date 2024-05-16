use rustsat::{
    clause,
    encodings::card::{
        simulators::{Double, Inverted},
        BoundBoth, BoundBothIncremental, BoundUpperIncremental, DbTotalizer, Totalizer,
    },
    instances::{BasicVarManager, ManageVars},
    lit,
    solvers::{
        Solve, SolveIncremental,
        SolverResult::{self, Sat, Unsat},
    },
    types::Lit,
    var,
};

fn test_inc_both_card<CE: BoundBothIncremental + Extend<Lit> + Default>() {
    // Set up instance
    let mut solver = rustsat_minisat::core::Minisat::default();
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

    let mut enc = CE::default();
    enc.extend(vec![lit![0], lit![1], lit![2], lit![3], lit![4]]);

    enc.encode_both(2..3, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_lb(2).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_both_change(0..4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    enc.extend(vec![lit![5]]);

    enc.encode_both_change(0..4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_both_change(0..5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    enc.extend(vec![lit![6], lit![7], lit![8], lit![9], lit![10]]);

    enc.encode_both_change(0..5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_both_change(0..8, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(7).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn test_inc_ub_card<CE: BoundUpperIncremental + Extend<Lit> + Default>() {
    // Set up instance
    let mut solver = rustsat_minisat::core::Minisat::default();
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

    let mut enc = CE::default();
    enc.extend(vec![lit![0], lit![1], lit![2], lit![3], lit![4]]);

    enc.encode_ub(2..3, &mut solver, &mut var_manager).unwrap();
    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    enc.extend(vec![lit![5]]);

    enc.encode_ub_change(0..4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    enc.extend(vec![lit![6], lit![7], lit![8], lit![9], lit![10]]);

    enc.encode_ub_change(0..5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..8, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(7).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn test_both_card<CE: BoundBoth + From<Vec<Lit>>>() {
    // Set up instance
    let mut solver = rustsat_minisat::core::Minisat::default();
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
    let mut enc = CE::from(vec![!lit![0], !lit![1], !lit![2], !lit![3], !lit![4]]);

    enc.encode_both(2..4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let assumps = enc.enforce_lb(3).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let assumps = enc.enforce_lb(2).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

/// Requires a cardinality encoding with upper and lower bounding functionality
fn test_both_card_min_enc<CE: BoundBoth + From<Vec<Lit>>>() {
    // Set up instance
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    let mut enc = CE::from(vec![lit![0], lit![1], lit![2], lit![3]]);

    enc.encode_both(3..4, &mut solver, &mut var_manager)
        .unwrap();
    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], lit![1], lit![2], !lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2], lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2], lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2], lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], lit![2], lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], lit![1], !lit![2], lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2], !lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], !lit![1], !lit![2], lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2], !lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(3).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2], !lit![3]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);
}

#[test]
fn tot_inc_both() {
    test_inc_both_card::<Totalizer>()
}

#[test]
fn tot_both() {
    test_both_card::<Totalizer>()
}

#[test]
fn tot_min_enc() {
    test_both_card_min_enc::<Totalizer>()
}

#[test]
fn invertet_tot() {
    test_inc_both_card::<Inverted<Totalizer>>()
}

#[test]
fn double_invertet_tot() {
    test_inc_both_card::<Double<Inverted<Totalizer>, Inverted<Totalizer>>>()
}

#[test]
fn tot_inc_ub() {
    test_inc_ub_card::<Totalizer>()
}

#[test]
fn dbtot_inc_ub() {
    test_inc_ub_card::<DbTotalizer>()
}

use rustsat_tools::{test_all, test_assignment};

fn test_ub_exhaustive<CE: BoundUpperIncremental + From<Vec<Lit>>>() {
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut enc = CE::from(vec![lit![0], lit![1], lit![2], lit![3]]);
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    enc.encode_ub(0..1, &mut solver, &mut var_manager).unwrap();
    let assumps = enc.enforce_ub(0).unwrap();

    test_all!(
        solver, assumps, //
        Unsat,   // 1111
        Unsat,   // 1110
        Unsat,   // 1101
        Unsat,   // 1100
        Unsat,   // 1011
        Unsat,   // 1010
        Unsat,   // 1001
        Unsat,   // 1000
        Unsat,   // 0111
        Unsat,   // 0110
        Unsat,   // 0101
        Unsat,   // 0100
        Unsat,   // 0011
        Unsat,   // 0010
        Unsat,   // 0001
        Sat      // 0000
    );

    enc.encode_ub_change(1..2, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(1).unwrap();

    test_all!(
        solver, assumps, //
        Unsat,   // 1111
        Unsat,   // 1110
        Unsat,   // 1101
        Unsat,   // 1100
        Unsat,   // 1011
        Unsat,   // 1010
        Unsat,   // 1001
        Sat,     // 1000
        Unsat,   // 0111
        Unsat,   // 0110
        Unsat,   // 0101
        Sat,     // 0100
        Unsat,   // 0011
        Sat,     // 0010
        Sat,     // 0001
        Sat      // 0000
    );

    enc.encode_ub_change(2..3, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(2).unwrap();

    test_all!(
        solver, assumps, //
        Unsat,   // 1111
        Unsat,   // 1110
        Unsat,   // 1101
        Sat,     // 1100
        Unsat,   // 1011
        Sat,     // 1010
        Sat,     // 1001
        Sat,     // 1000
        Unsat,   // 0111
        Sat,     // 0110
        Sat,     // 0101
        Sat,     // 0100
        Sat,     // 0011
        Sat,     // 0010
        Sat,     // 0001
        Sat      // 0000
    );

    enc.encode_ub_change(3..4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();

    test_all!(
        solver, assumps, //
        Unsat,   // 1111
        Sat,     // 1110
        Sat,     // 1101
        Sat,     // 1100
        Sat,     // 1011
        Sat,     // 1010
        Sat,     // 1001
        Sat,     // 1000
        Sat,     // 0111
        Sat,     // 0110
        Sat,     // 0101
        Sat,     // 0100
        Sat,     // 0011
        Sat,     // 0010
        Sat,     // 0001
        Sat      // 0000
    );

    enc.encode_ub_change(4..5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();

    test_all!(
        solver, assumps, //
        Sat,     // 1111
        Sat,     // 1110
        Sat,     // 1101
        Sat,     // 1100
        Sat,     // 1011
        Sat,     // 1010
        Sat,     // 1001
        Sat,     // 1000
        Sat,     // 0111
        Sat,     // 0110
        Sat,     // 0101
        Sat,     // 0100
        Sat,     // 0011
        Sat,     // 0010
        Sat,     // 0001
        Sat      // 0000
    );
}

fn test_both_exhaustive<CE: BoundBothIncremental + From<Vec<Lit>>>() {
    let mut solver = rustsat_tools::Solver::default();
    let mut enc = CE::from(vec![lit![0], lit![1], lit![2], lit![3]]);
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    enc.encode_both(0..1, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(0).unwrap();

    test_all!(
        solver, assumps, //
        Unsat,   // 1111
        Unsat,   // 1110
        Unsat,   // 1101
        Unsat,   // 1100
        Unsat,   // 1011
        Unsat,   // 1010
        Unsat,   // 1001
        Unsat,   // 1000
        Unsat,   // 0111
        Unsat,   // 0110
        Unsat,   // 0101
        Unsat,   // 0100
        Unsat,   // 0011
        Unsat,   // 0010
        Unsat,   // 0001
        Sat      // 0000
    );

    enc.encode_both_change(1..2, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(1).unwrap();

    test_all!(
        solver, assumps, //
        Unsat,   // 1111
        Unsat,   // 1110
        Unsat,   // 1101
        Unsat,   // 1100
        Unsat,   // 1011
        Unsat,   // 1010
        Unsat,   // 1001
        Sat,     // 1000
        Unsat,   // 0111
        Unsat,   // 0110
        Unsat,   // 0101
        Sat,     // 0100
        Unsat,   // 0011
        Sat,     // 0010
        Sat,     // 0001
        Unsat    // 0000
    );

    enc.encode_both_change(2..3, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(2).unwrap();

    test_all!(
        solver, assumps, //
        Unsat,   // 1111
        Unsat,   // 1110
        Unsat,   // 1101
        Sat,     // 1100
        Unsat,   // 1011
        Sat,     // 1010
        Sat,     // 1001
        Unsat,   // 1000
        Unsat,   // 0111
        Sat,     // 0110
        Sat,     // 0101
        Unsat,   // 0100
        Sat,     // 0011
        Unsat,   // 0010
        Unsat,   // 0001
        Unsat    // 0000
    );

    enc.encode_both_change(3..4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(3).unwrap();

    test_all!(
        solver, assumps, //
        Unsat,   // 1111
        Sat,     // 1110
        Sat,     // 1101
        Unsat,   // 1100
        Sat,     // 1011
        Unsat,   // 1010
        Unsat,   // 1001
        Unsat,   // 1000
        Sat,     // 0111
        Unsat,   // 0110
        Unsat,   // 0101
        Unsat,   // 0100
        Unsat,   // 0011
        Unsat,   // 0010
        Unsat,   // 0001
        Unsat    // 0000
    );

    enc.encode_both_change(4..5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(4).unwrap();

    test_all!(
        solver, assumps, //
        Sat,     // 1111
        Unsat,   // 1110
        Unsat,   // 1101
        Unsat,   // 1100
        Unsat,   // 1011
        Unsat,   // 1010
        Unsat,   // 1001
        Unsat,   // 1000
        Unsat,   // 0111
        Unsat,   // 0110
        Unsat,   // 0101
        Unsat,   // 0100
        Unsat,   // 0011
        Unsat,   // 0010
        Unsat,   // 0001
        Unsat    // 0000
    );
}

#[test]
fn tot_ub_exhaustive() {
    test_ub_exhaustive::<Totalizer>()
}

#[test]
fn tot_both_exhaustive() {
    test_both_exhaustive::<Totalizer>()
}

#[test]
fn invtot_both_exhaustive() {
    test_both_exhaustive::<Inverted<Totalizer>>()
}

#[test]
fn dbtot_ub_exhaustive() {
    test_ub_exhaustive::<DbTotalizer>()
}
