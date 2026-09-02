use rustsat::clause;
use rustsat::encodings::card::BoundBoth;
use rustsat::encodings::card::BoundBothIncremental;
use rustsat::encodings::card::BoundUpperIncremental;
use rustsat::encodings::card::Totalizer;
use rustsat::encodings::card::simulators::Double;
use rustsat::encodings::card::simulators::Inverted;
use rustsat::instances::BasicVarManager;
use rustsat::instances::ManageVars;
use rustsat::lit;
use rustsat::solvers::Solve;
use rustsat::solvers::SolveIncremental;
use rustsat::solvers::SolverResult;
use rustsat::types::Lit;
use rustsat::var;

mod common;
use common::test_all;

fn test_inc_both_card<CE: BoundBothIncremental + Extend<Lit> + Default>() {
    // Set up instance
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_clause(lit![0] | lit![1]).unwrap();
    solver.add_clause(clause![lit![1]]).unwrap();
    solver.add_clause(lit![1] | lit![2]).unwrap();
    solver.add_clause(lit![2] | lit![3]).unwrap();
    solver.add_clause(lit![3] | lit![4]).unwrap();
    solver.add_clause(clause![lit![4]]).unwrap();
    solver.add_clause(clause![lit![5]]).unwrap();
    solver.add_clause(lit![6] | lit![7]).unwrap();
    solver.add_clause(clause![lit![7]]).unwrap();
    solver.add_clause(lit![7] | lit![8]).unwrap();
    solver.add_clause(lit![8] | lit![9]).unwrap();
    solver.add_clause(lit![9] | lit![10]).unwrap();
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
    solver.add_clause(lit![0] | lit![1]).unwrap();
    solver.add_clause(clause![lit![1]]).unwrap();
    solver.add_clause(lit![1] | lit![2]).unwrap();
    solver.add_clause(lit![2] | lit![3]).unwrap();
    solver.add_clause(lit![3] | lit![4]).unwrap();
    solver.add_clause(clause![lit![4]]).unwrap();
    solver.add_clause(clause![lit![5]]).unwrap();
    solver.add_clause(lit![6] | lit![7]).unwrap();
    solver.add_clause(clause![lit![7]]).unwrap();
    solver.add_clause(lit![7] | lit![8]).unwrap();
    solver.add_clause(lit![8] | lit![9]).unwrap();
    solver.add_clause(lit![9] | lit![10]).unwrap();
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
    solver.add_clause(lit![0] | lit![1]).unwrap();
    solver.add_clause(clause![lit![1]]).unwrap();
    solver.add_clause(lit![1] | lit![2]).unwrap();
    solver.add_clause(lit![2] | lit![3]).unwrap();
    solver.add_clause(lit![3] | lit![4]).unwrap();
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
fn tot_inc_ub() {
    test_inc_ub_card::<Totalizer>()
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

fn test_ub_exhaustive<CE: BoundUpperIncremental + From<Vec<Lit>>>() {
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut enc = CE::from(vec![lit![0], lit![1], lit![2], lit![3]]);
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    enc.encode_ub(0..1, &mut solver, &mut var_manager).unwrap();
    let assumps = enc.enforce_ub(0).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Unsat, // 1111
        SolverResult::Unsat, // 1110
        SolverResult::Unsat, // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Unsat, // 1011
        SolverResult::Unsat, // 1010
        SolverResult::Unsat, // 1001
        SolverResult::Unsat, // 1000
        SolverResult::Unsat, // 0111
        SolverResult::Unsat, // 0110
        SolverResult::Unsat, // 0101
        SolverResult::Unsat, // 0100
        SolverResult::Unsat, // 0011
        SolverResult::Unsat, // 0010
        SolverResult::Unsat, // 0001
        SolverResult::Sat    // 0000
    );

    enc.encode_ub_change(1..2, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(1).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Unsat, // 1111
        SolverResult::Unsat, // 1110
        SolverResult::Unsat, // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Unsat, // 1011
        SolverResult::Unsat, // 1010
        SolverResult::Unsat, // 1001
        SolverResult::Sat,   // 1000
        SolverResult::Unsat, // 0111
        SolverResult::Unsat, // 0110
        SolverResult::Unsat, // 0101
        SolverResult::Sat,   // 0100
        SolverResult::Unsat, // 0011
        SolverResult::Sat,   // 0010
        SolverResult::Sat,   // 0001
        SolverResult::Sat    // 0000
    );

    enc.encode_ub_change(2..3, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(2).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Unsat, // 1111
        SolverResult::Unsat, // 1110
        SolverResult::Unsat, // 1101
        SolverResult::Sat,   // 1100
        SolverResult::Unsat, // 1011
        SolverResult::Sat,   // 1010
        SolverResult::Sat,   // 1001
        SolverResult::Sat,   // 1000
        SolverResult::Unsat, // 0111
        SolverResult::Sat,   // 0110
        SolverResult::Sat,   // 0101
        SolverResult::Sat,   // 0100
        SolverResult::Sat,   // 0011
        SolverResult::Sat,   // 0010
        SolverResult::Sat,   // 0001
        SolverResult::Sat    // 0000
    );

    enc.encode_ub_change(3..4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(3).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Unsat, // 1111
        SolverResult::Sat,   // 1110
        SolverResult::Sat,   // 1101
        SolverResult::Sat,   // 1100
        SolverResult::Sat,   // 1011
        SolverResult::Sat,   // 1010
        SolverResult::Sat,   // 1001
        SolverResult::Sat,   // 1000
        SolverResult::Sat,   // 0111
        SolverResult::Sat,   // 0110
        SolverResult::Sat,   // 0101
        SolverResult::Sat,   // 0100
        SolverResult::Sat,   // 0011
        SolverResult::Sat,   // 0010
        SolverResult::Sat,   // 0001
        SolverResult::Sat    // 0000
    );

    enc.encode_ub_change(4..5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Sat, // 1111
        SolverResult::Sat, // 1110
        SolverResult::Sat, // 1101
        SolverResult::Sat, // 1100
        SolverResult::Sat, // 1011
        SolverResult::Sat, // 1010
        SolverResult::Sat, // 1001
        SolverResult::Sat, // 1000
        SolverResult::Sat, // 0111
        SolverResult::Sat, // 0110
        SolverResult::Sat, // 0101
        SolverResult::Sat, // 0100
        SolverResult::Sat, // 0011
        SolverResult::Sat, // 0010
        SolverResult::Sat, // 0001
        SolverResult::Sat  // 0000
    );
}

fn test_both_exhaustive<CE: BoundBothIncremental + From<Vec<Lit>>>() {
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut enc = CE::from(vec![lit![0], lit![1], lit![2], lit![3]]);
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    enc.encode_both(0..1, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(0).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Unsat, // 1111
        SolverResult::Unsat, // 1110
        SolverResult::Unsat, // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Unsat, // 1011
        SolverResult::Unsat, // 1010
        SolverResult::Unsat, // 1001
        SolverResult::Unsat, // 1000
        SolverResult::Unsat, // 0111
        SolverResult::Unsat, // 0110
        SolverResult::Unsat, // 0101
        SolverResult::Unsat, // 0100
        SolverResult::Unsat, // 0011
        SolverResult::Unsat, // 0010
        SolverResult::Unsat, // 0001
        SolverResult::Sat    // 0000
    );

    enc.encode_both_change(1..2, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(1).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Unsat, // 1111
        SolverResult::Unsat, // 1110
        SolverResult::Unsat, // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Unsat, // 1011
        SolverResult::Unsat, // 1010
        SolverResult::Unsat, // 1001
        SolverResult::Sat,   // 1000
        SolverResult::Unsat, // 0111
        SolverResult::Unsat, // 0110
        SolverResult::Unsat, // 0101
        SolverResult::Sat,   // 0100
        SolverResult::Unsat, // 0011
        SolverResult::Sat,   // 0010
        SolverResult::Sat,   // 0001
        SolverResult::Unsat  // 0000
    );

    enc.encode_both_change(2..3, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(2).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Unsat, // 1111
        SolverResult::Unsat, // 1110
        SolverResult::Unsat, // 1101
        SolverResult::Sat,   // 1100
        SolverResult::Unsat, // 1011
        SolverResult::Sat,   // 1010
        SolverResult::Sat,   // 1001
        SolverResult::Unsat, // 1000
        SolverResult::Unsat, // 0111
        SolverResult::Sat,   // 0110
        SolverResult::Sat,   // 0101
        SolverResult::Unsat, // 0100
        SolverResult::Sat,   // 0011
        SolverResult::Unsat, // 0010
        SolverResult::Unsat, // 0001
        SolverResult::Unsat  // 0000
    );

    enc.encode_both_change(3..4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(3).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Unsat, // 1111
        SolverResult::Sat,   // 1110
        SolverResult::Sat,   // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Sat,   // 1011
        SolverResult::Unsat, // 1010
        SolverResult::Unsat, // 1001
        SolverResult::Unsat, // 1000
        SolverResult::Sat,   // 0111
        SolverResult::Unsat, // 0110
        SolverResult::Unsat, // 0101
        SolverResult::Unsat, // 0100
        SolverResult::Unsat, // 0011
        SolverResult::Unsat, // 0010
        SolverResult::Unsat, // 0001
        SolverResult::Unsat  // 0000
    );

    enc.encode_both_change(4..5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_eq(4).unwrap();

    test_all!(
        solver,
        assumps,
        SolverResult::Sat,   // 1111
        SolverResult::Unsat, // 1110
        SolverResult::Unsat, // 1101
        SolverResult::Unsat, // 1100
        SolverResult::Unsat, // 1011
        SolverResult::Unsat, // 1010
        SolverResult::Unsat, // 1001
        SolverResult::Unsat, // 1000
        SolverResult::Unsat, // 0111
        SolverResult::Unsat, // 0110
        SolverResult::Unsat, // 0101
        SolverResult::Unsat, // 0100
        SolverResult::Unsat, // 0011
        SolverResult::Unsat, // 0010
        SolverResult::Unsat, // 0001
        SolverResult::Unsat  // 0000
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

#[cfg(feature = "proof-logging")]
mod cert {
    use std::io::BufRead;

    use rustsat::clause;
    use rustsat::encodings::card::Totalizer;
    use rustsat::encodings::card::cert::BoundBothIncremental;
    use rustsat::instances::BasicVarManager;
    use rustsat::instances::Cnf;
    use rustsat::instances::ManageVars;
    use rustsat::lit;
    use rustsat::solvers::Solve;
    use rustsat::solvers::SolveIncremental;
    use rustsat::solvers::SolverResult;
    use rustsat::types::Lit;
    use rustsat::types::Var;
    use rustsat::var;

    use crate::common::test_all;

    fn test_inc_both_card<CE: BoundBothIncremental + Extend<Lit> + Default>() {
        // Set up instance
        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_clause(lit![0] | lit![1]).unwrap();
        solver.add_clause(clause![lit![1]]).unwrap();
        solver.add_clause(lit![1] | lit![2]).unwrap();
        solver.add_clause(lit![2] | lit![3]).unwrap();
        solver.add_clause(lit![3] | lit![4]).unwrap();
        solver.add_clause(clause![lit![4]]).unwrap();
        solver.add_clause(clause![lit![5]]).unwrap();
        solver.add_clause(lit![6] | lit![7]).unwrap();
        solver.add_clause(clause![lit![7]]).unwrap();
        solver.add_clause(lit![7] | lit![8]).unwrap();
        solver.add_clause(lit![8] | lit![9]).unwrap();
        solver.add_clause(lit![9] | lit![10]).unwrap();
        solver.add_clause(clause![lit![10]]).unwrap();
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![11]);

        let mut proof = new_proof(0, false);
        let mut cnf = Cnf::new();

        let res = solver.solve().unwrap();
        assert_eq!(res, SolverResult::Sat);

        let mut enc = CE::default();
        enc.extend(vec![lit![0], lit![1], lit![2], lit![3], lit![4]]);

        enc.encode_both_cert(2..3, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"first block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_lb(2).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Sat);

        let assumps = enc.enforce_ub(2).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Unsat);

        enc.encode_both_change_cert(0..4, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"second block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(3).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Sat);

        enc.extend(vec![lit![5]]);

        enc.encode_both_change_cert(0..4, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"third block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(3).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Unsat);

        enc.encode_both_change_cert(0..5, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"fourth block done").unwrap();
        let assumps = enc.enforce_ub(4).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Sat);

        enc.extend(vec![lit![6], lit![7], lit![8], lit![9], lit![10]]);

        enc.encode_both_change_cert(0..5, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"fifth block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(4).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Unsat);

        enc.encode_both_change_cert(0..8, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"sixth block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(7).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Sat);

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    fn test_both_exhaustive<CE: BoundBothIncremental + From<Vec<Lit>>>() {
        let mut solver = rustsat_minisat::core::Minisat::default();
        let mut enc = CE::from(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut proof = new_proof(0, false);
        let mut cnf = Cnf::new();

        enc.encode_both_cert(0..1, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"first block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_eq(0).unwrap();

        test_all!(
            solver,
            assumps,
            SolverResult::Unsat, // 1111
            SolverResult::Unsat, // 1110
            SolverResult::Unsat, // 1101
            SolverResult::Unsat, // 1100
            SolverResult::Unsat, // 1011
            SolverResult::Unsat, // 1010
            SolverResult::Unsat, // 1001
            SolverResult::Unsat, // 1000
            SolverResult::Unsat, // 0111
            SolverResult::Unsat, // 0110
            SolverResult::Unsat, // 0101
            SolverResult::Unsat, // 0100
            SolverResult::Unsat, // 0011
            SolverResult::Unsat, // 0010
            SolverResult::Unsat, // 0001
            SolverResult::Sat    // 0000
        );

        enc.encode_both_change_cert(1..2, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"second block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_eq(1).unwrap();

        test_all!(
            solver,
            assumps,
            SolverResult::Unsat, // 1111
            SolverResult::Unsat, // 1110
            SolverResult::Unsat, // 1101
            SolverResult::Unsat, // 1100
            SolverResult::Unsat, // 1011
            SolverResult::Unsat, // 1010
            SolverResult::Unsat, // 1001
            SolverResult::Sat,   // 1000
            SolverResult::Unsat, // 0111
            SolverResult::Unsat, // 0110
            SolverResult::Unsat, // 0101
            SolverResult::Sat,   // 0100
            SolverResult::Unsat, // 0011
            SolverResult::Sat,   // 0010
            SolverResult::Sat,   // 0001
            SolverResult::Unsat  // 0000
        );

        enc.encode_both_change_cert(2..3, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"third block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_eq(2).unwrap();

        test_all!(
            solver,
            assumps,
            SolverResult::Unsat, // 1111
            SolverResult::Unsat, // 1110
            SolverResult::Unsat, // 1101
            SolverResult::Sat,   // 1100
            SolverResult::Unsat, // 1011
            SolverResult::Sat,   // 1010
            SolverResult::Sat,   // 1001
            SolverResult::Unsat, // 1000
            SolverResult::Unsat, // 0111
            SolverResult::Sat,   // 0110
            SolverResult::Sat,   // 0101
            SolverResult::Unsat, // 0100
            SolverResult::Sat,   // 0011
            SolverResult::Unsat, // 0010
            SolverResult::Unsat, // 0001
            SolverResult::Unsat  // 0000
        );

        enc.encode_both_change_cert(3..4, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"fourth block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_eq(3).unwrap();

        test_all!(
            solver,
            assumps,
            SolverResult::Unsat, // 1111
            SolverResult::Sat,   // 1110
            SolverResult::Sat,   // 1101
            SolverResult::Unsat, // 1100
            SolverResult::Sat,   // 1011
            SolverResult::Unsat, // 1010
            SolverResult::Unsat, // 1001
            SolverResult::Unsat, // 1000
            SolverResult::Sat,   // 0111
            SolverResult::Unsat, // 0110
            SolverResult::Unsat, // 0101
            SolverResult::Unsat, // 0100
            SolverResult::Unsat, // 0011
            SolverResult::Unsat, // 0010
            SolverResult::Unsat, // 0001
            SolverResult::Unsat  // 0000
        );

        enc.encode_both_change_cert(4..5, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"fifth block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_eq(4).unwrap();

        test_all!(
            solver,
            assumps,
            SolverResult::Sat,   // 1111
            SolverResult::Unsat, // 1110
            SolverResult::Unsat, // 1101
            SolverResult::Unsat, // 1100
            SolverResult::Unsat, // 1011
            SolverResult::Unsat, // 1010
            SolverResult::Unsat, // 1001
            SolverResult::Unsat, // 1000
            SolverResult::Unsat, // 0111
            SolverResult::Unsat, // 0110
            SolverResult::Unsat, // 0101
            SolverResult::Unsat, // 0100
            SolverResult::Unsat, // 0011
            SolverResult::Unsat, // 0010
            SolverResult::Unsat, // 0001
            SolverResult::Unsat  // 0000
        );
    }

    fn print_file<P: AsRef<std::path::Path>>(path: P) {
        println!();
        for line in
            std::io::BufReader::new(std::fs::File::open(path).expect("could not open file")).lines()
        {
            println!("{}", line.unwrap());
        }
        println!();
    }

    fn verify_proof<P1: AsRef<std::path::Path>, P2: AsRef<std::path::Path>>(
        instance: P1,
        proof: P2,
    ) {
        if let Ok(veripb) = std::env::var("VERIPB_CHECKER") {
            println!("start checking proof");
            let out = std::process::Command::new(veripb)
                .arg(instance.as_ref())
                .arg(proof.as_ref())
                .output()
                .expect("failed to run veripb");
            print_file(proof);
            if out.status.success() {
                return;
            }
            panic!("verification failed: {out:?}")
        } else {
            println!("`$VERIPB_CHECKER` not set, omitting proof checking");
        }
    }

    fn new_proof(
        num_constraints: usize,
        optimization: bool,
    ) -> pigeons::Proof<tempfile::NamedTempFile> {
        let file = tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
        pigeons::Proof::new(file, num_constraints, optimization).expect("failed to start proof")
    }

    #[test]
    fn tot_inc_both() {
        test_inc_both_card::<Totalizer>()
    }

    #[test]
    fn tot_both_exhaustive() {
        test_both_exhaustive::<Totalizer>()
    }
}
