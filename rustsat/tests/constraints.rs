use rustsat::{
    instances::SatInstance,
    lit,
    solvers::{Solve, SolveIncremental, SolverResult},
    types::{
        constraints::{CardConstraint, PBConstraint},
        RsHashMap,
    },
};

macro_rules! test_card {
    ( $constr:expr, $sat_assump:expr, $unsat_assump:expr ) => {{
        let mut inst: SatInstance = SatInstance::new();
        inst.add_card_constr($constr);
        let (cnf, _) = inst.into_cnf();
        println!("{:?}", cnf);
        let mut solver = rustsat_tools::Solver::default();
        solver.add_cnf(cnf).unwrap();
        assert_eq!(
            solver.solve_assumps($sat_assump).unwrap(),
            SolverResult::Sat
        );
        assert_eq!(
            solver.solve_assumps($unsat_assump).unwrap(),
            SolverResult::Unsat
        );
    }};
}

macro_rules! test_pb {
    ( $constr:expr, $sat_assump:expr, $unsat_assump:expr ) => {{
        let mut inst: SatInstance = SatInstance::new();
        inst.add_pb_constr($constr);
        let (cnf, _) = inst.into_cnf();
        println!("{:?}", cnf);
        let mut solver = rustsat_tools::Solver::default();
        solver.add_cnf(cnf).unwrap();
        assert_eq!(
            solver.solve_assumps($sat_assump).unwrap(),
            SolverResult::Sat
        );
        assert_eq!(
            solver.solve_assumps($unsat_assump).unwrap(),
            SolverResult::Unsat
        );
    }};
}

#[test]
fn card_ub() {
    let lits = vec![lit![0], lit![1], lit![2]];
    test_card!(
        CardConstraint::new_ub(lits.clone(), 1),
        &[!lit![0], lit![1], !lit![2]],
        &[lit![0], lit![1], !lit![2]]
    );
    test_card!(
        CardConstraint::new_ub(lits.clone(), 2),
        &[lit![0], lit![1], !lit![2]],
        &[lit![0], lit![1], lit![2]]
    );
}

#[test]
fn card_lb() {
    let lits = vec![lit![0], lit![1], lit![2]];
    test_card!(
        CardConstraint::new_lb(lits.clone(), 1),
        &[lit![0], lit![1], !lit![2]],
        &[!lit![0], !lit![1], !lit![2]]
    );
    test_card!(
        CardConstraint::new_lb(lits.clone(), 2),
        &[lit![0], lit![1], !lit![2]],
        &[!lit![0], !lit![1], !lit![2]]
    );
    test_card!(
        CardConstraint::new_lb(lits.clone(), 3),
        &[lit![0], lit![1], lit![2]],
        &[!lit![0], lit![1], !lit![2]]
    );
}

#[test]
fn card_eq() {
    let lits = vec![lit![0], lit![1], lit![2]];
    test_card!(
        CardConstraint::new_eq(lits.clone(), 1),
        &[lit![0], !lit![1], !lit![2]],
        &[!lit![0], lit![1], lit![2]]
    );
    test_card!(
        CardConstraint::new_eq(lits.clone(), 2),
        &[lit![0], lit![1], !lit![2]],
        &[!lit![0], !lit![1], !lit![2]]
    );
    test_card!(
        CardConstraint::new_eq(lits.clone(), 3),
        &[lit![0], lit![1], lit![2]],
        &[!lit![0], lit![1], !lit![2]]
    );
}

#[test]
fn pb_ub() {
    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 3);
    test_pb!(
        PBConstraint::new_eq(lits.clone(), 1),
        &[lit![0], !lit![1], !lit![2]],
        &[!lit![0], lit![1], !lit![2]]
    );
    test_pb!(
        PBConstraint::new_eq(lits.clone(), 2),
        &[!lit![0], lit![1], !lit![2]],
        &[!lit![0], !lit![1], lit![2]]
    );
    test_pb!(
        PBConstraint::new_eq(lits.clone(), 3),
        &[!lit![0], !lit![1], lit![2]],
        &[lit![0], !lit![1], lit![2]]
    );
}

#[test]
fn pb_lb() {
    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 3);
    test_pb!(
        PBConstraint::new_lb(lits.clone(), 1),
        &[lit![0], lit![1], !lit![2]],
        &[!lit![0], !lit![1], !lit![2]]
    );
    test_pb!(
        PBConstraint::new_lb(lits.clone(), 2),
        &[lit![0], lit![1], !lit![2]],
        &[lit![0], !lit![1], !lit![2]]
    );
    test_pb!(
        PBConstraint::new_lb(lits.clone(), 3),
        &[!lit![0], !lit![1], lit![2]],
        &[!lit![0], lit![1], !lit![2]]
    );
}

#[test]
fn pb_eq() {
    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 3);
    test_pb!(
        PBConstraint::new_eq(lits.clone(), 1),
        &[lit![0], !lit![1], !lit![2]],
        &[!lit![0], lit![1], lit![2]]
    );
    test_pb!(
        PBConstraint::new_eq(lits.clone(), 2),
        &[!lit![0], lit![1], !lit![2]],
        &[!lit![0], !lit![1], !lit![2]]
    );
    test_pb!(
        PBConstraint::new_eq(lits.clone(), 3),
        &[!lit![0], !lit![1], lit![2]],
        &[!lit![0], lit![1], !lit![2]]
    );
}

#[test]
fn card_clause() {
    let lits = vec![lit![0], lit![1], lit![2]];
    test_card!(
        CardConstraint::new_lb(lits.clone(), 1),
        &[lit![0], lit![1], !lit![2]],
        &[!lit![0], !lit![1], !lit![2]]
    );
    test_card!(
        CardConstraint::new_ub(lits.clone(), 2),
        &[!lit![0], lit![1], lit![2]],
        &[lit![0], lit![1], lit![2]]
    );
}

#[test]
fn pb_clause() {
    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 2);
    lits.insert(lit![1], 3);
    lits.insert(lit![2], 2);
    test_pb!(
        PBConstraint::new_ub(lits.clone(), 6),
        &[lit![0], !lit![1], !lit![2]],
        &[lit![0], lit![1], lit![2]]
    );
    test_pb!(
        PBConstraint::new_lb(lits.clone(), 2),
        &[lit![0], lit![1], !lit![2]],
        &[!lit![0], !lit![1], !lit![2]]
    );
}
