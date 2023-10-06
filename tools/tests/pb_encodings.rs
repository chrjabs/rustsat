use rustsat::{
    clause,
    encodings::{
        card::Totalizer,
        pb::{
            simulators::Card, BoundBoth, BoundBothIncremental, BoundLower, BoundUpper,
            BoundUpperIncremental, DbGte, DoubleGeneralizedTotalizer, DynamicPolyWatchdog,
            GeneralizedTotalizer, InvertedGeneralizedTotalizer,
        },
    },
    instances::{BasicVarManager, ManageVars},
    lit,
    solvers::{
        Solve, SolveIncremental,
        SolverResult::{self, Sat, Unsat},
    },
    types::{Lit, RsHashMap},
    var,
};
use rustsat_cadical::CaDiCaL;

fn test_inc_pb_ub<PBE: BoundUpperIncremental>(mut enc: PBE) {
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

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    lits.insert(lit![3], 3);
    lits.insert(lit![4], 2);
    enc.extend(lits);

    enc.encode_ub(0..3, &mut solver, &mut var_manager);
    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..5, &mut solver, &mut var_manager);
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..6, &mut solver, &mut var_manager);
    let assumps = enc.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut lits = RsHashMap::default();
    lits.insert(lit![5], 4);
    enc.extend(lits);

    enc.encode_ub_change(0..6, &mut solver, &mut var_manager);
    let assumps = enc.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..10, &mut solver, &mut var_manager);
    let assumps = enc.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut lits = RsHashMap::default();
    lits.insert(lit![6], 1);
    lits.insert(lit![7], 2);
    lits.insert(lit![8], 1);
    lits.insert(lit![9], 3);
    lits.insert(lit![10], 2);
    enc.extend(lits);

    enc.encode_ub_change(0..10, &mut solver, &mut var_manager);
    let assumps = enc.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..15, &mut solver, &mut var_manager);
    let assumps = enc.enforce_ub(14).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn test_pb_eq<PBE: BoundBothIncremental>(mut enc: PBE) {
    // Set up instance
    let mut solver = CaDiCaL::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![3]);

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 4);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 2);
    enc.extend(lits);

    enc.encode_both(4..5, &mut solver, &mut var_manager);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![!lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_eq(4).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);
}

fn test_pb_lb<PBE: BoundLower>(mut enc: PBE) {
    // Set up instance
    let mut solver = CaDiCaL::default();
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

    enc.encode_lb(0..11, &mut solver, &mut var_manager);
    let assumps = enc.enforce_lb(10).unwrap();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let assumps = enc.enforce_lb(9).unwrap();
    println!("{:?}", assumps);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn test_pb_ub_min_enc<PBE: BoundUpper>(mut enc: PBE) {
    // Set up instance
    let mut solver = CaDiCaL::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    enc.extend(lits);

    enc.encode_ub(2..3, &mut solver, &mut var_manager);
    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], lit![1], lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], lit![1], !lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut assumps = enc.enforce_ub(2).unwrap();
    assumps.extend(vec![!lit![0], !lit![1], !lit![2]]);
    let res = solver.solve_assumps(&assumps).unwrap();
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

#[test]
fn dpw_ub() {
    let dpw = DynamicPolyWatchdog::default();
    test_inc_pb_ub(dpw);
}

#[test]
fn dpw_min_enc() {
    let dpw = DynamicPolyWatchdog::default();
    test_pb_ub_min_enc(dpw);
}

#[test]
fn dbgte_ub() {
    let gte = DbGte::default();
    test_inc_pb_ub(gte);
}

#[test]
fn dbgte_min_enc() {
    let gte = DbGte::default();
    test_pb_ub_min_enc(gte);
}

use rustsat_tools::{test_all, test_assignment};

fn test_ub_exhaustive<PBE: BoundUpperIncremental + From<RsHashMap<Lit, usize>>>(
    weights: [usize; 4],
    decreasing: bool,
) {
    let mut solver = CaDiCaL::default();
    let mut lits = RsHashMap::default();
    lits.insert(lit![0], weights[0]);
    lits.insert(lit![1], weights[1]);
    lits.insert(lit![2], weights[2]);
    lits.insert(lit![3], weights[3]);
    let mut enc = PBE::from(lits);
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    let max_val = weights.iter().fold(0, |sum, &w| sum + w);
    let expected = |assign: usize, bound: usize| {
        let sum = (0..4).fold(0, |sum, idx| sum + ((assign >> idx) & 1) * weights[3 - idx]);
        if sum <= bound {
            Sat
        } else {
            Unsat
        }
    };

    for mut bound in 0..=max_val {
        if decreasing {
            bound = max_val - bound;
        }

        enc.encode_ub_change(bound..bound + 1, &mut solver, &mut var_manager);
        let assumps = enc.enforce_ub(bound).unwrap();

        test_all!(
            solver,
            assumps, //
            expected(0b1111, bound),
            expected(0b1110, bound),
            expected(0b1101, bound),
            expected(0b1100, bound),
            expected(0b1011, bound),
            expected(0b1010, bound),
            expected(0b1001, bound),
            expected(0b1000, bound),
            expected(0b0111, bound),
            expected(0b0110, bound),
            expected(0b0101, bound),
            expected(0b0100, bound),
            expected(0b0011, bound),
            expected(0b0010, bound),
            expected(0b0001, bound),
            expected(0b0000, bound)
        );
    }
}

macro_rules! generate_exhaustive {
    ($mod:ident, $enc:ty) => {
        mod $mod {
            #[test]
            fn increasing_1111() {
                super::test_ub_exhaustive::<$enc>([1, 1, 1, 1], false);
            }

            #[test]
            fn decreasing_1111() {
                super::test_ub_exhaustive::<$enc>([1, 1, 1, 1], true);
            }

            #[test]
            fn increasing_7777() {
                super::test_ub_exhaustive::<$enc>([7, 7, 7, 7], false);
            }

            #[test]
            fn decreasing_7777() {
                super::test_ub_exhaustive::<$enc>([7, 7, 7, 7], true);
            }

            #[test]
            fn increasing_5533() {
                super::test_ub_exhaustive::<$enc>([5, 5, 3, 3], false);
            }

            #[test]
            fn decreasing_5533() {
                super::test_ub_exhaustive::<$enc>([5, 5, 3, 3], true);
            }

            #[test]
            fn increasing_2173() {
                super::test_ub_exhaustive::<$enc>([2, 1, 7, 3], true);
            }

            #[test]
            fn decreasing_2173() {
                super::test_ub_exhaustive::<$enc>([2, 1, 7, 3], true);
            }

            #[test]
            fn increasing_8918() {
                super::test_ub_exhaustive::<$enc>([8, 9, 1, 8], true);
            }

            #[test]
            fn decreasing_8918() {
                super::test_ub_exhaustive::<$enc>([8, 9, 1, 8], true);
            }

            #[test]
            fn increasing_5872() {
                super::test_ub_exhaustive::<$enc>([5, 8, 7, 2], true);
            }

            #[test]
            fn decreasing_5872() {
                super::test_ub_exhaustive::<$enc>([5, 8, 7, 2], true);
            }
        }
    };
}

generate_exhaustive!(gte, rustsat::encodings::pb::GeneralizedTotalizer);

generate_exhaustive!(dbgte, rustsat::encodings::pb::DbGte);

generate_exhaustive!(dpw, rustsat::encodings::pb::DynamicPolyWatchdog);
