use rustsat::{
    clause,
    encodings::{
        card::Totalizer,
        pb::{
            simulators::Card, BinaryAdder, BoundBothIncremental, BoundLower, BoundUpper,
            BoundUpperIncremental, DoubleGeneralizedTotalizer, DynamicPolyWatchdog,
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

fn test_inc_pb_ub<PBE: BoundUpperIncremental + Extend<(Lit, usize)> + Default>() {
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

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    lits.insert(lit![3], 3);
    lits.insert(lit![4], 2);
    let mut enc = PBE::default();
    enc.extend(lits);

    enc.encode_ub(0..=2, &mut solver, &mut var_manager).unwrap();
    let assumps = enc.enforce_ub(2).unwrap();
    let res = solver.solve_assumps(dbg!(&assumps)).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..=4, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(4).unwrap();
    let res = solver.solve_assumps(dbg!(&assumps)).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..=5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(dbg!(&assumps)).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut lits = RsHashMap::default();
    lits.insert(lit![5], 4);
    enc.extend(lits);

    enc.encode_ub_change(0..=5, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(5).unwrap();
    let res = solver.solve_assumps(dbg!(&assumps)).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..=9, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(dbg!(&assumps)).unwrap();
    assert_eq!(res, SolverResult::Sat);

    let mut lits = RsHashMap::default();
    lits.insert(lit![6], 1);
    lits.insert(lit![7], 2);
    lits.insert(lit![8], 1);
    lits.insert(lit![9], 3);
    lits.insert(lit![10], 2);
    enc.extend(lits);

    enc.encode_ub_change(0..=9, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(9).unwrap();
    let res = solver.solve_assumps(dbg!(&assumps)).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    enc.encode_ub_change(0..=14, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_ub(14).unwrap();
    let res = solver.solve_assumps(dbg!(&assumps)).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn test_pb_eq<PBE: BoundBothIncremental + From<RsHashMap<Lit, usize>>>() {
    // Set up instance
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![3]);

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 4);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 2);
    let mut enc = PBE::from(lits);

    enc.encode_both(4..=4, &mut solver, &mut var_manager)
        .unwrap();

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

fn test_pb_lb<PBE: BoundLower + From<RsHashMap<Lit, usize>>>() {
    // Set up instance
    let mut solver = rustsat_minisat::core::Minisat::default();
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
    let mut enc = PBE::from(lits);

    enc.encode_lb(0..=10, &mut solver, &mut var_manager)
        .unwrap();
    let assumps = enc.enforce_lb(10).unwrap();
    let res = solver.solve_assumps(dbg!(&assumps)).unwrap();
    assert_eq!(res, SolverResult::Unsat);

    let assumps = enc.enforce_lb(9).unwrap();
    println!("{assumps:?}");
    let res = solver.solve_assumps(dbg!(&assumps)).unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn test_pb_ub_min_enc<PBE: BoundUpper + From<RsHashMap<Lit, usize>>>() {
    // Set up instance
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 1);
    lits.insert(lit![1], 2);
    lits.insert(lit![2], 1);
    let mut enc = PBE::from(lits);

    enc.encode_ub(2..=2, &mut solver, &mut var_manager).unwrap();
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
    test_inc_pb_ub::<GeneralizedTotalizer>()
}

#[test]
fn gte_lb() {
    test_pb_lb::<InvertedGeneralizedTotalizer>()
}

#[test]
fn gte_min_enc() {
    test_pb_ub_min_enc::<GeneralizedTotalizer>()
}

#[test]
fn gte_eq() {
    test_pb_eq::<DoubleGeneralizedTotalizer>()
}

#[test]
fn tot_pb_sim_eq() {
    test_pb_eq::<Card<Totalizer>>()
}

#[test]
fn dpw_min_enc() {
    test_pb_ub_min_enc::<DynamicPolyWatchdog>()
}

#[test]
fn adder_ub() {
    test_inc_pb_ub::<BinaryAdder>()
}

#[test]
fn adder_lb() {
    test_pb_lb::<BinaryAdder>()
}

#[test]
fn adder_eq() {
    test_pb_eq::<BinaryAdder>()
}

#[test]
fn adder_min_enc() {
    test_pb_ub_min_enc::<BinaryAdder>()
}

use rustsat_tools::{test_all, test_assignment};

fn test_ub_exhaustive<PBE: BoundUpperIncremental + From<RsHashMap<Lit, usize>>>(
    weights: [usize; 4],
    decreasing: bool,
) {
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut lits = RsHashMap::default();
    lits.insert(lit![0], weights[0]);
    lits.insert(lit![1], weights[1]);
    lits.insert(lit![2], weights[2]);
    lits.insert(lit![3], weights[3]);
    let mut enc = PBE::from(lits);
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    let max_val = weights.iter().sum::<usize>();
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
        println!("bound: {bound}");

        enc.encode_ub_change(bound..bound + 1, &mut solver, &mut var_manager)
            .unwrap();
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
            use rustsat::encodings::pb::*;

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
use generate_exhaustive;

generate_exhaustive!(gte, GeneralizedTotalizer);

generate_exhaustive!(dpw, DynamicPolyWatchdog);

generate_exhaustive!(
    gte_inv_inv,
    simulators::Inverted<simulators::Inverted<GeneralizedTotalizer>>
);

generate_exhaustive!(
    tot_sim,
    simulators::Card<rustsat::encodings::card::Totalizer>
);

generate_exhaustive!(adder, BinaryAdder);

mod dpw_inc_prec {
    use rustsat::{
        encodings::pb::{dpw::DynamicPolyWatchdog, BoundUpper, BoundUpperIncremental},
        instances::{BasicVarManager, Cnf, ManageVars, OptInstance},
        lit,
        solvers::{
            Solve, SolveIncremental,
            SolverResult::{self, Sat, Unsat},
        },
        types::RsHashMap,
        var,
    };
    use rustsat_tools::{test_all, test_assignment};

    #[test]
    fn incremental_precision() {
        let weights = [5, 8, 7, 3];
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], weights[0]);
        lits.insert(lit![1], weights[1]);
        lits.insert(lit![2], weights[2]);
        lits.insert(lit![3], weights[3]);
        for decreasing in [false, true] {
            println!("decreasing: {decreasing}");
            let mut solver = rustsat_minisat::core::Minisat::default();
            let mut enc = DynamicPolyWatchdog::from(lits.clone());
            let mut var_manager = BasicVarManager::default();
            var_manager.increase_next_free(var![4]);

            for prec in 0..3 {
                let prec_div = 1 << (3 - prec);
                println!("precision: {prec_div}");
                enc.set_precision(prec_div).unwrap();

                let max_val = weights.iter().fold(0, |sum, &w| sum + (w / prec_div));
                let expected = |assign: usize, bound: usize| {
                    let sum = (0..4).fold(0, |sum, idx| {
                        sum + ((assign >> idx) & 1) * (weights[3 - idx] / prec_div)
                    });
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
                    println!("bound: {bound}");
                    let mut cnf = Cnf::default();
                    enc.encode_ub_change(bound..bound + 1, &mut cnf, &mut var_manager)
                        .unwrap();
                    println!("extending encoding: {cnf:?}");
                    solver.add_cnf(cnf).unwrap();
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
        }
    }

    #[test]
    fn incremental_precision_2() {
        let inst: OptInstance = OptInstance::from_dimacs_path("./data/inc-sis-fails.wcnf").unwrap();
        let (constr, obj) = inst.decompose();
        let (cnf, mut vm) = constr.into_cnf();
        let (hardened, (softs, offset)) = obj.into_soft_lits(&mut vm);
        debug_assert!(hardened.is_empty());
        debug_assert_eq!(offset, 0);
        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(cnf).unwrap();
        let mut enc = DynamicPolyWatchdog::from_iter(softs);

        enc.set_precision(8192).unwrap();
        enc.encode_ub_change(0..=1, &mut solver, &mut vm).unwrap();
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(1).unwrap()).unwrap(),
            SolverResult::Sat
        );
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(0).unwrap()).unwrap(),
            SolverResult::Unsat
        );

        enc.set_precision(1024).unwrap();
        enc.encode_ub_change(0..=9, &mut solver, &mut vm).unwrap();
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(9).unwrap()).unwrap(),
            SolverResult::Sat
        );
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(8).unwrap()).unwrap(),
            SolverResult::Sat
        );
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(7).unwrap()).unwrap(),
            SolverResult::Unsat
        );
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(0).unwrap()).unwrap(),
            SolverResult::Unsat
        );
    }

    #[test]
    fn incremental_precision_3() {
        let inst: OptInstance = OptInstance::from_dimacs_path("./data/inc-sis-fails.wcnf").unwrap();
        let (constr, obj) = inst.decompose();
        let (cnf, mut vm) = constr.into_cnf();
        let (hardened, (softs, offset)) = obj.into_soft_lits(&mut vm);
        debug_assert!(hardened.is_empty());
        debug_assert_eq!(offset, 0);
        let mut solver = rustsat_minisat::core::Minisat::default();
        solver.add_cnf(cnf).unwrap();
        let mut enc = DynamicPolyWatchdog::from_iter(softs);

        enc.set_precision(2048).unwrap();
        enc.encode_ub_change(0..=4, &mut solver, &mut vm).unwrap();
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(4).unwrap()).unwrap(),
            SolverResult::Sat
        );
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(2).unwrap()).unwrap(),
            SolverResult::Unsat
        );
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(0).unwrap()).unwrap(),
            SolverResult::Unsat
        );

        enc.set_precision(1024).unwrap();
        enc.encode_ub_change(0..=9, &mut solver, &mut vm).unwrap();
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(9).unwrap()).unwrap(),
            SolverResult::Sat
        );
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(8).unwrap()).unwrap(),
            SolverResult::Sat
        );
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(7).unwrap()).unwrap(),
            SolverResult::Unsat
        );
        debug_assert_eq!(
            solver.solve_assumps(&enc.enforce_ub(0).unwrap()).unwrap(),
            SolverResult::Unsat
        );
    }
}

fn adder_fuzzing_bug<PBE: BoundUpper + FromIterator<(Lit, usize)>>() {
    let weights = [
        14, 53, 25, 55, 87, 64, 100, 41, 97, 4, 62, 42, 35, 74, 19, 85, 63, 14, 48, 1, 83, 94, 60,
        51, 87, 40, 72, 15, 81, 53,
    ];
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut var_manager = BasicVarManager::from_next_free(var![30]);
    let mut enc: PBE = weights
        .into_iter()
        .enumerate()
        .map(|(idx, w)| (Lit::new(idx as u32, false), w))
        .collect();
    enc.encode_ub(1..=1, &mut solver, &mut var_manager).unwrap();
    for unit in enc.enforce_ub(1).unwrap() {
        solver.add_clause(clause![unit]).unwrap();
    }
    let assumps = [
        1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 1,
    ];
    let assumps: Vec<_> = assumps
        .into_iter()
        .enumerate()
        .map(|(idx, val)| Lit::new(idx as u32, val == 0))
        .collect();
    let res = solver.solve_assumps(&assumps).unwrap();
    assert_eq!(res, SolverResult::Unsat)
}

#[test]
fn binary_adder_fuzzing_bug() {
    adder_fuzzing_bug::<BinaryAdder>();
}

#[test]
fn gte_fuzzing_bug() {
    adder_fuzzing_bug::<GeneralizedTotalizer>();
}

#[test]
fn dpw_fuzzing_bug() {
    adder_fuzzing_bug::<DynamicPolyWatchdog>();
}

#[cfg(feature = "proof-logging")]
mod cert {
    use std::{
        fs::File,
        io::{BufRead, BufReader},
        path::Path,
        process::Command,
    };

    use rustsat::{
        clause,
        encodings::pb::{cert::BoundUpperIncremental, GeneralizedTotalizer},
        instances::{BasicVarManager, Cnf, ManageVars},
        lit,
        solvers::{
            Solve, SolveIncremental,
            SolverResult::{self, Sat, Unsat},
        },
        types::{Lit, RsHashMap, Var},
        var,
    };

    use rustsat_tools::{test_all, test_assignment};

    fn test_inc_pb_ub<PBE: BoundUpperIncremental + Extend<(Lit, usize)> + Default>() {
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

        let mut proof = new_proof(0, false);
        let mut cnf = Cnf::new();

        let res = solver.solve().unwrap();
        assert_eq!(res, SolverResult::Sat);

        let mut lits = RsHashMap::default();
        lits.insert(lit![0], 1);
        lits.insert(lit![1], 2);
        lits.insert(lit![2], 1);
        lits.insert(lit![3], 3);
        lits.insert(lit![4], 2);
        let mut enc = PBE::default();
        enc.extend(lits);

        enc.encode_ub_cert(0..3, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"first block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(2).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Unsat);

        enc.encode_ub_change_cert(0..5, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"second block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(4).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Unsat);

        enc.encode_ub_change_cert(0..6, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"third block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(5).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Sat);

        let mut lits = RsHashMap::default();
        lits.insert(lit![5], 4);
        enc.extend(lits);

        enc.encode_ub_change_cert(0..6, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"fourth block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(5).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Unsat);

        enc.encode_ub_change_cert(0..10, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"fifth block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
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

        enc.encode_ub_change_cert(0..10, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"sixth block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(9).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Unsat);

        enc.encode_ub_change_cert(0..15, &mut cnf, &mut var_manager, &mut proof)
            .unwrap();
        proof.comment(&"seventh block done").unwrap();
        solver.add_cnf_ref(&cnf).unwrap();
        cnf.clear();
        let assumps = enc.enforce_ub(14).unwrap();
        let res = solver.solve_assumps(&assumps).unwrap();
        assert_eq!(res, SolverResult::Sat);

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    fn test_ub_exhaustive<PBE: BoundUpperIncremental + From<RsHashMap<Lit, usize>>>(
        weights: [usize; 4],
        decreasing: bool,
    ) {
        let mut solver = rustsat_minisat::core::Minisat::default();
        let mut lits = RsHashMap::default();
        lits.insert(lit![0], weights[0]);
        lits.insert(lit![1], weights[1]);
        lits.insert(lit![2], weights[2]);
        lits.insert(lit![3], weights[3]);
        let mut enc = PBE::from(lits);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut proof = new_proof(0, false);
        let mut cnf = Cnf::new();

        let max_val = weights.iter().sum::<usize>();
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
            println!("bound: {bound}");

            enc.encode_ub_change_cert(bound..bound + 1, &mut cnf, &mut var_manager, &mut proof)
                .unwrap();
            proof.comment(&format!("bound {bound} done")).unwrap();
            solver.add_cnf_ref(&cnf).unwrap();
            cnf.clear();
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

        let proof_file = proof
            .conclude::<Var>(pigeons::OutputGuarantee::None, &pigeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    fn print_file<P: AsRef<Path>>(path: P) {
        println!();
        for line in BufReader::new(File::open(path).expect("could not open file")).lines() {
            println!("{}", line.unwrap());
        }
        println!();
    }

    fn verify_proof<P1: AsRef<Path>, P2: AsRef<Path>>(instance: P1, proof: P2) {
        if let Ok(veripb) = std::env::var("VERIPB_CHECKER") {
            println!("start checking proof");
            let out = Command::new(veripb)
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
    fn dbgte_inc_ub() {
        test_inc_pb_ub::<GeneralizedTotalizer>()
    }

    super::generate_exhaustive!(dbgte, GeneralizedTotalizer);
}
