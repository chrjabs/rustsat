use rustsat::encodings::am1;
use rustsat::encodings::EncodeStats;
use rustsat::encodings::IterInputs;
use rustsat::instances::BasicVarManager;
use rustsat::instances::Cnf;
use rustsat::instances::ManageVars;
use rustsat::lit;
use rustsat::solvers::Solve;
use rustsat::solvers::SolveIncremental;
use rustsat::solvers::SolverResult;
use rustsat::types::Lit;
use rustsat::var;

mod common;
use common::test_all;

macro_rules! gen_tests {
    ($mod:ident, $enc:ty) => {
        mod $mod {
            #[test]
            fn basic() {
                super::test_am1::<$enc>();
            }
            #[test]
            fn duplicate() {
                super::test_am1_duplicate::<$enc>();
            }
            #[test]
            fn negated() {
                super::test_am1_negated::<$enc>();
            }
            #[test]
            fn single_none() {
                super::test_am1_single_none::<$enc>();
            }
            #[test]
            fn stats() {
                super::test_am1_stats::<$enc>();
            }
        }
    };
}

fn test_am1<AM1: am1::Encode + From<Vec<Lit>>>() {
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![3]);

    let mut enc = AM1::from(vec![lit![0], lit![1], lit![2]]);
    let mut cnf = Cnf::new();
    enc.encode(&mut cnf, &mut var_manager).unwrap();
    println!("{cnf:?}");
    solver.add_cnf(cnf).unwrap();

    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Unsat, // 111
        SolverResult::Unsat, // 110
        SolverResult::Unsat, // 101
        SolverResult::Sat,   // 100
        SolverResult::Unsat, // 011
        SolverResult::Sat,   // 010
        SolverResult::Sat,   // 001
        SolverResult::Sat    // 000
    );

    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    let mut enc = AM1::from(vec![lit![0], lit![1], lit![2], lit![3]]);
    let mut cnf = Cnf::new();
    enc.encode(&mut cnf, &mut var_manager).unwrap();
    println!("{cnf:?}");
    solver.add_cnf(cnf).unwrap();

    test_all!(
        solver,
        Vec::<Lit>::new(),
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
}

fn test_am1_duplicate<AM1: am1::Encode + From<Vec<Lit>>>() {
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    let mut enc = AM1::from(vec![lit![0], lit![1], lit![0], lit![2]]);
    let mut cnf = Cnf::new();
    enc.encode(&mut cnf, &mut var_manager).unwrap();
    println!("{cnf:?}");
    solver.add_cnf(cnf).unwrap();

    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Unsat, // 111
        SolverResult::Unsat, // 110
        SolverResult::Unsat, // 101
        SolverResult::Unsat, // 100
        SolverResult::Unsat, // 011
        SolverResult::Sat,   // 010
        SolverResult::Sat,   // 001
        SolverResult::Sat    // 000
    );
}

fn test_am1_negated<AM1: am1::Encode + From<Vec<Lit>>>() {
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![4]);

    let mut enc = AM1::from(vec![lit![0], lit![1], !lit![0], lit![2]]);
    let mut cnf = Cnf::new();
    enc.encode(&mut cnf, &mut var_manager).unwrap();
    println!("{cnf:?}");
    solver.add_cnf(cnf).unwrap();

    test_all!(
        solver,
        Vec::<Lit>::new(),
        SolverResult::Unsat, // 111
        SolverResult::Unsat, // 110
        SolverResult::Unsat, // 101
        SolverResult::Sat,   // 100
        SolverResult::Unsat, // 011
        SolverResult::Unsat, // 010
        SolverResult::Unsat, // 001
        SolverResult::Sat    // 000
    );
}

fn test_am1_single_none<AM1: am1::Encode + From<Vec<Lit>>>() {
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![1]);

    let mut enc = AM1::from(vec![lit![0]]);
    let mut cnf = Cnf::new();
    enc.encode(&mut cnf, &mut var_manager).unwrap();
    println!("{cnf:?}");

    assert!(cnf.is_empty());

    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![0]);

    let mut enc = AM1::from(vec![]);
    let mut cnf = Cnf::new();
    enc.encode(&mut cnf, &mut var_manager).unwrap();
    println!("{cnf:?}");

    assert!(cnf.is_empty());
}

fn test_am1_stats<AM1: am1::Encode + EncodeStats + IterInputs + From<Vec<Lit>>>() {
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![3]);

    let lits = vec![lit![0], lit![1], lit![2]];
    let mut enc = AM1::from(lits.clone());
    let mut cnf = Cnf::new();
    enc.encode(&mut cnf, &mut var_manager).unwrap();

    assert_eq!(enc.n_lits(), 3);

    let inputs: Vec<_> = enc.iter().collect();
    assert_eq!(lits, inputs);

    assert_eq!(enc.n_clauses(), cnf.len());

    assert_eq!(enc.n_vars(), var_manager.n_used() - 3);
}

gen_tests!(pairwise, rustsat::encodings::am1::Pairwise);
gen_tests!(ladder, rustsat::encodings::am1::Ladder);
gen_tests!(bitwise, rustsat::encodings::am1::Bitwise);
gen_tests!(commander, rustsat::encodings::am1::Commander);
gen_tests!(bimander, rustsat::encodings::am1::Bimander);
gen_tests!(twoproduct, rustsat::encodings::am1::TwoProduct);
