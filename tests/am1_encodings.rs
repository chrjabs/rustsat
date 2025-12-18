use rustsat::{
    encodings::{am1, EncodeStats, IterInputs},
    instances::{BasicVarManager, Cnf, ManageVars},
    lit,
    solvers::{
        Solve, SolveIncremental,
        SolverResult::{Sat, Unsat},
    },
    types::Lit,
    var,
};

use rustsat_tools::{test_all, test_assignment};

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
        Unsat, // 111
        Unsat, // 110
        Unsat, // 101
        Sat,   // 100
        Unsat, // 011
        Sat,   // 010
        Sat,   // 001
        Sat    // 000
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
        Unsat, // 1111
        Unsat, // 1110
        Unsat, // 1101
        Unsat, // 1100
        Unsat, // 1011
        Unsat, // 1010
        Unsat, // 1001
        Sat,   // 1000
        Unsat, // 0111
        Unsat, // 0110
        Unsat, // 0101
        Sat,   // 0100
        Unsat, // 0011
        Sat,   // 0010
        Sat,   // 0001
        Sat    // 0000
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
        Unsat, // 111
        Unsat, // 110
        Unsat, // 101
        Unsat, // 100
        Unsat, // 011
        Sat,   // 010
        Sat,   // 001
        Sat    // 000
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
        Unsat, // 111
        Unsat, // 110
        Unsat, // 101
        Sat,   // 100
        Unsat, // 011
        Unsat, // 010
        Unsat, // 001
        Sat    // 000
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
