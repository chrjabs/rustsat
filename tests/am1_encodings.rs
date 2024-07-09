use rustsat::{
    encodings::am1,
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

#[test]
fn pairwise() {
    test_am1::<am1::Pairwise>();
}

#[test]
fn ladder() {
    test_am1::<am1::Ladder>();
}

#[test]
fn bitwise() {
    test_am1::<am1::Bitwise>();
}

#[test]
fn commander() {
    test_am1::<am1::Commander<2>>();
}

#[test]
fn bimander() {
    test_am1::<am1::Bimander<2>>();
}
