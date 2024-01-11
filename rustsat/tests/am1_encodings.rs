use rustsat::{
    encodings::am1::{Encode, Pairwise},
    instances::{BasicVarManager, ManageVars},
    lit,
    solvers::{
        Solve, SolveIncremental,
        SolverResult::{Sat, Unsat},
    },
    types::Lit,
    var,
};

use rustsat_tools::{test_all, test_assignment};

fn test_am1<AM1: Encode + From<Vec<Lit>>>() {
    let mut solver = rustsat_minisat::core::Minisat::default();
    let mut var_manager = BasicVarManager::default();
    var_manager.increase_next_free(var![3]);

    let mut enc = AM1::from(vec![lit![0], lit![1], lit![2]]);
    enc.encode(&mut solver, &mut var_manager).unwrap();

    test_all!(
        solver,
        Vec::<Lit>::new(),
        Unsat,
        Unsat,
        Unsat,
        Sat,
        Unsat,
        Sat,
        Sat,
        Sat
    );
}

#[test]
fn pairwise() {
    test_am1::<Pairwise>()
}
