use rustsat::{
    instances::{BasicVarManager, SatInstance},
    solvers::{Solve, SolverResult},
};
use rustsat_minisat::{core, simp};

#[test]
fn core_small_sat() {
    let mut solver = core::Minisat::default();
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/AProVE11-12.cnf").unwrap();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);
}

// Note: this instance seems too hard for minisat to solve
#[test]
#[ignore]
fn core_small_unsat() {
    let mut solver = core::Minisat::default();
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf")
            .unwrap();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Unsat);
}

#[test]
fn simp_small_sat() {
    let mut solver = simp::Minisat::default();
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/AProVE11-12.cnf").unwrap();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);
}

// Note: this instance seems too hard for minisat to solve
#[test]
#[ignore]
fn simp_small_unsat() {
    let mut solver = simp::Minisat::default();
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf")
            .unwrap();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Unsat);
}
