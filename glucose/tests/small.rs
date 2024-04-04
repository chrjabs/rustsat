use rustsat::{
    instances::{BasicVarManager, SatInstance},
    solvers::{Solve, SolverResult},
};
use rustsat_glucose::{core, simp};

fn small_sat_instance<S: Solve>(mut solver: S) {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/AProVE11-12.cnf").unwrap();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);
}

fn small_unsat_instance<S: Solve>(mut solver: S) {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf")
            .unwrap();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Unsat);
}

fn ms_segfault_instance<S: Solve>(mut solver: S) {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/minisat-segfault.cnf").unwrap();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Unsat);
}

#[test]
fn core_small_sat() {
    let solver = core::Glucose::default();
    small_sat_instance(solver);
}

// Note: this instance seems too hard for glucose to solve
#[test]
#[ignore]
fn core_small_unsat() {
    let solver = core::Glucose::default();
    small_unsat_instance(solver);
}

#[test]
fn core_ms_segfault() {
    let solver = core::Glucose::default();
    ms_segfault_instance(solver);
}

#[test]
fn simp_small_sat() {
    let solver = simp::Glucose::default();
    small_sat_instance(solver);
}

// Note: this instance seems too hard for glucose to solve
#[test]
#[ignore]
fn simp_small_unsat() {
    let solver = simp::Glucose::default();
    small_unsat_instance(solver);
}

#[test]
fn simp_ms_segfault() {
    let solver = simp::Glucose::default();
    ms_segfault_instance(solver);
}
