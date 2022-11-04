#![cfg(feature = "compression")]

use rustsat::{
    instances::{BasicVarManager, SatInstance},
    solvers::SolverResult,
    solvers::{self, Solve},
};

#[test]
fn small_sat_instance_gzip() {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/AProVE11-12.cnf.gz").unwrap();
    let mut solver = solvers::new_default_solver();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
fn small_unsat_instance_gzip() {
    let inst: SatInstance<BasicVarManager> = SatInstance::from_dimacs_path(
        "./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf.gz",
    )
    .unwrap();
    let mut solver = solvers::new_default_solver();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::UNSAT);
}

#[test]
fn small_sat_instance_bz2() {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/AProVE11-12.cnf.bz2").unwrap();
    let mut solver = solvers::new_default_solver();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
fn small_unsat_instance_bz2() {
    let inst: SatInstance<BasicVarManager> = SatInstance::from_dimacs_path(
        "./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf.bz2",
    )
    .unwrap();
    let mut solver = solvers::new_default_solver();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::UNSAT);
}
