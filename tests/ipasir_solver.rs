use rustsat::{
    instances::SatInstance,
    solvers::{ipasir::IpasirSolver, Solver, SolverResult},
};
use std::path::Path;

#[test]
fn small_sat_instance() {
    let inst = SatInstance::from_dimacs_path(Path::new("./data/AProVE11-12.cnf")).unwrap();
    let mut solver = IpasirSolver::new();
    inst.add_to_solver(&mut solver);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
fn small_unsat_instance() {
    let inst = SatInstance::from_dimacs_path(Path::new(
        "./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf",
    ))
    .unwrap();
    let mut solver = IpasirSolver::new();
    inst.add_to_solver(&mut solver);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::UNSAT);
}

#[test]
#[cfg(feature = "compression")]
fn small_sat_instance_gzip() {
    let inst = SatInstance::from_dimacs_path(Path::new("./data/AProVE11-12.cnf.gz")).unwrap();
    let mut solver = IpasirSolver::new();
    inst.add_to_solver(&mut solver);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
#[cfg(feature = "compression")]
fn small_unsat_instance_gzip() {
    let inst = SatInstance::from_dimacs_path(Path::new(
        "./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf.gz",
    ))
    .unwrap();
    let mut solver = IpasirSolver::new();
    inst.add_to_solver(&mut solver);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::UNSAT);
}

#[test]
#[cfg(feature = "compression")]
fn small_sat_instance_bz2() {
    let inst = SatInstance::from_dimacs_path(Path::new("./data/AProVE11-12.cnf.bz2")).unwrap();
    let mut solver = IpasirSolver::new();
    inst.add_to_solver(&mut solver);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);
}

#[test]
#[cfg(feature = "compression")]
fn small_unsat_instance_bz2() {
    let inst = SatInstance::from_dimacs_path(Path::new(
        "./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf.bz2",
    ))
    .unwrap();
    let mut solver = IpasirSolver::new();
    inst.add_to_solver(&mut solver);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::UNSAT);
}
