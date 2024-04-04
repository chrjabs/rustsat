use rustsat::{
    instances::{BasicVarManager, SatInstance},
    solvers::{Solve, SolverResult},
};
use rustsat_kissat::Kissat;

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
fn small_sat() {
    let solver = Kissat::default();
    small_sat_instance(solver);
}

#[test]
fn small_unsat() {
    let solver = Kissat::default();
    small_unsat_instance(solver);
}

#[test]
fn ms_segfault() {
    let solver = Kissat::default();
    ms_segfault_instance(solver);
}

#[test]
fn sat_small_sat() {
    let mut solver = Kissat::default();
    solver
        .set_configuration(rustsat_kissat::Config::SAT)
        .unwrap();
    small_sat_instance(solver);
}

#[test]
fn sat_small_unsat() {
    let mut solver = Kissat::default();
    solver
        .set_configuration(rustsat_kissat::Config::SAT)
        .unwrap();
    small_unsat_instance(solver);
}

#[test]
fn sat_ms_segfault() {
    let mut solver = Kissat::default();
    solver
        .set_configuration(rustsat_kissat::Config::SAT)
        .unwrap();
    ms_segfault_instance(solver);
}

#[test]
fn unsat_small_sat() {
    let mut solver = Kissat::default();
    solver
        .set_configuration(rustsat_kissat::Config::UNSAT)
        .unwrap();
    small_sat_instance(solver);
}

#[test]
fn unsat_small_unsat() {
    let mut solver = Kissat::default();
    solver
        .set_configuration(rustsat_kissat::Config::UNSAT)
        .unwrap();
    small_unsat_instance(solver);
}

#[test]
fn unsat_ms_segfault() {
    let mut solver = Kissat::default();
    solver
        .set_configuration(rustsat_kissat::Config::UNSAT)
        .unwrap();
    ms_segfault_instance(solver);
}
