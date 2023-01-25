#![allow(dead_code, unused)]

use rustsat::{
    instances::{BasicVarManager, SatInstance},
    solvers,
    solvers::{Solve, SolverResult},
};

fn small_sat_instance<S: Solve>(mut solver: S) {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/AProVE11-12.cnf").unwrap();
    solver.add_cnf(inst.as_cnf().0);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::SAT);
}

fn small_unsat_instance<S: Solve>(mut solver: S) {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf")
            .unwrap();
    solver.add_cnf(inst.as_cnf().0);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::UNSAT);
}

#[test]
#[cfg(feature = "ipasir")]
fn ipasir_small_sat() {
    let solver = solvers::IpasirSolver::default();
    small_sat_instance(solver);
}

#[test]
#[cfg(feature = "ipasir")]
fn ipasir_small_unsat() {
    let solver = solvers::IpasirSolver::default();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_small_sat() {
    let solver = solvers::CaDiCaL::default();
    small_sat_instance(solver);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_small_unsat() {
    let solver = solvers::CaDiCaL::default();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_sat_small_sat() {
    let mut solver = solvers::CaDiCaL::default();
    solver
        .set_configuration(solvers::cadical::Config::SAT)
        .unwrap();
    small_sat_instance(solver);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_unsat_small_unsat() {
    let mut solver = solvers::CaDiCaL::default();
    solver
        .set_configuration(solvers::cadical::Config::UNSAT)
        .unwrap();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "kissat")]
fn kissat_small_sat() {
    let solver = solvers::Kissat::default();
    small_sat_instance(solver);
}

#[test]
#[cfg(feature = "kissat")]
fn kissat_small_unsat() {
    let solver = solvers::Kissat::default();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "kissat")]
fn kissat_sat_small_sat() {
    let mut solver = solvers::Kissat::default();
    solver
        .set_configuration(solvers::kissat::Config::SAT)
        .unwrap();
    small_sat_instance(solver);
}

#[test]
#[cfg(feature = "kissat")]
fn kissat_unsat_small_unsat() {
    let mut solver = solvers::Kissat::default();
    solver
        .set_configuration(solvers::kissat::Config::UNSAT)
        .unwrap();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "glucose4")]
fn glucosecore4_small_sat() {
    let solver = solvers::GlucoseCore4::default();
    small_sat_instance(solver);
}

// Note: this instance seems too hard for glucose to solve
#[test]
#[ignore]
#[cfg(feature = "glucose4")]
fn glucosecore4_small_unsat() {
    let solver = solvers::GlucoseCore4::default();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "glucose4")]
fn glucosesimp4_small_sat() {
    let solver = solvers::GlucoseSimp4::default();
    small_sat_instance(solver);
}

// Note: this instance seems too hard for glucose to solve
#[test]
#[ignore]
#[cfg(feature = "glucose4")]
fn glucosesimp4_small_unsat() {
    let solver = solvers::GlucoseSimp4::default();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "minisat")]
fn minisatcore_small_sat() {
    let solver = solvers::MinisatCore::default();
    small_sat_instance(solver);
}

// Note: this instance seems too hard for minisat to solve
#[test]
#[ignore]
#[cfg(feature = "minisat")]
fn minisatcore_small_unsat() {
    let solver = solvers::MinisatCore::default();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "minisat")]
fn minisatsimp_small_sat() {
    let solver = solvers::MinisatSimp::default();
    small_sat_instance(solver);
}

// Note: this instance seems too hard for minisat to solve
#[test]
#[ignore]
#[cfg(feature = "minisat")]
fn minisatsimp_small_unsat() {
    let solver = solvers::MinisatSimp::default();
    small_unsat_instance(solver);
}