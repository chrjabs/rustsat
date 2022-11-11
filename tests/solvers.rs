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
    let solver = solvers::IpasirSolver::new();
    small_sat_instance(solver);
}

#[test]
#[cfg(feature = "ipasir")]
fn ipasir_small_unsat() {
    let solver = solvers::IpasirSolver::new();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_small_sat() {
    let solver = solvers::CaDiCaL::new();
    small_sat_instance(solver);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_small_unsat() {
    let solver = solvers::CaDiCaL::new();
    small_unsat_instance(solver);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_sat_small_sat() {
    let mut solver = solvers::CaDiCaL::new();
    solver
        .set_configuration(solvers::cadical::Config::SAT)
        .unwrap();
    small_sat_instance(solver);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_unsat_small_unsat() {
    let mut solver = solvers::CaDiCaL::new();
    solver
        .set_configuration(solvers::cadical::Config::UNSAT)
        .unwrap();
    small_unsat_instance(solver);
}
