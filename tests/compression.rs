use rustsat::{
    instances::{BasicVarManager, SatInstance},
    solvers::Solve,
    solvers::SolverResult,
};

#[test]
fn small_sat_instance_gzip() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path(format!("{manifest}/data/AProVE11-12.cnf.gz")).unwrap();
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(inst.into_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);
}

#[test]
#[ignore]
fn small_unsat_instance_gzip() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let inst: SatInstance<BasicVarManager> = SatInstance::from_dimacs_path(format!(
        "{manifest}/data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf.gz"
    ))
    .unwrap();
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(inst.into_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Unsat);
}

#[test]
fn small_sat_instance_bz2() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path(format!("{manifest}/data/AProVE11-12.cnf.bz2")).unwrap();
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(inst.into_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);
}

#[test]
#[ignore]
fn small_unsat_instance_bz2() {
    let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let inst: SatInstance<BasicVarManager> = SatInstance::from_dimacs_path(format!(
        "{manifest}/data/smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.cnf.bz2"
    ))
    .unwrap();
    let mut solver = rustsat_minisat::core::Minisat::default();
    solver.add_cnf(inst.into_cnf().0).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Unsat);
}
