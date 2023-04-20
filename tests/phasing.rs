#![allow(dead_code, unused)]

use rustsat::{
    instances::{BasicVarManager, SatInstance},
    lit, solvers,
    solvers::{PhaseLit, Solve, SolverResult},
    types::{Lit, TernaryVal, Var},
    var,
};

fn phase_saving<S: Solve + PhaseLit>(mut solver: S) {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/small.cnf").unwrap();
    solver.add_cnf(inst.as_cnf().0);
    solver.phase_lit(lit![0]);
    solver.phase_lit(!lit![1]);
    solver.phase_lit(lit![2]);
    solver.phase_lit(!lit![3]);
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);
    let sol = solver.solution(var![3]).unwrap();
    assert_eq!(sol.lit_value(lit![0]), TernaryVal::True);
    assert_eq!(sol.lit_value(lit![1]), TernaryVal::False);
    assert_eq!(sol.lit_value(lit![2]), TernaryVal::True);
    assert_eq!(sol.lit_value(lit![3]), TernaryVal::False);
    solver.unphase_var(var![1]);
    solver.unphase_var(var![0]);
}

#[test]
#[cfg(feature = "cadical")]
fn cadical_phase_saving() {
    let mut solver = solvers::CaDiCaL::default();
    solver.set_option("lucky", 0);
    phase_saving(solver);
}

#[test]
#[cfg(feature = "glucose4")]
fn glucosecore4_phase_saving() {
    let solver = solvers::GlucoseCore4::default();
    phase_saving(solver);
}

#[test]
#[cfg(feature = "glucose4")]
fn glucosesimp4_phase_saving() {
    let solver = solvers::GlucoseSimp4::default();
    phase_saving(solver);
}

#[test]
#[cfg(feature = "minisat")]
fn minisat_phase_saving() {
    let solver = solvers::MinisatCore::default();
    phase_saving(solver);
}

#[test]
#[cfg(feature = "minisat")]
fn minisatsimp_phase_saving() {
    let solver = solvers::MinisatSimp::default();
    phase_saving(solver);
}
