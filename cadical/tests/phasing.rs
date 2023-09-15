use rustsat::{
    instances::{BasicVarManager, SatInstance},
    lit,
    solvers::{PhaseLit, Solve, SolverResult},
    types::TernaryVal,
    var,
};
use rustsat_cadical::CaDiCaL;

fn test_phase_saving<S: Solve + PhaseLit>(mut solver: S) {
    let inst: SatInstance<BasicVarManager> =
        SatInstance::from_dimacs_path("./data/small.cnf").unwrap();
    solver.add_cnf(inst.as_cnf().0).unwrap();
    solver.phase_lit(lit![0]).unwrap();
    solver.phase_lit(!lit![1]).unwrap();
    solver.phase_lit(lit![2]).unwrap();
    solver.phase_lit(!lit![3]).unwrap();
    let res = solver.solve().unwrap();
    assert_eq!(res, SolverResult::Sat);
    let sol = solver.solution(var![3]).unwrap();
    assert_eq!(sol.lit_value(lit![0]), TernaryVal::True);
    assert_eq!(sol.lit_value(lit![1]), TernaryVal::False);
    assert_eq!(sol.lit_value(lit![2]), TernaryVal::True);
    assert_eq!(sol.lit_value(lit![3]), TernaryVal::False);
    solver.unphase_var(var![1]).unwrap();
    solver.unphase_var(var![0]).unwrap();
}

#[test]
fn phase_saving() {
    let mut solver = CaDiCaL::default();
    solver.set_option("lucky", 0).unwrap();
    test_phase_saving(solver);
}
