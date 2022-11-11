use rustsat::{
    instances::SatInstance,
    lit, solvers,
    solvers::SolverResult,
    types::{constraints::PBConstraint, Lit, RsHashMap},
};

#[cfg(feature = "multiopt")]
use rustsat::instances::MultiOptInstance;
#[cfg(feature = "optimization")]
use rustsat::instances::{Objective, OptInstance};

macro_rules! opb_test {
    ($path:expr, $expect:expr) => {{
        let inst: SatInstance = SatInstance::from_opb_path($path).unwrap();
        let (cnf, _) = inst.as_cnf();
        println!("{:?}", cnf);
        let mut solver = solvers::new_default_solver();
        solver.add_cnf(cnf);
        assert_eq!(solver.solve().unwrap(), $expect);
    }};
}

#[test]
fn opb_tiny_sat() {
    opb_test!("./data/tiny-sat.opb", SolverResult::SAT);
}

#[test]
fn opb_tiny_unsat() {
    opb_test!("./data/tiny-unsat.opb", SolverResult::UNSAT);
}

#[cfg(feature = "optimization")]
#[test]
fn opb_opt() {
    let inst: OptInstance = OptInstance::from_opb_path("./data/tiny-opt.opb").unwrap();
    let mut true_constr = SatInstance::new();
    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 5);
    lits.insert(lit![1], -3);
    true_constr.add_pb_constr(PBConstraint::new_lb(lits, 4));
    let mut lits = RsHashMap::default();
    lits.insert(lit![2], 5);
    lits.insert(lit![3], -3);
    true_constr.add_pb_constr(PBConstraint::new_lb(lits, 2));
    let mut lits = RsHashMap::default();
    lits.insert(!lit![3], 5);
    true_constr.add_pb_constr(PBConstraint::new_lb(lits, 4));
    let mut true_obj = Objective::new();
    true_obj.increase_soft_lit_int(1, lit![0]);
    true_obj.increase_soft_lit_int(2, lit![1]);
    assert_eq!(inst, OptInstance::compose(true_constr, true_obj));
}

#[cfg(feature = "multiopt")]
#[test]
fn opb_multi_opt() {
    let inst: MultiOptInstance =
        MultiOptInstance::from_opb_path("./data/tiny-opt.opb").unwrap();
    let mut true_constr = SatInstance::new();
    let mut lits = RsHashMap::default();
    lits.insert(lit![0], 5);
    lits.insert(lit![1], -3);
    true_constr.add_pb_constr(PBConstraint::new_lb(lits, 4));
    let mut lits = RsHashMap::default();
    lits.insert(lit![2], 5);
    lits.insert(lit![3], -3);
    true_constr.add_pb_constr(PBConstraint::new_lb(lits, 2));
    let mut lits = RsHashMap::default();
    lits.insert(!lit![3], 5);
    true_constr.add_pb_constr(PBConstraint::new_lb(lits, 4));
    let mut true_obj_1 = Objective::new();
    true_obj_1.increase_soft_lit_int(1, lit![0]);
    true_obj_1.increase_soft_lit_int(2, lit![1]);
    let mut true_obj_2 = Objective::new();
    true_obj_2.increase_soft_lit_int(2, lit![2]);
    true_obj_2.increase_soft_lit_int(-3, !lit![3]);
    assert_eq!(
        inst,
        MultiOptInstance::compose(true_constr, vec![true_obj_1, true_obj_2])
    );
}
