//! # Enumerator
//!
//! A small tool that enumerates all solutions of a DIMACS CNF file.
//!
//! Useage: enumerator [dimacs cnf file]

use rustsat::{
    instances::{ManageVars, SatInstance},
    solvers::{self, IncrementalSolve, Solve},
    types::{Assignment, Var},
};

struct Enumerator<S: IncrementalSolve> {
    solver: S,
    max_var: Var,
}

impl<S: IncrementalSolve> Iterator for Enumerator<S> {
    type Item = Assignment;

    fn next(&mut self) -> Option<Self::Item> {
        match self.solver.solve().expect("error while solving") {
            solvers::SolverResult::SAT => {
                let sol = self
                    .solver
                    .solution(self.max_var)
                    .expect("could not get solution from solver");
                // Add blocking clause to solver
                let bl_cl = sol.clone().into_iter().map(|l| !l).collect();
                self.solver
                    .add_clause(bl_cl)
                    .expect("error adding blocking clause to solver");
                Some(sol)
            }
            solvers::SolverResult::UNSAT => None,
            solvers::SolverResult::Interrupted => panic!("solver interrupted without limits"),
        }
    }
}

fn main() {
    let in_path = std::env::args().nth(1).expect("no input file given");

    let inst: SatInstance =
        SatInstance::from_dimacs_path(in_path).expect("error parsing the input file");
    let (cnf, vm) = inst.as_cnf();

    let mut solver = solvers::new_default_inc_solver();
    solver
        .reserve(vm.max_var().expect("no variables in instance"))
        .expect("error reserving memory in solver");
    solver.add_cnf(cnf).expect("error adding cnf to solver");

    let enumerator = Enumerator {
        solver,
        max_var: vm.max_var().unwrap(),
    };

    enumerator.for_each(|sol| println!("s {}", sol))
}
