//! # Enumerator
//!
//! A small tool that enumerates all solutions of a DIMACS CNF file.
//!
//! Usage: enumerator [dimacs cnf file]

use anyhow::Context;
use rustsat::{
    instances::{ManageVars, SatInstance},
    solvers::{self, Solve, SolveIncremental},
    types::{Assignment, Var},
};

macro_rules! print_usage {
    () => {{
        eprintln!("Usage: enumerator [dimacs cnf file]");
        panic!()
    }};
}

struct Enumerator<S: SolveIncremental> {
    solver: S,
    max_var: Var,
}

impl<S: SolveIncremental> Iterator for Enumerator<S> {
    type Item = Assignment;

    fn next(&mut self) -> Option<Self::Item> {
        match self.solver.solve().expect("error while solving") {
            solvers::SolverResult::Sat => {
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
            solvers::SolverResult::Unsat => None,
            solvers::SolverResult::Interrupted => panic!("solver interrupted without limits"),
        }
    }
}

fn main() -> anyhow::Result<()> {
    let in_path = std::env::args().nth(1).unwrap_or_else(|| print_usage!());

    let inst: SatInstance =
        SatInstance::from_dimacs_path(in_path).context("error parsing the input file")?;
    let (cnf, vm) = inst.into_cnf();

    let mut solver = rustsat_tools::Solver::default();
    solver
        .reserve(vm.max_var().expect("no variables in instance"))
        .context("error reserving memory in solver")?;
    solver.add_cnf(cnf).expect("error adding cnf to solver");

    let enumerator = Enumerator {
        solver,
        max_var: vm.max_var().unwrap(),
    };

    enumerator.for_each(|sol| println!("s {}", sol));
    Ok(())
}
