//! # BatSat Solver Interface
//!
//! Interface to the [BatSat](https://github.com/c-cube/batsat) incremental SAT-Solver

use batsat::{intmap::AsIndex, lbool, BasicSolver, SolverInterface};
use rustsat::{
    solvers::{Solve, SolveIncremental, SolverResult},
    types::{Clause, Lit, TernaryVal},
};
use thiserror::Error;

#[derive(Error, Clone, Copy, PartialEq, Eq, Debug)]
#[error("BatSat returned an invalid value: {error}")]
pub struct InvalidApiReturn {
    error: &'static str,
}

pub struct BatsatBasicSolver(BasicSolver);

impl Default for BatsatBasicSolver {
    fn default() -> BatsatBasicSolver {
        BatsatBasicSolver(BasicSolver::default())
    }
}

impl Extend<Clause> for BatsatBasicSolver {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"))
    }
}

impl Solve for BatsatBasicSolver {
    fn signature(&self) -> &'static str {
        "BatSat 0.5.0"
    }

    fn solve(&mut self) -> anyhow::Result<SolverResult> {
        match self.0.solve_limited(&[]) {
            x if x == lbool::TRUE => Ok(SolverResult::Sat),
            x if x == lbool::FALSE => Ok(SolverResult::Unsat),
            x if x == lbool::UNDEF => Err(InvalidApiReturn {
                error: "BatSat Solver is in an UNSAT state".into(),
            }
            .into()),
            _ => unreachable!(),
        }
    }

    fn lit_val(&self, lit: Lit) -> anyhow::Result<TernaryVal> {
        let l = batsat::Lit::new(batsat::Var::from_index(lit.vidx() + 1), lit.is_pos());

        match self.0.value_lit(l) {
            x if x == lbool::TRUE => Ok(TernaryVal::True),
            x if x == lbool::FALSE => Ok(TernaryVal::False),
            x if x == lbool::UNDEF => Ok(TernaryVal::DontCare),
            _ => unreachable!(),
        }
    }

    fn add_clause(&mut self, clause: Clause) -> anyhow::Result<()> {
        let mut c: Vec<batsat::Lit> = clause
            .iter()
            .map(|l| batsat::Lit::new(self.0.var_of_int(l.vidx32() + 1), l.is_pos()))
            .collect::<Vec<batsat::Lit>>();

        self.0.add_clause_reuse(&mut c);

        Ok(())
    }
}

impl SolveIncremental for BatsatBasicSolver {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult> {
        let a = assumps
            .iter()
            .map(|l| {
                batsat::Lit::new(
                    self.0.var_of_int((l.vidx32() + 1).try_into().unwrap()),
                    l.is_pos(),
                )
            })
            .collect::<Vec<_>>();

        match self.0.solve_limited(&a) {
            x if x == lbool::TRUE => Ok(SolverResult::Sat),
            x if x == lbool::FALSE => Ok(SolverResult::Unsat),
            x if x == lbool::UNDEF => Err(InvalidApiReturn {
                error: "BatSat Solver is in an UNSAT state".into(),
            }
            .into()),
            _ => unreachable!(),
        }
    }

    fn core(&mut self) -> anyhow::Result<Vec<Lit>> {
        Ok(self
            .0
            .unsat_core()
            .iter()
            .map(|l| Lit::new(l.var().idx() - 1, !l.sign()))
            .collect::<Vec<_>>())
    }
}
