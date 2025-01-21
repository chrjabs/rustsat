//! # rustsat-batsat - Interface to the BatSat SAT Solver for RustSAT
//!
//! Interface to the [BatSat](https://github.com/c-cube/batsat) incremental SAT-Solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! BatSat is fully implemented in Rust which has advantages in restricted compilation scenarios like WebAssembly.
//!
//! # BatSat Version
//!
//! The version of BatSat in this crate is Version 0.6.0.

#![warn(clippy::pedantic)]
#![warn(missing_docs)]

use std::time::Duration;

use batsat::{intmap::AsIndex, lbool, Callbacks, SolverInterface};
use cpu_time::ProcessTime;
use rustsat::{
    solvers::{Solve, SolveIncremental, SolveStats, SolverResult, SolverStats},
    types::{Cl, Clause, Lit, TernaryVal, Var},
};

/// RustSAT wrapper for [`batsat::BasicSolver`]
pub type BasicSolver = Solver<batsat::BasicCallbacks>;

/// RustSAT wrapper for a [`batsat::Solver`] Solver from BatSat
#[derive(Default)]
pub struct Solver<Cb: Callbacks> {
    internal: batsat::Solver<Cb>,
    n_sat: usize,
    n_unsat: usize,
    n_terminated: usize,
    avg_clause_len: f32,
    cpu_time: Duration,
}

impl<Cb: Callbacks> Solver<Cb> {
    /// Gets a reference to the internal [`BasicSolver`]
    #[must_use]
    pub fn batsat_ref(&self) -> &batsat::Solver<Cb> {
        &self.internal
    }

    /// Gets a mutable reference to the internal [`BasicSolver`]
    #[must_use]
    pub fn batsat_mut(&mut self) -> &mut batsat::Solver<Cb> {
        &mut self.internal
    }

    #[allow(clippy::cast_precision_loss)]
    #[inline]
    fn update_avg_clause_len(&mut self, clause: &Cl) {
        self.avg_clause_len = (self.avg_clause_len * ((self.n_clauses()) as f32)
            + clause.len() as f32)
            / (self.n_clauses() + 1) as f32;
    }

    fn solve_track_stats(&mut self, assumps: &[Lit]) -> SolverResult {
        let a = assumps
            .iter()
            .map(|l| batsat::Lit::new(self.internal.var_of_int(l.vidx32() + 1), l.is_pos()))
            .collect::<Vec<_>>();

        let start = ProcessTime::now();
        let ret = match self.internal.solve_limited(&a) {
            x if x == lbool::TRUE => {
                self.n_sat += 1;
                SolverResult::Sat
            }
            x if x == lbool::FALSE => {
                self.n_unsat += 1;
                SolverResult::Unsat
            }
            x if x == lbool::UNDEF => {
                self.n_terminated += 1;
                SolverResult::Interrupted
            }
            _ => unreachable!(),
        };
        self.cpu_time += start.elapsed();
        ret
    }
}

impl<Cb: Callbacks> Extend<Clause> for Solver<Cb> {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"));
    }
}

impl<'a, C, Cb> Extend<&'a C> for Solver<Cb>
where
    C: AsRef<Cl> + ?Sized,
    Cb: Callbacks,
{
    fn extend<T: IntoIterator<Item = &'a C>>(&mut self, iter: T) {
        iter.into_iter().for_each(|cl| {
            self.add_clause_ref(cl)
                .expect("Error adding clause in extend");
        });
    }
}

impl<Cb: Callbacks> Solve for Solver<Cb> {
    fn signature(&self) -> &'static str {
        "BatSat 0.6.0"
    }

    fn solve(&mut self) -> anyhow::Result<SolverResult> {
        Ok(self.solve_track_stats(&[]))
    }

    fn lit_val(&self, lit: Lit) -> anyhow::Result<TernaryVal> {
        let l = batsat::Lit::new(batsat::Var::from_index(lit.vidx() + 1), lit.is_pos());

        match self.internal.value_lit(l) {
            x if x == lbool::TRUE => Ok(TernaryVal::True),
            x if x == lbool::FALSE => Ok(TernaryVal::False),
            x if x == lbool::UNDEF => Ok(TernaryVal::DontCare),
            _ => unreachable!(),
        }
    }

    fn add_clause_ref<C>(&mut self, clause: &C) -> anyhow::Result<()>
    where
        C: AsRef<Cl> + ?Sized,
    {
        let clause = clause.as_ref();
        self.update_avg_clause_len(clause);

        let mut c: Vec<_> = clause
            .iter()
            .map(|l| batsat::Lit::new(self.internal.var_of_int(l.vidx32() + 1), l.is_pos()))
            .collect();

        self.internal.add_clause_reuse(&mut c);

        Ok(())
    }
}

impl<Cb: Callbacks> SolveIncremental for Solver<Cb> {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult> {
        Ok(self.solve_track_stats(assumps))
    }

    fn core(&mut self) -> anyhow::Result<Vec<Lit>> {
        Ok(self
            .internal
            .unsat_core()
            .iter()
            .map(|l| Lit::new(l.var().idx() - 1, !l.sign()))
            .collect::<Vec<_>>())
    }
}

impl<Cb: Callbacks> SolveStats for Solver<Cb> {
    fn stats(&self) -> SolverStats {
        SolverStats {
            n_sat: self.n_sat,
            n_unsat: self.n_unsat,
            n_terminated: self.n_terminated,
            n_clauses: self.n_clauses(),
            max_var: self.max_var(),
            avg_clause_len: self.avg_clause_len,
            cpu_solve_time: self.cpu_time,
        }
    }

    fn n_sat_solves(&self) -> usize {
        self.n_sat
    }

    fn n_unsat_solves(&self) -> usize {
        self.n_unsat
    }

    fn n_terminated(&self) -> usize {
        self.n_terminated
    }

    fn n_clauses(&self) -> usize {
        usize::try_from(self.internal.num_clauses()).expect("more than `usize::MAX` clauses")
    }

    fn max_var(&self) -> Option<Var> {
        let num = self.internal.num_vars();
        if num > 0 {
            // BatSat returns a value that is off by one
            Some(Var::new(num - 2))
        } else {
            None
        }
    }

    fn avg_clause_len(&self) -> f32 {
        self.avg_clause_len
    }

    fn cpu_solve_time(&self) -> Duration {
        self.cpu_time
    }
}

#[cfg(test)]
mod test {
    rustsat_solvertests::basic_unittests!(super::BasicSolver, false);
}
