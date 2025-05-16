//! # rustsat-batsat - Interface to the BatSat SAT Solver for RustSAT
//!
//! Interface to the [BatSat](https://github.com/c-cube/batsat) incremental SAT-Solver to be used with the [RustSAT](https://github.com/chrjabs/rustsat) library.
//!
//! BatSat is fully implemented in Rust which has advantages in restricted compilation scenarios like WebAssembly.
//!
//! # BatSat Version
//!
//! The version of BatSat in this crate is Version 0.6.0.
//!
//! ## Minimum Supported Rust Version (MSRV)
//!
//! Currently, the MSRV is 1.76.0, the plan is to always support an MSRV that is at least a year
//! old.
//!
//! Bumps in the MSRV will _not_ be considered breaking changes. If you need a specific MSRV, make
//! sure to pin a precise version of RustSAT.

// NOTE: For some reason, batsat flipped the memory representation of the sign bit in the literal
// representation compared to Minisat and therefore RustSAT
// https://github.com/c-cube/batsat/commit/8563ae6e3a59478a0d414fe647d99ad9b989841f
// For this reason we cannot transmute RustSAT literals to batsat literals and we have to recreate
// the literals through batsat's API

#![warn(clippy::pedantic)]
#![warn(missing_docs)]
#![warn(missing_debug_implementations)]

use std::time::Duration;

use batsat::{intmap::AsIndex, lbool, Callbacks, SolverInterface};
use cpu_time::ProcessTime;
use rustsat::{
    solvers::{
        Solve, SolveIncremental, SolveStats, SolverResult, SolverState, SolverStats, StateError,
    },
    types::{Cl, Clause, Lit, TernaryVal, Var},
};

/// RustSAT wrapper for [`batsat::BasicSolver`]
pub type BasicSolver = Solver<batsat::BasicCallbacks>;

#[derive(Debug, PartialEq, Eq, Default)]
enum InternalSolverState {
    #[default]
    Input,
    Sat,
    Unsat(bool),
}

impl InternalSolverState {
    fn to_external(&self) -> SolverState {
        match self {
            InternalSolverState::Input => SolverState::Input,
            InternalSolverState::Sat => SolverState::Sat,
            InternalSolverState::Unsat(_) => SolverState::Unsat,
        }
    }
}

/// RustSAT wrapper for a [`batsat::Solver`] Solver from BatSat
#[derive(Default)]
pub struct Solver<Cb: Callbacks> {
    internal: batsat::Solver<Cb>,
    state: InternalSolverState,
    n_sat: usize,
    n_unsat: usize,
    n_terminated: usize,
    avg_clause_len: f32,
    cpu_time: Duration,
}

impl<Cb: Callbacks> std::fmt::Debug for Solver<Cb> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Solver")
            .field("internal", &"omitted")
            .field("state", &self.state)
            .field("n_sat", &self.n_sat)
            .field("n_unsat", &self.n_unsat)
            .field("n_terminated", &self.n_terminated)
            .field("avg_clause_len", &self.avg_clause_len)
            .field("cpu_time", &self.cpu_time)
            .finish()
    }
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
        let assumps = assumps
            .iter()
            .map(|l| batsat::Lit::new(self.internal.var_of_int(l.vidx32()), l.is_pos()))
            .collect::<Vec<_>>();

        let start = ProcessTime::now();
        let ret = match self.internal.solve_limited(&assumps) {
            x if x == lbool::TRUE => {
                self.n_sat += 1;
                self.state = InternalSolverState::Sat;
                SolverResult::Sat
            }
            x if x == lbool::FALSE => {
                self.n_unsat += 1;
                self.state = InternalSolverState::Unsat(!assumps.is_empty());
                SolverResult::Unsat
            }
            x if x == lbool::UNDEF => {
                self.n_terminated += 1;
                self.state = InternalSolverState::Input;
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
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        }
        if let InternalSolverState::Unsat(under_assumps) = &self.state {
            if !under_assumps {
                return Ok(SolverResult::Unsat);
            }
        }
        Ok(self.solve_track_stats(&[]))
    }

    fn lit_val(&self, lit: Lit) -> anyhow::Result<TernaryVal> {
        if self.state != InternalSolverState::Sat {
            return Err(StateError {
                required_state: SolverState::Sat,
                actual_state: self.state.to_external(),
            }
            .into());
        }

        let lit = batsat::Lit::new(batsat::Var::from_index(lit.vidx()), lit.is_pos());

        match self.internal.value_lit(lit) {
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

        let mut clause: Vec<_> = clause
            .iter()
            .map(|l| batsat::Lit::new(self.internal.var_of_int(l.vidx32()), l.is_pos()))
            .collect();

        self.internal.add_clause_reuse(&mut clause);

        Ok(())
    }

    fn reserve(&mut self, max_var: Var) -> anyhow::Result<()> {
        while self.internal.num_vars() <= max_var.idx32() {
            self.internal.new_var_default();
        }
        Ok(())
    }
}

impl<Cb: Callbacks> SolveIncremental for Solver<Cb> {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult> {
        Ok(self.solve_track_stats(assumps))
    }

    fn core(&mut self) -> anyhow::Result<Vec<Lit>> {
        match &self.state {
            InternalSolverState::Unsat(under_assumps) => {
                if *under_assumps {
                    Ok(self
                        .internal
                        .unsat_core()
                        .iter()
                        .map(|l| Lit::new(l.var().idx(), !l.sign()))
                        .collect::<Vec<_>>())
                } else {
                    Ok(vec![])
                }
            }
            other => Err(StateError {
                required_state: SolverState::Unsat,
                actual_state: other.to_external(),
            }
            .into()),
        }
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
            Some(Var::new(num - 1))
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
    rustsat_solvertests::basic_unittests!(
        super::BasicSolver,
        "BatSat [major].[minor].[patch]",
        false
    );
}
