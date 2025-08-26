//! # Solver Simulators
//!
//! This module contains generic code to simulate features that solvers might not support.

use crate::{
    instances::Cnf,
    types::{Cl, Clause, Lit},
    utils::Timer,
};

use super::Solve;

#[derive(Debug, PartialEq, Eq, Default)]
enum InternalSolverState {
    #[default]
    Init,
    Sat,
    Unsat(Vec<Lit>),
    Unknown,
}

impl InternalSolverState {
    fn to_external(&self) -> super::SolverState {
        match self {
            InternalSolverState::Init | InternalSolverState::Unknown => super::SolverState::Input,
            InternalSolverState::Sat => super::SolverState::Sat,
            InternalSolverState::Unsat(_) => super::SolverState::Unsat,
        }
    }
}

/// Simulates an incremental solver based on a non-incremental one
///
/// This simply stores the added clauses internally, and re-initializes a new solver whenever solve
/// has been called. Assumptions are also added as unit clauses and the returned core will always
/// be the entire set of assumptions.
///
/// # Generics
///
/// - `S`: the wrapped [`Solve`] type
/// - `Init`: an initializer for `S`, implementing [`super::Initialize`]
#[derive(Debug)]
pub struct Incremental<S, Init = super::DefaultInitializer> {
    solver: S,
    init: std::marker::PhantomData<Init>,
    state: InternalSolverState,
    clauses: Cnf,
    stats: super::SolverStats,
}

impl<S, Init> Default for Incremental<S, Init>
where
    Init: super::Initialize<S>,
{
    fn default() -> Self {
        Self {
            solver: Init::init(),
            init: std::marker::PhantomData,
            state: InternalSolverState::default(),
            clauses: Cnf::default(),
            stats: super::SolverStats::default(),
        }
    }
}

impl<S, Init> Incremental<S, Init> {
    #[allow(clippy::cast_precision_loss)]
    #[inline]
    fn update_avg_clause_len(&mut self, clause: &Cl) {
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
    }

    #[inline]
    fn update_max_var(&mut self, clause: &Cl) {
        if self.stats.max_var.is_none() {
            self.stats.max_var = Some(crate::types::Var::new(0));
        }
        let max_var = self.stats.max_var.as_mut().unwrap();
        for lit in clause {
            *max_var = std::cmp::max(*max_var, lit.var());
        }
    }
}

impl<S, Init> super::Solve for Incremental<S, Init>
where
    S: super::Solve,
    Init: super::Initialize<S>,
{
    fn signature(&self) -> &'static str {
        self.solver.signature()
    }

    fn solve(&mut self) -> anyhow::Result<super::SolverResult> {
        let start = Timer::now();
        if !matches!(self.state, InternalSolverState::Init) {
            self.solver = Init::init();
            self.solver.add_cnf_ref(&self.clauses)?;
        }
        let res = self.solver.solve()?;
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            super::SolverResult::Sat => {
                self.stats.n_sat += 1;
                self.state = InternalSolverState::Sat;
            }
            super::SolverResult::Unsat => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Unsat(vec![]);
            }
            super::SolverResult::Interrupted => {
                self.stats.n_terminated += 1;
                self.state = InternalSolverState::Unknown;
            }
        }
        Ok(res)
    }

    fn lit_val(&self, lit: Lit) -> anyhow::Result<crate::types::TernaryVal> {
        self.solver.lit_val(lit)
    }

    fn var_val(&self, var: crate::types::Var) -> anyhow::Result<crate::types::TernaryVal> {
        self.solver.var_val(var)
    }

    fn add_clause_ref<C>(&mut self, clause: &C) -> anyhow::Result<()>
    where
        C: AsRef<crate::types::Cl> + ?Sized,
    {
        self.stats.n_clauses += 1;
        self.update_avg_clause_len(clause.as_ref());
        self.update_max_var(clause.as_ref());
        if matches!(self.state, InternalSolverState::Init) {
            self.solver.add_clause_ref(clause)?;
        }
        self.clauses
            .add_clause(clause.as_ref().iter().copied().collect());
        Ok(())
    }

    fn add_clause(&mut self, clause: Clause) -> anyhow::Result<()> {
        self.stats.n_clauses += 1;
        self.update_avg_clause_len(&clause);
        self.update_max_var(&clause);
        if matches!(self.state, InternalSolverState::Init) {
            self.solver.add_clause_ref(&clause)?;
        }
        self.clauses.add_clause(clause);
        Ok(())
    }

    fn solution(&self, high_var: crate::types::Var) -> anyhow::Result<crate::types::Assignment> {
        self.solver.solution(high_var)
    }
}

impl<S, Init> super::SolveStats for Incremental<S, Init> {
    fn stats(&self) -> super::SolverStats {
        self.stats.clone()
    }
}

impl<S, Init> super::SolveIncremental for Incremental<S, Init>
where
    S: super::Solve,
    Init: super::Initialize<S>,
{
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<super::SolverResult> {
        let start = Timer::now();
        if !matches!(self.state, InternalSolverState::Init) {
            self.solver = Init::init();
            self.solver.add_cnf_ref(&self.clauses)?;
        }
        for lit in assumps {
            self.solver.add_unit(*lit)?;
        }
        let res = self.solver.solve()?;
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            super::SolverResult::Sat => {
                self.stats.n_sat += 1;
                self.state = InternalSolverState::Sat;
            }
            super::SolverResult::Unsat => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Unsat(assumps.iter().map(|l| !*l).collect());
            }
            super::SolverResult::Interrupted => {
                self.stats.n_terminated += 1;
                self.state = InternalSolverState::Unknown;
            }
        }
        Ok(res)
    }

    fn core(&mut self) -> anyhow::Result<Vec<Lit>> {
        match &self.state {
            InternalSolverState::Unsat(core) => Ok(core.clone()),
            other => Err(super::StateError {
                required_state: super::SolverState::Unsat,
                actual_state: other.to_external(),
            }
            .into()),
        }
    }
}

impl<S, Init> Extend<Clause> for Incremental<S, Init>
where
    S: super::Solve,
    Init: super::Initialize<S>,
{
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"));
    }
}

impl<'a, S, Init, C> Extend<&'a C> for Incremental<S, Init>
where
    S: super::Solve,
    Init: super::Initialize<S>,
    C: AsRef<Cl> + ?Sized,
{
    fn extend<T: IntoIterator<Item = &'a C>>(&mut self, iter: T) {
        iter.into_iter().for_each(|cl| {
            self.add_clause_ref(cl)
                .expect("Error adding clause in extend");
        });
    }
}
