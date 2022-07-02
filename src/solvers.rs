pub mod ipasir;

use crate::types::{Error, Lit, LitVal, Solution, Var};

pub trait Solver {
    fn solve_assumps(&mut self, assumps: Vec<Lit>) -> Result<SolverResult, Error>;
    fn solve(&mut self) -> Result<SolverResult, Error> {
        self.solve_assumps(vec![])
    }
    fn get_solution(&self, high_var: &Var) -> Result<Solution, Error> {
        let mut assignment = Vec::new();
        let len = high_var.index() + 1;
        assignment.reserve(len);
        for idx in 0..len {
            let lit = Lit::new(idx, false);
            assignment.push(self.lit_val(&lit)?);
        }
        Ok(Solution::from_vec(assignment))
    }
    fn var_val(&self, var: &Var) -> Result<LitVal, Error> {
        self.lit_val(&var.pos_lit())
    }
    fn lit_val(&self, lit: &Lit) -> Result<LitVal, Error>;
    fn add_clause(&mut self, clause: Vec<Lit>);
    fn add_unit(&mut self, lit: Lit) {
        self.add_clause(vec![lit])
    }
    fn add_pair(&mut self, lit1: Lit, lit2: Lit) {
        self.add_clause(vec![lit1, lit2])
    }
    fn add_ternary(&mut self, lit1: Lit, lit2: Lit, lit3: Lit) {
        self.add_clause(vec![lit1, lit2, lit3])
    }
    fn get_core(&mut self) -> Option<Vec<Lit>>;
}

pub trait SolverStats {
    fn get_n_sat_solves(&self) -> u32;
    fn get_n_unsat_solves(&self) -> u32;
    fn get_n_terminated(&self) -> u32;
    fn get_n_solves(&self) -> u32 {
        self.get_n_sat_solves() + self.get_n_unsat_solves() + self.get_n_terminated()
    }
    fn get_n_clauses(&self) -> u32;
    fn get_n_vars(&self) -> u32;
    fn get_avg_clause_len(&self) -> f32;
    fn get_cpu_solve_time(&self) -> f32;
}

enum InternalSolverState {
    Loading,
    SAT,
    UNSAT(Vec<Lit>),
    Terminated,
}

impl InternalSolverState {
    fn to_external(&self) -> SolverState {
        match self {
            InternalSolverState::Loading => SolverState::Loading,
            InternalSolverState::SAT => SolverState::SAT,
            InternalSolverState::UNSAT(_) => SolverState::UNSAT,
            InternalSolverState::Terminated => SolverState::Terminated,
        }
    }
}

pub enum SolverState {
    Loading,
    SAT,
    UNSAT,
    Terminated,
}

pub enum SolverResult {
    SAT,
    UNSAT,
    Interrupted,
}
