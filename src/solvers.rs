mod ipasir;

use crate::types::{Lit, Solution, Var};

pub trait Solver {
    fn solve_assumps(&mut self, assumps: Vec<Lit>) -> Option<bool>;
    fn solve(&mut self) -> Option<bool> {
        self.solve_assumps(vec![])
    }
    fn get_solution() -> Option<Solution>;
    fn var_val(&self, var: &Var) -> Option<bool>;
    fn lit_val(&self, lit: &Lit) -> Option<bool> {
        let val = self.var_val(lit.var());
        match val {
            Some(val) => Some(val && lit.is_pos() || !val && lit.is_neg()),
            None => None,
        }
    }
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
    fn get_core(&self) -> Option<Vec<Lit>>;
}

pub trait SolverStats {
    fn get_n_sat_solves(&self) -> u32;
    fn get_n_unsat_solves(&self) -> u32;
    fn get_n_solves(&self) -> u32 {
        self.get_n_sat_solves() + self.get_n_unsat_solves()
    }
    fn get_n_clauses(&self) -> u32;
    fn get_n_vars(&self) -> u32;
    fn get_n_avg_clause_len(&self) -> f32;
    fn get_cpu_solve_time(&self) -> f32;
}

enum SolverState {
    Loading,
    SAT(Solution),
    UNSAT(Vec<Lit>),
    Terminated,
}
