mod ffi;

use super::{Solver, SolverState, SolverStats};
use ffi::IpasirHandle;

pub struct IpasirSolver {
    handle: *mut IpasirHandle,
    state: SolverState,
    n_sat: u32,
    n_unsat: u32,
    n_clauses: u32,
    n_vars: u32,
    avg_clause_len: f32,
    cpu_solve_time: f32,
}

impl IpasirSolver {
    pub fn new() -> IpasirSolver {
        IpasirSolver {
            handle: unsafe { ffi::ipasir_init() },
            state: SolverState::Loading,
            n_sat: 0,
            n_unsat: 0,
            n_clauses: 0,
            n_vars: 0,
            avg_clause_len: 0.0,
            cpu_solve_time: 0.0,
        }
    }
}

impl Solver for IpasirSolver {
    fn solve_assumps(&mut self, assumps: Vec<crate::types::Lit>) -> Option<bool> {
        todo!()
    }

    fn get_solution() -> Option<crate::types::Solution> {
        todo!()
    }

    fn var_val(&self, var: &crate::types::Var) -> Option<bool> {
        todo!()
    }

    fn add_clause(&mut self, clause: Vec<crate::types::Lit>) {
        todo!()
    }

    fn get_core(&self) -> Option<Vec<crate::types::Lit>> {
        todo!()
    }
}

impl SolverStats for IpasirSolver {
    fn get_n_sat_solves(&self) -> u32 {
        self.n_sat
    }

    fn get_n_unsat_solves(&self) -> u32 {
        self.n_unsat
    }

    fn get_n_clauses(&self) -> u32 {
        self.n_clauses
    }

    fn get_n_vars(&self) -> u32 {
        self.n_vars
    }

    fn get_avg_clause_len(&self) -> f32 {
        self.avg_clause_len
    }

    fn get_cpu_solve_time(&self) -> f32 {
        self.cpu_solve_time
    }
}
