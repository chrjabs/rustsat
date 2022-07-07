//! # IPASIR Interface
//!
//! Interface to any SAT solver implementing the
//! [IPASIR API](https://github.com/biotomas/ipasir) for incremental SAT solvers.

mod ffi;

use std::{ffi::CStr, fmt, os::raw::c_int};

use super::{InternalSolverState, Solver, SolverResult, SolverState, SolverStats};
use crate::types::{Error, Lit, TernaryVal, Var};
use ffi::IpasirHandle;

/// Type for an IPASIR solver.
pub struct IpasirSolver {
    handle: *mut IpasirHandle,
    state: InternalSolverState,
    n_sat: u32,
    n_unsat: u32,
    n_terminated: u32,
    n_clauses: u32,
    max_var: Option<Var>,
    avg_clause_len: f32,
    cpu_solve_time: f32,
}

impl IpasirSolver {
    /// Creates a new IPASIR solver.
    pub fn new() -> IpasirSolver {
        IpasirSolver {
            handle: unsafe { ffi::ipasir_init() },
            state: InternalSolverState::Input,
            n_sat: 0,
            n_unsat: 0,
            n_terminated: 0,
            n_clauses: 0,
            max_var: None,
            avg_clause_len: 0.0,
            cpu_solve_time: 0.0,
        }
    }

    /// Get the signature of the linked IPASIR solver.
    pub fn signature(&self) -> &'static str {
        let c_chars = unsafe { ffi::ipasir_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("IPASIR signature returned invalid UTF-8.")
    }

    fn get_core_assumps(&self, assumps: &Vec<Lit>) -> Result<Vec<Lit>, Error> {
        let mut core = Vec::new();
        core.reserve(assumps.len());
        for a in assumps {
            match unsafe { ffi::ipasir_failed(self.handle, a.to_ipasir()) } {
                0 => (),
                1 => core.push(!*a),
                invalid => return Err(Error::Ipasir(IpasirError::Failed(invalid))),
            }
        }
        Ok(core)
    }
}

impl Solver for IpasirSolver {
    fn solve_assumps(&mut self, assumps: Vec<Lit>) -> Result<SolverResult, Error> {
        // If already solved, return state
        if let InternalSolverState::SAT = self.state {
            return Ok(SolverResult::SAT);
        } else if let InternalSolverState::UNSAT(_) = self.state {
            return Ok(SolverResult::UNSAT);
        }
        // Solve with IPASIR backend
        for a in &assumps {
            unsafe { ffi::ipasir_assume(self.handle, a.to_ipasir()) }
        }
        match unsafe { ffi::ipasir_solve(self.handle) } {
            0 => {
                self.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.n_sat += 1;
                self.state = InternalSolverState::SAT;
                Ok(SolverResult::SAT)
            }
            20 => {
                self.n_unsat += 1;
                self.state = InternalSolverState::UNSAT(self.get_core_assumps(&assumps)?);
                Ok(SolverResult::UNSAT)
            }
            invalid => Err(Error::Ipasir(IpasirError::Solve(invalid))),
        }
    }

    fn lit_val(&self, lit: &Lit) -> Result<TernaryVal, Error> {
        match &self.state {
            InternalSolverState::SAT => {
                let lit = lit.to_ipasir();
                match unsafe { ffi::ipasir_val(self.handle, lit) } {
                    0 => Ok(TernaryVal::DontCare),
                    p if p == lit => Ok(TernaryVal::True),
                    n if n == -lit => Ok(TernaryVal::False),
                    invalid => Err(Error::Ipasir(IpasirError::Val(invalid))),
                }
            }
            other => Err(Error::StateError(other.to_external(), SolverState::SAT)),
        }
    }

    fn add_clause(&mut self, clause: Vec<Lit>) {
        // Update wrapper-internal state
        self.n_clauses += 1;
        for lit in &clause {
            match self.max_var {
                None => self.max_var = Some(*lit.var()),
                Some(var) => {
                    if lit.var() > &var {
                        self.max_var = Some(*lit.var());
                    }
                }
            }
        }
        self.avg_clause_len = (self.avg_clause_len * ((self.n_clauses - 1) as f32)
            + clause.len() as f32)
            / self.n_clauses as f32;
        self.state = InternalSolverState::Input;
        // Call IPASIR backend
        for lit in clause {
            unsafe { ffi::ipasir_add(self.handle, lit.to_ipasir()) }
        }
        unsafe { ffi::ipasir_add(self.handle, 0) }
    }

    fn get_core(&mut self) -> Result<Vec<Lit>, Error> {
        match &self.state {
            InternalSolverState::UNSAT(core) => Ok(core.clone()),
            other => Err(Error::StateError(other.to_external(), SolverState::UNSAT)),
        }
    }
}

impl SolverStats for IpasirSolver {
    fn get_n_sat_solves(&self) -> u32 {
        self.n_sat
    }

    fn get_n_unsat_solves(&self) -> u32 {
        self.n_unsat
    }

    fn get_n_terminated(&self) -> u32 {
        self.n_terminated
    }

    fn get_n_clauses(&self) -> u32 {
        self.n_clauses
    }

    fn get_max_var(&self) -> Option<Var> {
        self.max_var
    }

    fn get_avg_clause_len(&self) -> f32 {
        self.avg_clause_len
    }

    fn get_cpu_solve_time(&self) -> f32 {
        self.cpu_solve_time
    }
}

impl Drop for IpasirSolver {
    fn drop(&mut self) {
        unsafe { ffi::ipasir_release(self.handle) }
    }
}

/// Type representing errors that can occur in the IPASIR API.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IpasirError {
    /// Invalid return value in the `ipasir_solve` function.
    Solve(c_int),
    /// Invalid return value in the `ipasir_val` function.
    Val(c_int),
    /// Invalid return value in the `ipasir_failed` function.
    Failed(c_int),
}

impl fmt::Display for IpasirError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IpasirError::Solve(invalid) => write!(f, "invalid response {} from solve", invalid),
            IpasirError::Val(invalid) => write!(f, "invalid response {} from val", invalid),
            IpasirError::Failed(invalid) => write!(f, "invalid response {} from failed", invalid),
        }
    }
}

#[cfg(test)]
mod test {
    use super::IpasirSolver;
    use crate::solvers::{Solver, SolverResult};
    use crate::types::Lit;

    #[test]
    fn build_destroy() {
        let _solver = IpasirSolver::new();
    }

    #[test]
    fn build_two() {
        let _solver1 = IpasirSolver::new();
        let _solver2 = IpasirSolver::new();
    }

    #[test]
    fn tiny_instance() {
        let mut solver = IpasirSolver::new();
        solver.add_clause(vec![Lit::positive(0), Lit::negative(1)]);
        solver.add_clause(vec![Lit::positive(1), Lit::negative(2)]);
        let ret = solver.solve();
        match ret {
            Err(e) => panic!("got error when solving"),
            Ok(res) => assert_eq!(res, SolverResult::SAT),
        }
    }
}
