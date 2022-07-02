mod ffi;

use std::{ffi::CStr, fmt, os::raw::c_int};

use super::{InternalSolverState, Solver, SolverResult, SolverStats};
use crate::types::{Error, Lit, LitVal};
use ffi::IpasirHandle;

pub struct IpasirSolver {
    handle: *mut IpasirHandle,
    state: InternalSolverState,
    n_sat: u32,
    n_unsat: u32,
    n_terminated: u32,
    n_clauses: u32,
    n_vars: u32,
    avg_clause_len: f32,
    cpu_solve_time: f32,
}

impl IpasirSolver {
    pub fn new() -> IpasirSolver {
        IpasirSolver {
            handle: unsafe { ffi::ipasir_init() },
            state: InternalSolverState::Input,
            n_sat: 0,
            n_unsat: 0,
            n_terminated: 0,
            n_clauses: 0,
            n_vars: 0,
            avg_clause_len: 0.0,
            cpu_solve_time: 0.0,
        }
    }

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

    fn lit_val(&self, lit: &crate::types::Lit) -> Result<LitVal, Error> {
        match &self.state {
            InternalSolverState::SAT => {
                let lit = lit.to_ipasir();
                match unsafe { ffi::ipasir_val(self.handle, lit) } {
                    0 => Ok(LitVal::DontCare),
                    p if p == lit => Ok(LitVal::True),
                    n if n == -lit => Ok(LitVal::False),
                    invalid => Err(Error::Ipasir(IpasirError::Val(invalid))),
                }
            }
            other => Err(Error::StateError(other.to_external())),
        }
    }

    fn add_clause(&mut self, clause: Vec<crate::types::Lit>) {
        self.state = InternalSolverState::Input;
        for lit in clause {
            unsafe { ffi::ipasir_add(self.handle, lit.to_ipasir()) }
        }
        unsafe { ffi::ipasir_add(self.handle, 0) }
    }

    fn get_core(&mut self) -> Option<Vec<crate::types::Lit>> {
        match &self.state {
            InternalSolverState::UNSAT(core) => Some(core.clone()),
            _ => None,
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

impl Drop for IpasirSolver {
    fn drop(&mut self) {
        unsafe { ffi::ipasir_release(self.handle) }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IpasirError {
    Solve(c_int),
    Val(c_int),
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
