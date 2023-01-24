//! # Glucose 4 Solver Interface
//!
//! Interface to the [Glucose 4](https://www.labri.fr/perso/lsimon/research/glucose/#glucose-4.2.1) incremental SAT solver.

use core::ffi::{c_int, CStr};
use std::fmt;

use super::{
    IncrementalSolve, InternalSolverState, Solve, SolveMightFail, SolveStats, SolverError,
    SolverResult, SolverState, SolverStats,
};
use crate::types::{Clause, Lit, TernaryVal, Var};
use cpu_time::ProcessTime;
use ffi::Glucose4Handle;

/// The Glucose 4 solver type
pub struct Glucose4 {
    handle: *mut Glucose4Handle,
    state: InternalSolverState,
    stats: SolverStats,
}

impl Default for Glucose4 {
    fn default() -> Self {
        Self {
            handle: unsafe { ffi::cglucose4_init() },
            state: Default::default(),
            stats: Default::default(),
        }
    }
}

impl Glucose4 {
    fn get_core_assumps(&self, assumps: &Vec<Lit>) -> Result<Vec<Lit>, SolverError> {
        let mut core = Vec::new();
        core.reserve(assumps.len());
        for a in assumps {
            match unsafe { ffi::cglucose4_failed(self.handle, a.to_ipasir()) } {
                0 => (),
                1 => core.push(!*a),
                invalid => {
                    return Err(SolverError::API(format!(
                        "cglucose_failed returned invalid value: {}",
                        invalid
                    )))
                }
            }
        }
        Ok(core)
    }

    /// Sets an internal limit for Glucose
    pub fn set_limit(&mut self, limit: Limit) {
        match limit {
            Limit::None => unsafe { ffi::cglucose4_set_no_limit(self.handle) },
            Limit::Conflicts(limit) => unsafe { ffi::cglucose4_set_conf_limit(self.handle, limit) },
            Limit::Propagations(limit) => unsafe {
                ffi::cglucose4_set_prop_limit(self.handle, limit)
            },
        };
    }

    /// Gets the current number of assigned literals
    pub fn n_assigns(&self) -> c_int {
        unsafe { ffi::cglucose4_n_assigns(self.handle) }
    }

    /// Gets the current number of learnt clauses
    pub fn n_learnts(&self) -> c_int {
        unsafe { ffi::cglucose4_n_learnts(self.handle) }
    }

    /// Asynchronously force the solver to terminate
    pub fn terminate(&mut self) {
        unsafe { ffi::cglucose4_interrupt(self.handle) }
    }
}

impl Solve for Glucose4 {
    fn signature(&self) -> &'static str {
        let c_chars = unsafe { ffi::cglucose4_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Glucose 4 signature returned invalid UTF-8.")
    }

    fn solve(&mut self) -> Result<SolverResult, SolverError> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::SAT);
        } else if let InternalSolverState::Unsat(core) = &self.state {
            if core.is_empty() {
                return Ok(SolverResult::UNSAT);
            }
        } else if let InternalSolverState::Error(desc) = &self.state {
            return Err(SolverError::State(
                SolverState::Error(desc.clone()),
                SolverState::Input,
            ));
        }
        let start = ProcessTime::now();
        // Solve with glucose backend
        let res = unsafe { ffi::cglucose4_solve(self.handle) };
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            0 => {
                self.stats.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.stats.n_sat += 1;
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::SAT)
            }
            20 => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Unsat(vec![]);
                Ok(SolverResult::UNSAT)
            }
            invalid => Err(SolverError::API(format!(
                "cglucose4_solve returned invalid value: {}",
                invalid
            ))),
        }
    }

    fn lit_val(&self, lit: Lit) -> Result<TernaryVal, SolverError> {
        match &self.state {
            InternalSolverState::Sat => {
                let lit = lit.to_ipasir();
                match unsafe { ffi::cglucose4_val(self.handle, lit) } {
                    0 => Ok(TernaryVal::DontCare),
                    p if p == lit => Ok(TernaryVal::True),
                    n if n == -lit => Ok(TernaryVal::False),
                    invalid => Err(SolverError::API(format!(
                        "cglucose4_val returned invalid value: {}",
                        invalid
                    ))),
                }
            }
            other => Err(SolverError::State(other.to_external(), SolverState::SAT)),
        }
    }

    fn add_clause(&mut self, clause: Clause) -> SolveMightFail {
        if let InternalSolverState::Error(_) = self.state {
            // Don't add clause if already in error state.
            return Err(SolverError::State(
                self.state.to_external(),
                SolverState::Input,
            ));
        }
        // Update wrapper-internal state
        self.stats.n_clauses += 1;
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
        self.state = InternalSolverState::Input;
        // Call glucose backend
        clause.into_iter().for_each(|l| unsafe {
            ffi::cglucose4_add(self.handle, l.to_ipasir());
        });
        unsafe { ffi::cglucose4_add(self.handle, 0) };
        Ok(())
    }
}

impl IncrementalSolve for Glucose4 {
    fn solve_assumps(&mut self, assumps: Vec<Lit>) -> Result<SolverResult, SolverError> {
        // If in error state, remain there
        // If not, need to resolve because assumptions might have changed
        if let InternalSolverState::Error(desc) = &self.state {
            return Err(SolverError::State(
                SolverState::Error(desc.clone()),
                SolverState::Input,
            ));
        }
        let start = ProcessTime::now();
        // Solve with glucose backend
        for a in &assumps {
            unsafe { ffi::cglucose4_assume(self.handle, a.to_ipasir()) }
        }
        let res = unsafe { ffi::cglucose4_solve(self.handle) };
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            0 => {
                self.stats.n_terminated += 1;
                self.state = InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.stats.n_sat += 1;
                self.state = InternalSolverState::Sat;
                Ok(SolverResult::SAT)
            }
            20 => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Unsat(self.get_core_assumps(&assumps)?);
                Ok(SolverResult::UNSAT)
            }
            invalid => Err(SolverError::API(format!(
                "cglucose4_solve returned invalid value: {}",
                invalid
            ))),
        }
    }

    fn core(&mut self) -> Result<Vec<Lit>, SolverError> {
        match &self.state {
            InternalSolverState::Unsat(core) => Ok(core.clone()),
            other => Err(SolverError::State(other.to_external(), SolverState::UNSAT)),
        }
    }
}

impl SolveStats for Glucose4 {
    fn stats(&self) -> SolverStats {
        let mut stats = self.stats.clone();
        stats.max_var = self.max_var();
        stats.n_clauses = self.n_clauses();
        stats
    }

    fn max_var(&self) -> Option<Var> {
        let max_var_idx = unsafe { ffi::cglucose4_n_vars(self.handle) };
        if max_var_idx > 0 {
            Some(Var::new((max_var_idx - 1) as usize))
        } else {
            None
        }
    }

    fn n_clauses(&self) -> usize {
        unsafe { ffi::cglucose4_n_clauses(self.handle) }
            .try_into()
            .unwrap()
    }
}

impl Drop for Glucose4 {
    fn drop(&mut self) {
        unsafe { ffi::cglucose4_release(self.handle) }
    }
}

/// Possible CaDiCaL limits
#[derive(Debug)]
pub enum Limit {
    /// No limits
    None,
    /// A limit on the number of conflicts
    Conflicts(i64),
    /// A limit on the number of propagations
    Propagations(i64),
}

impl fmt::Display for Limit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Limit::None => write!(f, "none"),
            Limit::Conflicts(val) => write!(f, "conflicts ({})", val),
            Limit::Propagations(val) => write!(f, "propagations ({})", val),
        }
    }
}

#[cfg(test)]
mod test {
    use super::Glucose4;
    use crate::{
        lit,
        solvers::{Solve, SolveStats, SolverResult},
        types::{Lit, Var},
        var,
    };

    #[test]
    fn build_destroy() {
        let _solver = Glucose4::default();
    }

    #[test]
    fn build_two() {
        let _solver1 = Glucose4::default();
        let _solver2 = Glucose4::default();
    }

    #[test]
    fn tiny_instance_sat() {
        let mut solver = Glucose4::default();
        solver.add_binary(lit![0], !lit![1]).unwrap();
        solver.add_binary(lit![1], !lit![2]).unwrap();
        let ret = solver.solve();
        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::SAT),
        }
    }

    #[test]
    fn tiny_instance_unsat() {
        let mut solver = Glucose4::default();
        solver.add_unit(!lit![0]).unwrap();
        solver.add_binary(lit![0], !lit![1]).unwrap();
        solver.add_binary(lit![1], !lit![2]).unwrap();
        solver.add_unit(lit![2]).unwrap();
        let ret = solver.solve();
        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::UNSAT),
        }
    }

    #[test]
    fn backend_stats() {
        let mut solver = Glucose4::default();
        solver.add_binary(lit![0], !lit![1]).unwrap();
        solver.add_binary(lit![1], !lit![2]).unwrap();
        solver.add_binary(lit![2], !lit![3]).unwrap();
        solver.add_binary(lit![3], !lit![4]).unwrap();
        solver.add_binary(lit![4], !lit![5]).unwrap();
        solver.add_binary(lit![5], !lit![6]).unwrap();
        solver.add_binary(lit![6], !lit![7]).unwrap();
        solver.add_binary(lit![7], !lit![8]).unwrap();
        solver.add_binary(lit![8], !lit![9]).unwrap();

        assert_eq!(solver.n_learnts(), 0);
        assert_eq!(solver.n_clauses(), 9);
        assert_eq!(solver.max_var(), Some(var![9]));
    }
}

mod ffi {
    use core::ffi::{c_char, c_int};

    #[repr(C)]
    pub struct Glucose4Handle {
        _private: [u8; 0],
    }

    extern "C" {
        // Redefinitions of CaDiCaL C API
        pub fn cglucose4_signature() -> *const c_char;
        pub fn cglucose4_init() -> *mut Glucose4Handle;
        pub fn cglucose4_release(solver: *mut Glucose4Handle);
        pub fn cglucose4_add(solver: *mut Glucose4Handle, lit_or_zero: c_int);
        pub fn cglucose4_assume(solver: *mut Glucose4Handle, lit: c_int);
        pub fn cglucose4_solve(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucose4_val(solver: *mut Glucose4Handle, lit: c_int) -> c_int;
        pub fn cglucose4_failed(solver: *mut Glucose4Handle, lit: c_int) -> c_int;
        pub fn cglucose4_n_assigns(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucose4_n_clauses(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucose4_n_learnts(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucose4_n_vars(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucose4_set_conf_limit(solver: *mut Glucose4Handle, limit: i64);
        pub fn cglucose4_set_prop_limit(solver: *mut Glucose4Handle, limit: i64);
        pub fn cglucose4_set_no_limit(solver: *mut Glucose4Handle);
        pub fn cglucose4_interrupt(solver: *mut Glucose4Handle);
    }
}
