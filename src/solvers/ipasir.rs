//! # IPASIR Interface
//!
//! Interface to any SAT solver implementing the
//! [IPASIR API](https://github.com/biotomas/ipasir) for incremental SAT solvers.

mod ffi;

use std::{
    ffi::CStr,
    fmt,
    os::raw::{c_int, c_void},
};

use super::{
    ControlSignal, IncrementalSolve, InternalSolverState, Solve, SolveStats, SolverResult,
    SolverState,
};
use crate::types::{Clause, Error, Lit, TernaryVal, Var};
use ffi::IpasirHandle;

/// Type for an IPASIR solver.
pub struct IpasirSolver<'a> {
    handle: *mut IpasirHandle,
    state: InternalSolverState,
    terminate_cb: Option<Box<Box<dyn FnMut() -> ControlSignal + 'a>>>,
    learner_cb: Option<Box<Box<dyn FnMut(Vec<Lit>) + 'a>>>,
    n_sat: u32,
    n_unsat: u32,
    n_terminated: u32,
    n_clauses: u32,
    max_var: Option<Var>,
    avg_clause_len: f32,
    cpu_solve_time: f32,
}

impl<'a> IpasirSolver<'a> {
    /// Creates a new IPASIR solver.
    pub fn new() -> IpasirSolver<'a> {
        IpasirSolver {
            handle: unsafe { ffi::ipasir_init() },
            state: InternalSolverState::Input,
            terminate_cb: None,
            learner_cb: None,
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

    /// Sets a terminator callback that is regularly called during solving.
    ///
    /// # Examples
    ///
    /// Terminate solver after 10 callback calls.
    ///
    /// ```
    /// use rustsat::solvers::{ipasir::IpasirSolver, ControlSignal, Solve, SolverResult};
    ///
    /// let mut solver = IpasirSolver::new();
    ///
    /// // Load instance
    ///
    /// let mut cnt = 1;
    /// solver.set_terminator(move || {
    ///     if cnt > 10 {
    ///         ControlSignal::Terminate
    ///     } else {
    ///         cnt += 1;
    ///         ControlSignal::Continue
    ///     }
    /// });
    ///
    /// let ret = solver.solve().unwrap();
    ///
    /// // Assuming an instance is actually loaded and runs long enough
    /// // assert_eq!(ret, SolverResult::Interrupted);
    /// ```
    pub fn set_terminator<CB>(&mut self, cb: CB)
    where
        CB: FnMut() -> ControlSignal + 'a,
    {
        self.terminate_cb = Some(Box::new(Box::new(cb)));
        let cb_ptr = self.terminate_cb.as_mut().unwrap().as_mut() as *const _ as *const c_void;
        unsafe { ffi::ipasir_set_terminate(self.handle, cb_ptr, ffi::ipasir_terminate_cb) }
    }

    /// Sets a learner callback that gets passed clauses up to a certain length learned by the solver.
    ///
    /// The callback goes out of scope with the solver, afterwards captured variables become accessible.
    ///
    /// # Examples
    ///
    /// Count number of learned clauses up to length 10.
    ///
    /// ```
    /// use rustsat::solvers::{ipasir::IpasirSolver, Solve, SolverResult};
    ///
    /// let mut cnt = 0;
    ///
    /// {
    ///     let mut solver = IpasirSolver::new();
    ///     // Load instance
    ///
    ///     solver.set_learner(|_| cnt += 1, 10);
    ///
    ///     solver.solve().unwrap();
    /// }
    ///
    /// // cnt variable can be accessed from here on
    /// ```
    pub fn set_learner<CB>(&mut self, cb: CB, max_len: usize)
    where
        CB: FnMut(Vec<Lit>) + 'a,
    {
        self.learner_cb = Some(Box::new(Box::new(cb)));
        let cb_ptr = self.learner_cb.as_mut().unwrap().as_mut() as *const _ as *const c_void;
        unsafe {
            ffi::ipasir_set_learn(
                self.handle,
                cb_ptr,
                max_len.try_into().unwrap(),
                ffi::ipasir_learn_cb,
            )
        }
    }
}

impl Solve for IpasirSolver<'_> {
    fn solve(&mut self) -> Result<SolverResult, Error> {
        // If already solved, return state
        if let InternalSolverState::SAT = self.state {
            return Ok(SolverResult::SAT);
        } else if let InternalSolverState::UNSAT(_) = self.state {
            return Ok(SolverResult::UNSAT);
        } else if let InternalSolverState::Error(desc) = &self.state {
            return Err(Error::State(
                SolverState::Error(desc.clone()),
                SolverState::Input,
            ));
        }
        // Solve with IPASIR backend
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
                self.state = InternalSolverState::UNSAT(vec![]);
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
            other => Err(Error::State(other.to_external(), SolverState::SAT)),
        }
    }

    fn add_clause(&mut self, clause: Clause) {
        if let InternalSolverState::Error(_) = self.state {
            // Don't add clause if already in error state.
            return;
        }
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
        for lit in &clause {
            unsafe { ffi::ipasir_add(self.handle, lit.to_ipasir()) }
        }
        unsafe { ffi::ipasir_add(self.handle, 0) }
    }
}

impl IncrementalSolve for IpasirSolver<'_> {
    fn solve_assumps(&mut self, assumps: Vec<Lit>) -> Result<SolverResult, Error> {
        // If already solved, return state
        if let InternalSolverState::SAT = self.state {
            return Ok(SolverResult::SAT);
        } else if let InternalSolverState::UNSAT(_) = self.state {
            return Ok(SolverResult::UNSAT);
        } else if let InternalSolverState::Error(desc) = &self.state {
            return Err(Error::State(
                SolverState::Error(desc.clone()),
                SolverState::Input,
            ));
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

    fn get_core(&mut self) -> Result<Vec<Lit>, Error> {
        match &self.state {
            InternalSolverState::UNSAT(core) => Ok(core.clone()),
            other => Err(Error::State(other.to_external(), SolverState::UNSAT)),
        }
    }
}

impl SolveStats for IpasirSolver<'_> {
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

impl Drop for IpasirSolver<'_> {
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
    /// Zero was tried to use as a literal
    ZeroLiteral,
}

impl fmt::Display for IpasirError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IpasirError::Solve(invalid) => write!(f, "invalid response {} from solve", invalid),
            IpasirError::Val(invalid) => write!(f, "invalid response {} from val", invalid),
            IpasirError::Failed(invalid) => write!(f, "invalid response {} from failed", invalid),
            IpasirError::ZeroLiteral => write!(f, "zero is an invalid IPASIR literal value"),
        }
    }
}

#[cfg(test)]
mod test {
    use super::IpasirSolver;
    use crate::lit;
    use crate::solvers::{ControlSignal, Solve, SolverResult};
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
        solver.add_pair(lit![0], !lit![1]);
        solver.add_pair(lit![1], !lit![2]);
        let ret = solver.solve();
        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::SAT),
        }
    }

    #[test]
    fn termination_callback() {
        let mut solver = IpasirSolver::new();
        solver.add_pair(lit![0], !lit![1]);
        solver.add_pair(lit![1], !lit![2]);
        solver.add_pair(lit![2], !lit![3]);
        solver.add_pair(lit![3], !lit![4]);
        solver.add_pair(lit![4], !lit![5]);
        solver.add_pair(lit![5], !lit![6]);
        solver.add_pair(lit![6], !lit![7]);
        solver.add_pair(lit![7], !lit![8]);
        solver.add_pair(lit![8], !lit![9]);

        solver.set_terminator(|| ControlSignal::Terminate);

        let ret = solver.solve();

        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::Interrupted),
        }

        // Note: since IPASIR doesn't specify _when_ the terminator callback needs
        // to be called, there is no guarantee that the callback is actually
        // called during solving. This might cause this test to fail with some solvers.
    }

    #[test]
    fn learner_callback() {
        let mut solver = IpasirSolver::new();
        solver.add_pair(lit![0], !lit![1]);
        solver.add_pair(lit![1], !lit![2]);
        solver.add_pair(lit![2], !lit![3]);
        solver.add_pair(lit![3], !lit![4]);
        solver.add_pair(lit![4], !lit![5]);
        solver.add_pair(lit![5], !lit![6]);
        solver.add_pair(lit![6], !lit![7]);
        solver.add_pair(lit![7], !lit![8]);
        solver.add_pair(lit![8], !lit![9]);
        solver.add_unit(lit![9]);
        solver.add_unit(!lit![0]);

        let mut cl_len = 0;
        let ret;

        solver.set_learner(
            |clause| {
                cl_len = clause.len();
            },
            10,
        );

        ret = solver.solve();

        drop(solver);

        // Note: it is hard to create a testing instance on which clause learning
        // actually happens and therefore it is not actually tested if the
        // callback is called

        match ret {
            Err(e) => panic!("got error when solving: {}", e),
            Ok(res) => assert_eq!(res, SolverResult::UNSAT),
        }
    }
}
