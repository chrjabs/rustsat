//! # Glucose 4 Solver Interface With Preprocessing (Simp)
//!
//! Interface to the [Glucose](https://www.labri.fr/perso/lsimon/research/glucose/#glucose-4.2.1)
//! incremental SAT solver.

use core::ffi::{c_int, CStr};

use super::{AssumpEliminated, InternalSolverState, InvalidApiReturn, Limit};
use cpu_time::ProcessTime;
use ffi::Glucose4Handle;
use rustsat::{
    solvers::{
        FreezeVar, GetInternalStats, Interrupt, InterruptSolver, LimitConflicts, LimitPropagations,
        PhaseLit, Solve, SolveIncremental, SolveStats, SolverResult, SolverState, SolverStats,
        StateError,
    },
    types::{Clause, Lit, TernaryVal, Var},
};

/// The Glucose 4 solver type with preprocessing
pub struct Glucose {
    handle: *mut Glucose4Handle,
    state: InternalSolverState,
    stats: SolverStats,
}

unsafe impl Send for Glucose {}

impl Default for Glucose {
    fn default() -> Self {
        Self {
            handle: unsafe { ffi::cglucosesimp4_init() },
            state: Default::default(),
            stats: Default::default(),
        }
    }
}

impl Glucose {
    fn get_core_assumps(&self, assumps: &[Lit]) -> Result<Vec<Lit>, InvalidApiReturn> {
        let mut core = Vec::new();
        for a in assumps {
            match unsafe { ffi::cglucosesimp4_failed(self.handle, a.to_ipasir()) } {
                0 => (),
                1 => core.push(!*a),
                value => {
                    return Err(InvalidApiReturn {
                        api_call: "cglucosesimp4_failed",
                        value,
                    })
                }
            }
        }
        Ok(core)
    }

    /// Sets an internal limit for Glucose
    pub fn set_limit(&mut self, limit: Limit) {
        match limit {
            Limit::None => unsafe { ffi::cglucosesimp4_set_no_limit(self.handle) },
            Limit::Conflicts(limit) => unsafe {
                ffi::cglucosesimp4_set_conf_limit(self.handle, limit)
            },
            Limit::Propagations(limit) => unsafe {
                ffi::cglucosesimp4_set_prop_limit(self.handle, limit)
            },
        };
    }

    /// Gets the current number of assigned literals
    pub fn n_assigns(&self) -> c_int {
        unsafe { ffi::cglucosesimp4_n_assigns(self.handle) }
    }

    /// Gets the current number of learnt clauses
    pub fn n_learnts(&self) -> c_int {
        unsafe { ffi::cglucosesimp4_n_learnts(self.handle) }
    }

    /// Checks if a variable has been eliminated by preprocessing.
    pub fn var_eliminated(&mut self, var: Var) -> bool {
        (unsafe { ffi::cglucosesimp4_is_eliminated(self.handle, var.to_ipasir()) } != 0)
    }
}

impl Extend<Clause> for Glucose {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"))
    }
}

impl Solve for Glucose {
    fn signature(&self) -> &'static str {
        let c_chars = unsafe { ffi::cglucose4_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Glucose 4 signature returned invalid UTF-8.")
    }

    fn solve(&mut self) -> anyhow::Result<SolverResult> {
        // If already solved, return state
        if let InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        }
        if let InternalSolverState::Unsat(core) = &self.state {
            if core.is_empty() {
                return Ok(SolverResult::Unsat);
            }
        }
        let start = ProcessTime::now();
        // Solve with glucose backend
        let res = unsafe { ffi::cglucosesimp4_solve(self.handle) };
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
                Ok(SolverResult::Sat)
            }
            20 => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Unsat(vec![]);
                Ok(SolverResult::Unsat)
            }
            value => Err(InvalidApiReturn {
                api_call: "cglucosesimp4_solve",
                value,
            }
            .into()),
        }
    }

    fn lit_val(&self, lit: Lit) -> anyhow::Result<TernaryVal> {
        if self.state != InternalSolverState::Sat {
            return Err(StateError {
                required_state: SolverState::Sat,
                actual_state: self.state.to_external(),
            }
            .into());
        }
        let lit = lit.to_ipasir();
        match unsafe { ffi::cglucosesimp4_val(self.handle, lit) } {
            0 => Ok(TernaryVal::DontCare),
            p if p == lit => Ok(TernaryVal::True),
            n if n == -lit => Ok(TernaryVal::False),
            value => Err(InvalidApiReturn {
                api_call: "cglucosesimp4_val",
                value,
            }
            .into()),
        }
    }

    fn add_clause(&mut self, clause: Clause) -> anyhow::Result<()> {
        // Update wrapper-internal state
        self.stats.n_clauses += 1;
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
        self.state = InternalSolverState::Input;
        // Call glucose backend
        clause.into_iter().for_each(|l| unsafe {
            ffi::cglucosesimp4_add(self.handle, l.to_ipasir());
        });
        unsafe { ffi::cglucosesimp4_add(self.handle, 0) };
        Ok(())
    }
}

impl SolveIncremental for Glucose {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult> {
        let start = ProcessTime::now();
        // Solve with glucose backend
        for a in assumps {
            if self.var_eliminated(a.var()) {
                return Err(AssumpEliminated(a.var()).into());
            }
        }
        for a in assumps {
            unsafe { ffi::cglucosesimp4_assume(self.handle, a.to_ipasir()) }
        }
        let res = unsafe { ffi::cglucosesimp4_solve(self.handle) };
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
                Ok(SolverResult::Sat)
            }
            20 => {
                self.stats.n_unsat += 1;
                self.state = InternalSolverState::Unsat(self.get_core_assumps(assumps)?);
                Ok(SolverResult::Unsat)
            }
            value => Err(InvalidApiReturn {
                api_call: "cglucosesimp4_solve",
                value,
            }
            .into()),
        }
    }

    fn core(&mut self) -> anyhow::Result<Vec<Lit>> {
        match &self.state {
            InternalSolverState::Unsat(core) => Ok(core.clone()),
            other => Err(StateError {
                required_state: SolverState::Unsat,
                actual_state: other.to_external(),
            }
            .into()),
        }
    }
}

impl Interrupt for Glucose {
    type Interrupter = Interrupter;
    fn interrupter(&mut self) -> Self::Interrupter {
        Interrupter {
            handle: self.handle,
        }
    }
}

/// An Interrupter for the Glucose 4 Simp solver
pub struct Interrupter {
    /// The C API handle
    handle: *mut Glucose4Handle,
}

unsafe impl Send for Interrupter {}
unsafe impl Sync for Interrupter {}

impl InterruptSolver for Interrupter {
    fn interrupt(&self) {
        unsafe { ffi::cglucosesimp4_interrupt(self.handle) }
    }
}

impl PhaseLit for Glucose {
    /// Forces the default decision phase of a variable to a certain value
    fn phase_lit(&mut self, lit: Lit) -> anyhow::Result<()> {
        unsafe { ffi::cglucosesimp4_phase(self.handle, lit.to_ipasir()) };
        Ok(())
    }

    /// Undoes the effect of a call to [`Glucose::phase_lit`]
    fn unphase_var(&mut self, var: Var) -> anyhow::Result<()> {
        unsafe { ffi::cglucosesimp4_unphase(self.handle, var.to_ipasir()) };
        Ok(())
    }
}

impl FreezeVar for Glucose {
    fn freeze_var(&mut self, var: Var) -> anyhow::Result<()> {
        unsafe { ffi::cglucosesimp4_set_frozen(self.handle, var.to_ipasir(), true) };
        Ok(())
    }

    fn melt_var(&mut self, var: Var) -> anyhow::Result<()> {
        unsafe { ffi::cglucosesimp4_set_frozen(self.handle, var.to_ipasir(), false) };
        Ok(())
    }

    fn is_frozen(&mut self, var: Var) -> anyhow::Result<bool> {
        Ok(unsafe { ffi::cglucosesimp4_is_frozen(self.handle, var.to_ipasir()) } != 0)
    }
}

impl LimitConflicts for Glucose {
    fn limit_conflicts(&mut self, limit: Option<u32>) -> anyhow::Result<()> {
        self.set_limit(Limit::Conflicts(if let Some(limit) = limit {
            limit as i64
        } else {
            -1
        }));
        Ok(())
    }
}

impl LimitPropagations for Glucose {
    fn limit_propagations(&mut self, limit: Option<u32>) -> anyhow::Result<()> {
        self.set_limit(Limit::Propagations(if let Some(limit) = limit {
            limit as i64
        } else {
            -1
        }));
        Ok(())
    }
}

impl GetInternalStats for Glucose {
    fn propagations(&self) -> usize {
        unsafe { ffi::cglucosesimp4_propagations(self.handle) }
            .try_into()
            .unwrap()
    }

    fn decisions(&self) -> usize {
        unsafe { ffi::cglucosesimp4_decisions(self.handle) }
            .try_into()
            .unwrap()
    }

    fn conflicts(&self) -> usize {
        unsafe { ffi::cglucosesimp4_conflicts(self.handle) }
            .try_into()
            .unwrap()
    }
}

impl SolveStats for Glucose {
    fn stats(&self) -> SolverStats {
        let mut stats = self.stats.clone();
        stats.max_var = self.max_var();
        stats.n_clauses = self.n_clauses();
        stats
    }

    fn max_var(&self) -> Option<Var> {
        let max_var_idx = unsafe { ffi::cglucosesimp4_n_vars(self.handle) };
        if max_var_idx > 0 {
            Some(Var::new((max_var_idx - 1) as u32))
        } else {
            None
        }
    }

    fn n_clauses(&self) -> usize {
        unsafe { ffi::cglucosesimp4_n_clauses(self.handle) }
            .try_into()
            .unwrap()
    }
}

impl Drop for Glucose {
    fn drop(&mut self) {
        unsafe { ffi::cglucosesimp4_release(self.handle) }
    }
}

#[cfg(test)]
mod test {
    use super::Glucose;
    use rustsat::{
        lit,
        solvers::{Solve, SolveStats},
        var,
    };

    rustsat_solvertests::basic_unittests!(Glucose);
    rustsat_solvertests::freezing_unittests!(Glucose);

    #[test]
    fn backend_stats() {
        let mut solver = Glucose::default();
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
        // Redefinitions of Glucose C API
        pub fn cglucose4_signature() -> *const c_char;
        pub fn cglucosesimp4_init() -> *mut Glucose4Handle;
        pub fn cglucosesimp4_release(solver: *mut Glucose4Handle);
        pub fn cglucosesimp4_add(solver: *mut Glucose4Handle, lit_or_zero: c_int);
        pub fn cglucosesimp4_assume(solver: *mut Glucose4Handle, lit: c_int);
        pub fn cglucosesimp4_solve(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucosesimp4_val(solver: *mut Glucose4Handle, lit: c_int) -> c_int;
        pub fn cglucosesimp4_failed(solver: *mut Glucose4Handle, lit: c_int) -> c_int;
        pub fn cglucosesimp4_phase(solver: *mut Glucose4Handle, lit: c_int);
        pub fn cglucosesimp4_unphase(solver: *mut Glucose4Handle, lit: c_int);
        pub fn cglucosesimp4_n_assigns(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucosesimp4_n_clauses(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucosesimp4_n_learnts(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucosesimp4_n_vars(solver: *mut Glucose4Handle) -> c_int;
        pub fn cglucosesimp4_set_conf_limit(solver: *mut Glucose4Handle, limit: i64);
        pub fn cglucosesimp4_set_prop_limit(solver: *mut Glucose4Handle, limit: i64);
        pub fn cglucosesimp4_set_no_limit(solver: *mut Glucose4Handle);
        pub fn cglucosesimp4_interrupt(solver: *mut Glucose4Handle);
        pub fn cglucosesimp4_set_frozen(solver: *mut Glucose4Handle, var: c_int, frozen: bool);
        pub fn cglucosesimp4_is_frozen(solver: *mut Glucose4Handle, var: c_int) -> c_int;
        pub fn cglucosesimp4_is_eliminated(solver: *mut Glucose4Handle, var: c_int) -> c_int;
        pub fn cglucosesimp4_propagations(solver: *mut Glucose4Handle) -> u64;
        pub fn cglucosesimp4_decisions(solver: *mut Glucose4Handle) -> u64;
        pub fn cglucosesimp4_conflicts(solver: *mut Glucose4Handle) -> u64;
    }
}
