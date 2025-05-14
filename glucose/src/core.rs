//! # Glucose Solver Interface Without Preprocessing (Core)
//!
//! Interface to the [Glucose](https://www.labri.fr/perso/lsimon/research/glucose/#glucose-4.2.1)
//! incremental SAT solver.

use core::ffi::{c_int, CStr};

use cpu_time::ProcessTime;
use rustsat::{
    solvers::{
        GetInternalStats, Interrupt, InterruptSolver, LimitConflicts, LimitPropagations, PhaseLit,
        Propagate, PropagateResult, Solve, SolveIncremental, SolveStats, SolverResult, SolverState,
        SolverStats, StateError,
    },
    types::{Cl, Clause, Lit, TernaryVal, Var},
};

use super::{ffi, handle_oom, InternalSolverState, InvalidApiReturn, Limit};

/// The Glucose 4 solver type without preprocessing
#[derive(Debug)]
pub struct Glucose {
    handle: *mut ffi::CGlucose4,
    state: InternalSolverState,
    stats: SolverStats,
}

unsafe impl Send for Glucose {}

impl Default for Glucose {
    fn default() -> Self {
        let handle = unsafe { ffi::cglucose4_init() };
        assert!(
            !handle.is_null(),
            "not enough memory to initialize glucose solver"
        );
        Self {
            handle,
            state: InternalSolverState::default(),
            stats: SolverStats::default(),
        }
    }
}

impl Glucose {
    #[allow(clippy::cast_precision_loss)]
    #[inline]
    fn update_avg_clause_len(&mut self, clause: &Cl) {
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
    }

    /// Sets an internal limit for Glucose
    pub fn set_limit(&mut self, limit: Limit) {
        match limit {
            Limit::None => unsafe { ffi::cglucose4_set_no_limit(self.handle) },
            Limit::Conflicts(limit) => unsafe { ffi::cglucose4_set_conf_limit(self.handle, limit) },
            Limit::Propagations(limit) => unsafe {
                ffi::cglucose4_set_prop_limit(self.handle, limit);
            },
        }
    }

    /// Gets the current number of assigned literals
    #[must_use]
    pub fn n_assigns(&self) -> c_int {
        unsafe { ffi::cglucose4_n_assigns(self.handle) }
    }

    /// Gets the current number of learnt clauses
    #[must_use]
    pub fn n_learnts(&self) -> c_int {
        unsafe { ffi::cglucose4_n_learnts(self.handle) }
    }
}

impl Extend<Clause> for Glucose {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"));
    }
}

impl<'a, C> Extend<&'a C> for Glucose
where
    C: AsRef<Cl> + ?Sized,
{
    fn extend<T: IntoIterator<Item = &'a C>>(&mut self, iter: T) {
        iter.into_iter().for_each(|cl| {
            self.add_clause_ref(cl)
                .expect("Error adding clause in extend");
        });
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
        if let InternalSolverState::Unsat(under_assumps) = &self.state {
            if !under_assumps {
                return Ok(SolverResult::Unsat);
            }
        }
        let start = ProcessTime::now();
        // Solve with glucose backend
        let res = handle_oom!(unsafe { ffi::cglucose4_solve(self.handle, std::ptr::null(), 0) });
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
                self.state = InternalSolverState::Unsat(false);
                Ok(SolverResult::Unsat)
            }
            value => Err(InvalidApiReturn {
                api_call: "cglucose4_solve",
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
        match unsafe { ffi::cglucose4_val(self.handle, lit.into()) } {
            ffi::T_UNASSIGNED => Ok(TernaryVal::DontCare),
            ffi::T_TRUE => Ok(TernaryVal::True),
            ffi::T_FALSE => Ok(TernaryVal::False),
            value => Err(InvalidApiReturn {
                api_call: "cglucose4_val",
                value,
            }
            .into()),
        }
    }

    fn add_clause_ref<C>(&mut self, clause: &C) -> anyhow::Result<()>
    where
        C: AsRef<Cl> + ?Sized,
    {
        let clause = clause.as_ref();
        // Update wrapper-internal state
        self.stats.n_clauses += 1;
        self.update_avg_clause_len(clause);
        self.state = InternalSolverState::Input;
        handle_oom!(unsafe {
            ffi::cglucose4_add_clause(self.handle, clause.as_ref().as_ptr().cast(), clause.len())
        });
        Ok(())
    }

    fn reserve(&mut self, max_var: Var) -> anyhow::Result<()> {
        handle_oom!(unsafe {
            #[allow(clippy::cast_possible_wrap)]
            ffi::cglucose4_reserve(self.handle, max_var.idx32() as c_int)
        });
        Ok(())
    }
}

impl SolveIncremental for Glucose {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult> {
        let start = ProcessTime::now();
        // Solve with glucose backend
        let res = handle_oom!(unsafe {
            ffi::cglucose4_solve(self.handle, assumps.as_ptr().cast(), assumps.len())
        });
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
                self.state = InternalSolverState::Unsat(true);
                Ok(SolverResult::Unsat)
            }
            value => Err(InvalidApiReturn {
                api_call: "cglucose4_solve",
                value,
            }
            .into()),
        }
    }

    fn core(&mut self) -> anyhow::Result<Vec<Lit>> {
        match &self.state {
            InternalSolverState::Unsat(under_assumps) => {
                if *under_assumps {
                    let conflict = unsafe {
                        let mut conflict = std::ptr::null::<ffi::c_Lit>();
                        let mut conflict_len = 0;
                        ffi::cglucose4_conflict(self.handle, &mut conflict, &mut conflict_len);
                        std::slice::from_raw_parts(conflict.cast(), conflict_len)
                    };
                    Ok(conflict.to_vec())
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

impl Interrupt for Glucose {
    type Interrupter = Interrupter;
    fn interrupter(&mut self) -> Self::Interrupter {
        Interrupter {
            handle: self.handle,
        }
    }
}

/// An Interrupter for the Glucose 4 Core solver
#[derive(Debug)]
pub struct Interrupter {
    /// The C API handle
    handle: *mut ffi::CGlucose4,
}

unsafe impl Send for Interrupter {}
unsafe impl Sync for Interrupter {}

impl InterruptSolver for Interrupter {
    fn interrupt(&self) {
        unsafe { ffi::cglucose4_interrupt(self.handle) }
    }
}

impl PhaseLit for Glucose {
    /// Forces the default decision phase of a variable to a certain value
    fn phase_lit(&mut self, lit: Lit) -> anyhow::Result<()> {
        self.reserve(lit.var())?;
        handle_oom!(unsafe { ffi::cglucose4_phase(self.handle, lit.into()) });
        Ok(())
    }

    /// Undoes the effect of a call to [`Glucose::phase_lit`]
    fn unphase_var(&mut self, var: Var) -> anyhow::Result<()> {
        match self.max_var() {
            None => return Ok(()),
            Some(max) if max < var => return Ok(()),
            _ => (),
        }
        unsafe {
            #[allow(clippy::cast_possible_wrap)]
            ffi::cglucose4_unphase(self.handle, var.idx32() as c_int);
        };
        Ok(())
    }
}

impl LimitConflicts for Glucose {
    fn limit_conflicts(&mut self, limit: Option<u32>) -> anyhow::Result<()> {
        self.set_limit(Limit::Conflicts(if let Some(limit) = limit {
            i64::from(limit)
        } else {
            -1
        }));
        Ok(())
    }
}

impl LimitPropagations for Glucose {
    fn limit_propagations(&mut self, limit: Option<u32>) -> anyhow::Result<()> {
        self.set_limit(Limit::Propagations(if let Some(limit) = limit {
            i64::from(limit)
        } else {
            -1
        }));
        Ok(())
    }
}

impl GetInternalStats for Glucose {
    fn propagations(&self) -> usize {
        unsafe { ffi::cglucose4_propagations(self.handle) }
            .try_into()
            .unwrap()
    }

    fn decisions(&self) -> usize {
        unsafe { ffi::cglucose4_decisions(self.handle) }
            .try_into()
            .unwrap()
    }

    fn conflicts(&self) -> usize {
        unsafe { ffi::cglucose4_conflicts(self.handle) }
            .try_into()
            .unwrap()
    }
}

impl Propagate for Glucose {
    fn propagate(
        &mut self,
        assumps: &[Lit],
        phase_saving: bool,
    ) -> anyhow::Result<PropagateResult> {
        let start = ProcessTime::now();
        self.state = InternalSolverState::Input;
        // Propagate with glucose backend
        let mut props = Vec::new();
        let ptr: *mut Vec<Lit> = &mut props;
        let res = handle_oom!(unsafe {
            ffi::cglucose4_propcheck(
                self.handle,
                assumps.as_ptr().cast(),
                assumps.len(),
                c_int::from(phase_saving),
                Some(ffi::rustsat_glucose_collect_lits),
                ptr.cast::<std::os::raw::c_void>(),
            )
        });
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            10 => Ok(PropagateResult {
                propagated: props,
                conflict: false,
            }),
            20 => Ok(PropagateResult {
                propagated: props,
                conflict: true,
            }),
            value => Err(InvalidApiReturn {
                api_call: "cglucose4_propcheck",
                value,
            }
            .into()),
        }
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
        let max_var_idx = unsafe { ffi::cglucose4_n_vars(self.handle) };
        if max_var_idx > 0 {
            Some(Var::new(
                (max_var_idx - 1)
                    .try_into()
                    .expect("got negative number of vars from glucose"),
            ))
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

impl Drop for Glucose {
    fn drop(&mut self) {
        unsafe { ffi::cglucose4_release(self.handle) }
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

    rustsat_solvertests::basic_unittests!(Glucose, "Glucose [major].[minor].[patch]");
    rustsat_solvertests::propagating_unittests!(Glucose);

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
