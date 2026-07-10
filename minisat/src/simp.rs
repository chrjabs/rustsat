//! # Minisat Solver Interface With Preprocessing (Simp)
//!
//! Interface to the [Minisat](https://github.com/niklasso/minisat) incremental
//! SAT solver.

use core::ffi::c_int;
use core::ffi::CStr;

use rustsat::solvers::SolverResult;
use rustsat::types::Cl;
use rustsat::types::Clause;
use rustsat::types::Lit;
use rustsat::types::Var;

/// The Minisat solver type with preprocessing
#[derive(Debug)]
pub struct Minisat {
    handle: *mut crate::ffi::CMinisatSimp,
    state: crate::InternalSolverState,
    stats: rustsat::solvers::SolverStats,
}

unsafe impl Send for Minisat {}

impl Default for Minisat {
    fn default() -> Self {
        let handle = unsafe { crate::ffi::cminisatsimp_init() };
        assert!(
            !handle.is_null(),
            "not enough memory to initialize minisat solver"
        );
        Self {
            handle,
            state: crate::InternalSolverState::default(),
            stats: rustsat::solvers::SolverStats::default(),
        }
    }
}

impl Minisat {
    #[expect(clippy::cast_precision_loss)]
    #[inline]
    fn update_avg_clause_len(&mut self, clause: &Cl) {
        self.stats.avg_clause_len =
            (self.stats.avg_clause_len * ((self.stats.n_clauses - 1) as f32) + clause.len() as f32)
                / self.stats.n_clauses as f32;
    }

    /// Sets an internal limit for Minisat
    pub fn set_limit(&mut self, limit: crate::Limit) {
        match limit {
            crate::Limit::None => unsafe { crate::ffi::cminisatsimp_set_no_limit(self.handle) },
            crate::Limit::Conflicts(limit) => unsafe {
                crate::ffi::cminisatsimp_set_conf_limit(self.handle, limit);
            },
            crate::Limit::Propagations(limit) => unsafe {
                crate::ffi::cminisatsimp_set_prop_limit(self.handle, limit);
            },
        }
    }

    /// Gets the current number of assigned literals
    #[must_use]
    pub fn n_assigns(&self) -> c_int {
        unsafe { crate::ffi::cminisatsimp_n_assigns(self.handle) }
    }

    /// Gets the current number of learnt clauses
    #[must_use]
    pub fn n_learnts(&self) -> c_int {
        unsafe { crate::ffi::cminisatsimp_n_learnts(self.handle) }
    }

    /// Checks if a variable has been eliminated by preprocessing.
    pub fn var_eliminated(&mut self, var: Var) -> bool {
        (unsafe {
            #[expect(clippy::cast_possible_wrap)]
            crate::ffi::cminisatsimp_is_eliminated(self.handle, var.idx32() as c_int)
        } != 0)
    }
}

impl Extend<Clause> for Minisat {
    fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
        use rustsat::solvers::Solve;

        iter.into_iter()
            .for_each(|cl| self.add_clause(cl).expect("Error adding clause in extend"));
    }
}

impl<'a, C> Extend<&'a C> for Minisat
where
    C: AsRef<Cl> + ?Sized,
{
    fn extend<T: IntoIterator<Item = &'a C>>(&mut self, iter: T) {
        use rustsat::solvers::Solve;

        iter.into_iter().for_each(|cl| {
            self.add_clause_ref(cl)
                .expect("Error adding clause in extend");
        });
    }
}

impl rustsat::solvers::Solve for Minisat {
    fn signature(&self) -> &'static str {
        let c_chars = unsafe { crate::ffi::cminisat_signature() };
        let c_str = unsafe { CStr::from_ptr(c_chars) };
        c_str
            .to_str()
            .expect("Minisat signature returned invalid UTF-8.")
    }

    fn solve(&mut self) -> anyhow::Result<SolverResult> {
        // If already solved, return state
        if let crate::InternalSolverState::Sat = self.state {
            return Ok(SolverResult::Sat);
        }
        if let crate::InternalSolverState::Unsat(under_assumps) = &self.state {
            if !under_assumps {
                return Ok(SolverResult::Unsat);
            }
        }
        let start = rustsat::utils::Timer::now();
        // Solve with minisat backend
        let res = crate::handle_oom!(unsafe {
            crate::ffi::cminisatsimp_solve(self.handle, std::ptr::null(), 0)
        });
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            0 => {
                self.stats.n_terminated += 1;
                self.state = crate::InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.stats.n_sat += 1;
                self.state = crate::InternalSolverState::Sat;
                Ok(SolverResult::Sat)
            }
            20 => {
                self.stats.n_unsat += 1;
                self.state = crate::InternalSolverState::Unsat(false);
                Ok(SolverResult::Unsat)
            }
            value => Err(crate::InvalidApiReturn {
                api_call: "cminisatsimp_solve",
                value,
            }
            .into()),
        }
    }

    fn lit_val(&self, lit: Lit) -> anyhow::Result<rustsat::types::TernaryVal> {
        if self.state != crate::InternalSolverState::Sat {
            return Err(rustsat::solvers::StateError {
                required_state: rustsat::solvers::SolverState::Sat,
                actual_state: self.state.to_external(),
            }
            .into());
        }
        match unsafe { crate::ffi::cminisatsimp_val(self.handle, lit.into()) } {
            crate::ffi::T_UNASSIGNED => Ok(rustsat::types::TernaryVal::DontCare),
            crate::ffi::T_TRUE => Ok(rustsat::types::TernaryVal::True),
            crate::ffi::T_FALSE => Ok(rustsat::types::TernaryVal::False),
            value => Err(crate::InvalidApiReturn {
                api_call: "cminisatsimp_val",
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
        self.state = crate::InternalSolverState::Input;
        crate::handle_oom!(unsafe {
            crate::ffi::cminisatsimp_add_clause(
                self.handle,
                AsRef::<[Lit]>::as_ref(clause).as_ptr().cast(),
                clause.len(),
            )
        });
        Ok(())
    }

    fn reserve(&mut self, max_var: Var) -> anyhow::Result<()> {
        crate::handle_oom!(unsafe {
            #[expect(clippy::cast_possible_wrap)]
            crate::ffi::cminisatsimp_reserve(self.handle, max_var.idx32() as c_int)
        });
        Ok(())
    }
}

impl rustsat::solvers::SolveIncremental for Minisat {
    fn solve_assumps(&mut self, assumps: &[Lit]) -> anyhow::Result<SolverResult> {
        let start = rustsat::utils::Timer::now();
        // Solve with minisat backend
        for a in assumps {
            if self.var_eliminated(a.var()) {
                return Err(crate::AssumpEliminated(a.var()).into());
            }
        }
        let res = crate::handle_oom!(unsafe {
            crate::ffi::cminisatsimp_solve(self.handle, assumps.as_ptr().cast(), assumps.len())
        });
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            0 => {
                self.stats.n_terminated += 1;
                self.state = crate::InternalSolverState::Input;
                Ok(SolverResult::Interrupted)
            }
            10 => {
                self.stats.n_sat += 1;
                self.state = crate::InternalSolverState::Sat;
                Ok(SolverResult::Sat)
            }
            20 => {
                self.stats.n_unsat += 1;
                self.state = crate::InternalSolverState::Unsat(true);
                Ok(SolverResult::Unsat)
            }
            value => Err(crate::InvalidApiReturn {
                api_call: "cminisatsimp_solve",
                value,
            }
            .into()),
        }
    }

    fn core(&mut self) -> anyhow::Result<Vec<Lit>> {
        match &self.state {
            crate::InternalSolverState::Unsat(under_assumps) => {
                if *under_assumps {
                    let conflict = unsafe {
                        let mut conflict = std::ptr::null::<crate::ffi::c_Lit>();
                        let mut conflict_len = 0;
                        crate::ffi::cminisatsimp_conflict(
                            self.handle,
                            &raw mut conflict,
                            &raw mut conflict_len,
                        );
                        rustsat::utils::from_raw_parts_maybe_null(conflict.cast(), conflict_len)
                    };
                    Ok(conflict.to_vec())
                } else {
                    Ok(vec![])
                }
            }
            other => Err(rustsat::solvers::StateError {
                required_state: rustsat::solvers::SolverState::Unsat,
                actual_state: other.to_external(),
            }
            .into()),
        }
    }
}

impl rustsat::solvers::Interrupt for Minisat {
    type Interrupter = Interrupter;
    fn interrupter(&mut self) -> Self::Interrupter {
        Interrupter {
            handle: self.handle,
        }
    }
}

/// An Interrupter for the Minisat Simp solver
#[derive(Debug)]
pub struct Interrupter {
    /// The C API handle
    handle: *mut crate::ffi::CMinisatSimp,
}

unsafe impl Send for Interrupter {}
unsafe impl Sync for Interrupter {}

impl rustsat::solvers::InterruptSolver for Interrupter {
    fn interrupt(&self) {
        unsafe { crate::ffi::cminisatsimp_interrupt(self.handle) }
    }
}

impl rustsat::solvers::PhaseLit for Minisat {
    /// Forces the default decision phase of a variable to a certain value
    fn phase_lit(&mut self, lit: Lit) -> anyhow::Result<()> {
        use rustsat::solvers::Solve;

        self.reserve(lit.var())?;
        crate::handle_oom!(unsafe { crate::ffi::cminisatsimp_phase(self.handle, lit.into()) });
        Ok(())
    }

    /// Undoes the effect of a call to [`Minisat::phase_lit`]
    fn unphase_var(&mut self, var: Var) -> anyhow::Result<()> {
        use rustsat::solvers::SolveStats;

        match self.max_var() {
            None => return Ok(()),
            Some(max) if max < var => return Ok(()),
            _ => (),
        }
        unsafe {
            #[expect(clippy::cast_possible_wrap)]
            crate::ffi::cminisatsimp_unphase(self.handle, var.idx32() as c_int);
        };
        Ok(())
    }
}

impl rustsat::solvers::FreezeVar for Minisat {
    fn freeze_var(&mut self, var: Var) -> anyhow::Result<()> {
        use rustsat::solvers::Solve;

        self.reserve(var)?;
        unsafe {
            #[expect(clippy::cast_possible_wrap)]
            crate::ffi::cminisatsimp_set_frozen(self.handle, var.idx32() as c_int, 1);
        };
        Ok(())
    }

    fn melt_var(&mut self, var: Var) -> anyhow::Result<()> {
        use rustsat::solvers::SolveStats;

        match self.max_var() {
            None => return Ok(()),
            Some(max) if max < var => return Ok(()),
            _ => (),
        }
        unsafe {
            #[expect(clippy::cast_possible_wrap)]
            crate::ffi::cminisatsimp_set_frozen(self.handle, var.idx32() as c_int, 0);
        };
        Ok(())
    }

    fn is_frozen(&mut self, var: Var) -> anyhow::Result<bool> {
        use rustsat::solvers::SolveStats;

        match self.max_var() {
            None => return Ok(false),
            Some(max) if max < var => return Ok(false),
            _ => (),
        }
        Ok(unsafe {
            #[expect(clippy::cast_possible_wrap)]
            crate::ffi::cminisatsimp_is_frozen(self.handle, var.idx32() as c_int)
        } != 0)
    }
}

impl rustsat::solvers::LimitConflicts for Minisat {
    fn limit_conflicts(&mut self, limit: Option<u32>) -> anyhow::Result<()> {
        self.set_limit(crate::Limit::Conflicts(if let Some(limit) = limit {
            i64::from(limit)
        } else {
            -1
        }));
        Ok(())
    }
}

impl rustsat::solvers::LimitPropagations for Minisat {
    fn limit_propagations(&mut self, limit: Option<u32>) -> anyhow::Result<()> {
        self.set_limit(crate::Limit::Propagations(if let Some(limit) = limit {
            i64::from(limit)
        } else {
            -1
        }));
        Ok(())
    }
}

impl rustsat::solvers::GetInternalStats for Minisat {
    fn propagations(&self) -> usize {
        unsafe { crate::ffi::cminisatsimp_propagations(self.handle) }
            .try_into()
            .unwrap()
    }

    fn decisions(&self) -> usize {
        unsafe { crate::ffi::cminisatsimp_decisions(self.handle) }
            .try_into()
            .unwrap()
    }

    fn conflicts(&self) -> usize {
        unsafe { crate::ffi::cminisatsimp_conflicts(self.handle) }
            .try_into()
            .unwrap()
    }
}

impl rustsat::solvers::Propagate for Minisat {
    fn propagate(
        &mut self,
        assumps: &[Lit],
        phase_saving: bool,
    ) -> anyhow::Result<rustsat::solvers::PropagateResult> {
        let start = rustsat::utils::Timer::now();
        self.state = crate::InternalSolverState::Input;
        // Propagate with minisat backend
        let mut props = Vec::new();
        let ptr: *mut Vec<Lit> = &raw mut props;
        let res = crate::handle_oom!(unsafe {
            crate::ffi::cminisatsimp_propcheck(
                self.handle,
                assumps.as_ptr().cast(),
                assumps.len(),
                c_int::from(phase_saving),
                Some(crate::ffi::rustsat_minisat_collect_lits),
                ptr.cast::<std::os::raw::c_void>(),
            )
        });
        self.stats.cpu_solve_time += start.elapsed();
        match res {
            10 => Ok(rustsat::solvers::PropagateResult {
                propagated: props,
                conflict: false,
            }),
            20 => Ok(rustsat::solvers::PropagateResult {
                propagated: props,
                conflict: true,
            }),
            value => Err(crate::InvalidApiReturn {
                api_call: "cminisatsimp_propcheck",
                value,
            }
            .into()),
        }
    }
}

impl rustsat::solvers::SolveStats for Minisat {
    fn stats(&self) -> rustsat::solvers::SolverStats {
        let mut stats = self.stats.clone();
        stats.max_var = self.max_var();
        stats.n_clauses = self.n_clauses();
        stats
    }

    fn max_var(&self) -> Option<Var> {
        let max_var_idx = unsafe { crate::ffi::cminisatsimp_n_vars(self.handle) };
        if max_var_idx > 0 {
            Some(Var::new(
                (max_var_idx - 1)
                    .try_into()
                    .expect("got negative number of vars from minisat"),
            ))
        } else {
            None
        }
    }

    fn n_clauses(&self) -> usize {
        unsafe { crate::ffi::cminisatsimp_n_clauses(self.handle) }
            .try_into()
            .unwrap()
    }
}

impl Drop for Minisat {
    fn drop(&mut self) {
        unsafe { crate::ffi::cminisatsimp_release(self.handle) }
    }
}

#[cfg(test)]
mod test {
    use super::Minisat;
    use rustsat::{
        lit,
        solvers::{Solve, SolveStats},
        var,
    };

    rustsat_solvertests::basic_unittests!(Minisat, "Minisat [major].[minor].[patch]");
    rustsat_solvertests::freezing_unittests!(Minisat);
    rustsat_solvertests::propagating_unittests!(Minisat);

    #[test]
    fn backend_stats() {
        let mut solver = Minisat::default();
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
