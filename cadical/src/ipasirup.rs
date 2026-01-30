//! # IPASIR-UP Interface

use std::{
    marker::PhantomData,
    os::raw::{c_int, c_void},
    pin::Pin,
};

use rustsat::{
    clause,
    solvers::sat,
    types::{Assignment, Clause, Lit, Var},
};

use crate::ffi;

/// Trait representing the IPASIR-UP interface
pub trait ExternalPropagate: From<Self::Config> + Unpin + 'static {
    /// True if the propagator only checks complete assignments
    const IS_LAZY: bool = false;

    /// True if reason external clauses can be deleted
    const HAS_FORGETTABLE_REASONS: bool = false;

    /// A configuration type that the propagator can be constructed from
    type Config;

    /// Notify the propagator about assignments to observed variables. The notification is not
    /// necessarily eager. It usually happens before the call of propagator callbacks and when a
    /// driving clause is leading to an assignment.
    fn assignment(&mut self, lits: AssignmentIter<'_>, context: &mut SolvingContext);

    /// Notify the propagator about a new decision level
    fn new_decision_level(&mut self, context: &mut SolvingContext);

    /// Notify the propagator of backtracking to a given level
    fn backtrack(&mut self, new_level: usize, context: &mut SolvingContext);

    /// Checks the satisfiability of the current model
    ///
    /// # Requirements
    ///
    /// If this method is implemented differently from the default implementation,
    /// [`Self::external_clause`] also needs to be implemented.
    #[must_use]
    fn check_found_solution(
        &mut self,
        _solution: &Assignment,
        _context: &mut BacktrackableContext,
    ) -> bool {
        true
    }

    /// Ask the external propagator for the next decision literal. If it returns 0, the solver
    /// makes its own choice.
    #[must_use]
    fn decide(&mut self, _context: &mut BacktrackableContext) -> Option<Lit> {
        None
    }

    /// Ask the external propagator if there is an external propagation to make under the current
    /// assignment. It returns either a literal to be propagated or 0, indicating that there is no
    /// external propagation under the current assignment.
    ///
    /// # Requirements
    ///
    /// If this method is implemented differently from the default implementation,
    /// [`Self::reason_clause`] also needs to be implemented.
    #[must_use]
    fn propagate(&mut self, _context: &mut SolvingContext) -> Option<Lit> {
        None
    }

    /// Ask the external propagator for the reason clause of a previous external propagation step
    /// (done by `propagate`). The clause must contain the propagated literal.
    #[must_use]
    fn reason_clause(&mut self, propagated_lit: Lit, _context: &mut SolvingContext) -> Clause {
        clause![propagated_lit]
    }

    /// The solver queries the external propagator whether there is an external clause to be added
    ///
    /// The clause can be arbitrary, but if it is root-satisfied or tautology, the solver will
    /// ignore it without learning it. Root-falsified literals are eagerly removed from the clause.
    /// Falsified clauses trigger conflict analysis, propagating clauses trigger propagation. In
    /// case chrono is 0, the solver backtracks to propagate the new literal on the right decision
    /// level, otherwise it potentially will be an out-of-order assignment on the current level.
    /// Unit clauses always (unless root-satisfied, see above) trigger backtracking (independently
    /// from the value of the chrono option and independently from being falsified or satisfied or
    /// unassigned) to level 0. Empty clause (or root falsified clause, see above) makes the
    /// problem unsat and stops the search immediately.
    #[must_use]
    fn external_clause(&mut self, _context: &mut SolvingContext) -> Option<ExternalClause> {
        None
    }
}

type InnerAssignmentIter<'a> =
    std::iter::Map<std::iter::Copied<std::slice::Iter<'a, c_int>>, fn(c_int) -> Lit>;

/// An iterator over literals that have been assigned in the solver
#[derive(Debug, Clone)]
pub struct AssignmentIter<'a>(InnerAssignmentIter<'a>);

impl<'a> AssignmentIter<'a> {
    pub(crate) fn new(lits: &'a [c_int]) -> Self {
        Self(lits.iter().copied().map(ffi::ipasirup::from_ipasir_panic))
    }
}

impl Iterator for AssignmentIter<'_> {
    type Item = Lit;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

impl DoubleEndedIterator for AssignmentIter<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back()
    }
}

/// An external clause with associated information
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalClause {
    pub(crate) clause: Clause,
    pub(crate) forgettable: bool,
}

impl ExternalClause {
    /// Creates a new, unforgettable external clasue
    #[must_use]
    pub fn unforgettable(clause: Clause) -> Self {
        ExternalClause {
            clause,
            forgettable: false,
        }
    }

    /// Creates a new, unforgettable external clasue
    #[cfg(cadical_version = "v2.1")]
    #[must_use]
    pub fn forgettable(clause: Clause) -> Self {
        ExternalClause {
            clause,
            forgettable: false,
        }
    }
}

/// Allows access to CaDiCaL's `force_backtrack` function, as well as other functions that are only
/// valid in its `SOLVING` state
#[derive(Debug)]
pub struct BacktrackableContext {
    handle: *mut ffi::CCaDiCaL,
}

impl BacktrackableContext {
    pub(crate) fn new(handle: *mut ffi::CCaDiCaL) -> Self {
        Self { handle }
    }

    /// Marks a variable as observed by the external propagator
    pub fn add_observed_var(&mut self, var: Var) {
        unsafe { ffi::ccadical_add_observed_var(self.handle, var.to_ipasir()) };
    }

    /// Marks a variable as not observed by the external propagator
    #[cfg(cadical_version = "v2.2")]
    pub fn remove_observed_var(&mut self, var: Var) {
        unsafe { ffi::ccadical_remove_observed_var(self.handle, var.to_ipasir()) };
    }

    /// Resets all variable observed by the external propagator
    #[cfg(cadical_version = "v2.2")]
    pub fn reset_observed_vars(&mut self) {
        unsafe { ffi::ccadical_reset_observed_vars(self.handle) };
    }

    /// If `var` is an observed variable and was assigned by a decision during solving, returns
    /// `true`, otherwise `false`
    #[must_use]
    pub fn is_decision(&self, lit: Lit) -> bool {
        unsafe { ffi::ccadical_is_decision(self.handle, lit.to_ipasir()) != 0 }
    }

    /// Gets the number of variables in the solver
    pub fn n_vars(&self) -> u32 {
        u32::try_from(unsafe { ffi::ccadical_vars(self.handle) })
            .expect("number of variables should always be non-negative and fit in `u32`")
    }

    /// Terminates solving
    pub fn terminate(&mut self) {
        unsafe { ffi::ccadical_terminate(self.handle) }
    }

    /// Terminates solving
    #[cfg(cadical_version = "v2.2")]
    pub fn force_backtrack(&mut self, new_level: u32) {
        let new_level = c_int::try_from(new_level).expect("`new_level` should fit in `c_int`");
        unsafe { ffi::ccadical_force_backtrack(self.handle, new_level) }
    }
}

/// Allows access to CaDiCaL functions that are only valid in its `SOLVING` state
#[derive(Debug)]
pub struct SolvingContext {
    handle: *mut ffi::CCaDiCaL,
}

impl SolvingContext {
    pub(crate) fn new(handle: *mut ffi::CCaDiCaL) -> Self {
        Self { handle }
    }

    /// Marks a variable as observed by the external propagator
    pub fn add_observed_var(&mut self, var: Var) {
        unsafe { ffi::ccadical_add_observed_var(self.handle, var.to_ipasir()) };
    }

    /// Marks a variable as not observed by the external propagator
    #[cfg(cadical_version = "v2.2")]
    pub fn remove_observed_var(&mut self, var: Var) {
        unsafe { ffi::ccadical_remove_observed_var(self.handle, var.to_ipasir()) };
    }

    /// Resets all variable observed by the external propagator
    #[cfg(cadical_version = "v2.2")]
    pub fn reset_observed_vars(&mut self) {
        unsafe { ffi::ccadical_reset_observed_vars(self.handle) };
    }

    /// If `var` is an observed variable and was assigned by a decision during solving, returns
    /// `true`, otherwise `false`
    #[must_use]
    pub fn is_decision(&self, lit: Lit) -> bool {
        unsafe { ffi::ccadical_is_decision(self.handle, lit.to_ipasir()) != 0 }
    }

    /// Gets the number of variables in the solver
    pub fn n_vars(&self) -> u32 {
        u32::try_from(unsafe { ffi::ccadical_vars(self.handle) })
            .expect("number of variables should always be non-negative and fit in `u32`")
    }

    /// Terminates solving
    pub fn terminate(&mut self) {
        unsafe { ffi::ccadical_terminate(self.handle) }
    }
}

/// Dyn-compatible version of the [`ExternalPropagate`] trait for internal use
///
/// This does not have access to the associated consts
pub(crate) trait DynCompatExternalPropagate {
    fn assignment(&mut self, lits: AssignmentIter<'_>, context: &mut SolvingContext);
    fn new_decision_level(&mut self, context: &mut SolvingContext);
    fn backtrack(&mut self, new_level: usize, context: &mut SolvingContext);
    #[must_use]
    fn check_found_solution(
        &mut self,
        solution: &Assignment,
        context: &mut BacktrackableContext,
    ) -> bool;
    #[must_use]
    fn decide(&mut self, context: &mut BacktrackableContext) -> Option<Lit>;
    #[must_use]
    fn propagate(&mut self, context: &mut SolvingContext) -> Option<Lit>;
    #[must_use]
    #[allow(unused_variables)]
    fn reason_clause(&mut self, propagated_lit: Lit, context: &mut SolvingContext) -> Clause;
    #[must_use]
    fn external_clause(&mut self, context: &mut SolvingContext) -> Option<ExternalClause>;
}

impl<Prop> DynCompatExternalPropagate for Prop
where
    Prop: ExternalPropagate,
{
    fn assignment(&mut self, lits: AssignmentIter<'_>, context: &mut SolvingContext) {
        ExternalPropagate::assignment(self, lits, context);
    }

    fn new_decision_level(&mut self, context: &mut SolvingContext) {
        ExternalPropagate::new_decision_level(self, context);
    }

    fn backtrack(&mut self, new_level: usize, context: &mut SolvingContext) {
        ExternalPropagate::backtrack(self, new_level, context);
    }

    fn check_found_solution(
        &mut self,
        solution: &Assignment,
        context: &mut BacktrackableContext,
    ) -> bool {
        ExternalPropagate::check_found_solution(self, solution, context)
    }

    fn decide(&mut self, context: &mut BacktrackableContext) -> Option<Lit> {
        ExternalPropagate::decide(self, context)
    }

    fn propagate(&mut self, context: &mut SolvingContext) -> Option<Lit> {
        ExternalPropagate::propagate(self, context)
    }

    fn reason_clause(&mut self, propagated_lit: Lit, context: &mut SolvingContext) -> Clause {
        ExternalPropagate::reason_clause(self, propagated_lit, context)
    }

    fn external_clause(&mut self, context: &mut SolvingContext) -> Option<ExternalClause> {
        ExternalPropagate::external_clause(self, context)
    }
}

/// Interface to the CaDiCaL solver when an external propagator is attached
#[derive(Debug)]
pub struct CaDiCaLWithPropagator<Propagator> {
    solver: PhantomData<super::CaDiCaLNewApi>,
    propagator: PhantomData<Propagator>,
}

/// A CaDiCaL Solver in different States with a propagator attached
#[derive(Debug)]
pub struct CaDiCaLWithPropagatorState<State, Propagator> {
    solver: super::CaDiCaLState<State>,
    propagator: Pin<Box<Propagator>>,
    /// NOTE: the pointer in this will always point to the propagator
    ipasirup_data: Pin<Box<ffi::ipasirup::Data>>,
}

unsafe impl<State, Propagator> Send for CaDiCaLWithPropagatorState<State, Propagator>
where
    State: Send,
    Propagator: Send,
{
}

/// A CaDiCaL Solver in its initialization state with a propagator that will be attached
#[derive(Debug)]
pub struct CaDiCaLWithPropagatorInitState<Propagator> {
    solver: super::CaDiCaLState<super::Init>,
    propagator: Propagator,
}

impl<Propagator> sat::Solve for CaDiCaLWithPropagator<Propagator>
where
    Propagator: ExternalPropagate,
{
    type Init = CaDiCaLWithPropagatorInitState<Propagator>;
    type Input = CaDiCaLWithPropagatorState<super::Input, Propagator>;
    type Sat = CaDiCaLWithPropagatorState<super::Sat, Propagator>;
    type Unsat = CaDiCaLWithPropagatorState<super::Unsat, Propagator>;
    type Unknown = CaDiCaLWithPropagatorState<super::Unknown, Propagator>;

    fn signature() -> &'static str {
        super::CaDiCaLNewApi::signature()
    }
}

impl<Propagator> sat::SolveIncremental for CaDiCaLWithPropagator<Propagator>
where
    Propagator: ExternalPropagate,
{
    type SatGuard<'a> = super::CaDiCaLGuard<'a, super::Sat>;
    type UnsatGuard<'a> = super::CaDiCaLGuard<'a, super::Unsat>;
    type UnknownGuard<'a> = super::CaDiCaLGuard<'a, super::Unknown>;
}

impl<Propagator> sat::Init for CaDiCaLWithPropagatorInitState<Propagator>
where
    Propagator: ExternalPropagate,
{
    type Config = (super::Config, Propagator::Config);

    type Option = ();

    fn set_option(&mut self, option: Self::Option) -> &mut Self {
        todo!()
    }
}

impl<Propagator> From<(super::Config, Propagator::Config)>
    for CaDiCaLWithPropagatorInitState<Propagator>
where
    Propagator: ExternalPropagate,
{
    fn from((solver_cfg, propagator_cfg): (super::Config, Propagator::Config)) -> Self {
        Self {
            solver: solver_cfg.into(),
            propagator: propagator_cfg.into(),
        }
    }
}

impl<Propagator> CaDiCaLWithPropagatorState<super::Input, Propagator>
where
    Propagator: ExternalPropagate,
{
    /// Disconnects the connected external propagator
    #[must_use]
    pub fn disconnect_propagator(self) -> (super::CaDiCaLState<super::Input>, Propagator) {
        // SAFETY: this is the only way the user can get the propagator back and it can be moved in
        // memory, so we need to disconnect it here
        unsafe { ffi::ccadical_disconnect_external_propagator(self.solver.handle.0) };
        let propagator = *Pin::into_inner(self.propagator);
        (self.solver, propagator)
    }

    /// Gets a reference to the propagator
    #[must_use]
    pub fn propagator(&self) -> &Propagator {
        &self.propagator
    }

    /// Gets a mutable reference to the propagator
    pub fn propagator_mut(&mut self) -> &mut Propagator {
        &mut self.propagator
    }

    /// Gets a reference to the solver and the propagator
    #[must_use]
    pub fn solver_and_propagator(&self) -> (&super::CaDiCaLState<super::Input>, &Propagator) {
        (&self.solver, &self.propagator)
    }

    /// Gets a mutable reference to the solver and the propagator
    pub fn solver_and_propagator_mut(
        &mut self,
    ) -> (&mut super::CaDiCaLState<super::Input>, &mut Propagator) {
        (&mut self.solver, &mut self.propagator)
    }

    /// Gets a reference to the propagator
    #[deprecated(
        note = "All functionality of the solver should be exposed on the wrapper type. If you find a need to use this method, please open an issue at https://github.com/chrjabs/rustsat"
    )]
    #[must_use]
    pub fn solver(&self) -> &super::CaDiCaLState<super::Input> {
        &self.solver
    }

    /// Gets a mutable reference to the propagator
    #[deprecated(
        note = "All functionality of the solver should be exposed on the wrapper type. If you find a need to use this method, please open an issue at https://github.com/chrjabs/rustsat"
    )]
    pub fn solver_mut(&mut self) -> &mut super::CaDiCaLState<super::Input> {
        &mut self.solver
    }

    /// Marks a variable as observed by the external propagator
    pub fn add_observed_var(&mut self, var: Var) {
        unsafe { ffi::ccadical_add_observed_var(self.solver.handle.0, var.to_ipasir()) };
    }

    /// Marks a variable as not observed by the external propagator
    pub fn remove_observed_var(&mut self, var: Var) {
        unsafe { ffi::ccadical_remove_observed_var(self.solver.handle.0, var.to_ipasir()) };
    }

    /// Resets all variable observed by the external propagator
    pub fn reset_observed_vars(&mut self) {
        unsafe { ffi::ccadical_reset_observed_vars(self.solver.handle.0) };
    }

    /// If `var` is an observed variable and was assigned by a decision during solving, returns
    /// `true`, otherwise `false`
    #[must_use]
    pub fn is_decision(&self, lit: Lit) -> bool {
        unsafe { ffi::ccadical_is_decision(self.solver.handle.0, lit.to_ipasir()) != 0 }
    }

    /// Gets the number of variables in the solver
    pub fn n_vars(&self) -> u32 {
        u32::try_from(unsafe { ffi::ccadical_vars(self.solver.handle.0) })
            .expect("number of variables should always be non-negative and fit in `u32`")
    }

    fn wrap(solver: super::CaDiCaLState<super::Input>, propagator: Propagator) -> Self {
        let mut propagator = Box::pin(propagator);
        let pointer: *mut dyn DynCompatExternalPropagate = &mut *propagator;
        let mut ipasirup_data = Box::pin(ffi::ipasirup::Data::new(solver.handle.0, pointer));
        let data_pointer: *mut ffi::ipasirup::Data = &mut *ipasirup_data;
        // SAFETY: The only way for the propagator to be moved is by calling
        // `disconnect_propagator`, which detaches the propagator first, so CaDiCaL doesn't have
        // access to it anymore
        unsafe {
            ffi::ccadical_connect_external_propagator(
                solver.handle.0,
                data_pointer.cast::<c_void>(),
                ffi::ipasirup::DISPATCH_CALLBACKS,
                c_int::from(Propagator::IS_LAZY),
                c_int::from(Propagator::HAS_FORGETTABLE_REASONS),
            );
        }
        Self {
            solver,
            propagator,
            ipasirup_data,
        }
    }
}

impl<Propagator> sat::Input<CaDiCaLWithPropagator<Propagator>>
    for CaDiCaLWithPropagatorState<super::Input, Propagator>
where
    Propagator: ExternalPropagate,
{
    type Option = ();

    fn set_option(&mut self, option: Self::Option) -> &mut Self {
        <super::CaDiCaLState<super::Input> as sat::Input<super::CaDiCaLNewApi>>::set_option(
            &mut self.solver,
            option,
        );
        self
    }

    fn add_clause<C>(&mut self, clause: &C) -> rustsat::MightMemout<&Self>
    where
        C: AsRef<rustsat::types::Cl> + ?Sized,
    {
        self.solver.add_clause(clause)?;
        Ok(self)
    }

    fn solve(self) -> rustsat::MightMemout<sat::SolveResult<CaDiCaLWithPropagator<Propagator>>> {
        let result = self.solver.solve()?;
        Ok(match result {
            sat::SolveResult::Sat(solver) => sat::SolveResult::Sat(CaDiCaLWithPropagatorState {
                solver,
                propagator: self.propagator,
                ipasirup_data: self.ipasirup_data,
            }),
            sat::SolveResult::Unsat(solver) => {
                sat::SolveResult::Unsat(CaDiCaLWithPropagatorState {
                    solver,
                    propagator: self.propagator,
                    ipasirup_data: self.ipasirup_data,
                })
            }
            sat::SolveResult::Unknown(solver) => {
                sat::SolveResult::Unknown(CaDiCaLWithPropagatorState {
                    solver,
                    propagator: self.propagator,
                    ipasirup_data: self.ipasirup_data,
                })
            }
        })
    }
}

impl<Propagator> rustsat::encodings::CollectClauses
    for CaDiCaLWithPropagatorState<super::Input, Propagator>
where
    Propagator: ExternalPropagate,
{
    fn n_clauses(&self) -> usize {
        self.solver.n_clauses()
    }

    fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
    where
        T: IntoIterator<Item = Clause>,
    {
        self.solver.extend_clauses(cl_iter)
    }
}

impl<Propagator> sat::SolveAssumptions<CaDiCaLWithPropagator<Propagator>>
    for CaDiCaLWithPropagatorState<super::Input, Propagator>
where
    Propagator: ExternalPropagate,
{
    fn solve_under_assumptions(
        self,
        assumptions: &[Lit],
    ) -> rustsat::MightMemout<sat::SolveResult<CaDiCaLWithPropagator<Propagator>>> {
        let result = self.solver.solve_under_assumptions(assumptions)?;
        Ok(match result {
            sat::SolveResult::Sat(solver) => sat::SolveResult::Sat(CaDiCaLWithPropagatorState {
                solver,
                propagator: self.propagator,
                ipasirup_data: self.ipasirup_data,
            }),
            sat::SolveResult::Unsat(solver) => {
                sat::SolveResult::Unsat(CaDiCaLWithPropagatorState {
                    solver,
                    propagator: self.propagator,
                    ipasirup_data: self.ipasirup_data,
                })
            }
            sat::SolveResult::Unknown(solver) => {
                sat::SolveResult::Unknown(CaDiCaLWithPropagatorState {
                    solver,
                    propagator: self.propagator,
                    ipasirup_data: self.ipasirup_data,
                })
            }
        })
    }
}

impl<Propagator> sat::SolveGuarded<CaDiCaLWithPropagator<Propagator>>
    for CaDiCaLWithPropagatorState<super::Input, Propagator>
where
    Propagator: ExternalPropagate,
{
    fn solve(
        &mut self,
    ) -> rustsat::MightMemout<sat::SolveGuard<'_, CaDiCaLWithPropagator<Propagator>>> {
        let res =
            <super::CaDiCaLState<super::Input> as sat::SolveGuarded<super::CaDiCaLNewApi>>::solve(
                &mut self.solver,
            )?;
        Ok(match res {
            sat::SolveGuard::Sat(guard) => sat::SolveGuard::Sat(guard),
            sat::SolveGuard::Unsat(guard) => sat::SolveGuard::Unsat(guard),
            sat::SolveGuard::Unknown(guard) => sat::SolveGuard::Unknown(guard),
        })
    }

    fn solve_under_assumptions(
        &mut self,
        assumptions: &[Lit],
    ) -> rustsat::MightMemout<sat::SolveGuard<'_, CaDiCaLWithPropagator<Propagator>>> {
        let res =
            <super::CaDiCaLState<super::Input> as sat::SolveGuarded<super::CaDiCaLNewApi>>::solve_under_assumptions(
                &mut self.solver,
                assumptions,
            )?;
        Ok(match res {
            sat::SolveGuard::Sat(guard) => sat::SolveGuard::Sat(guard),
            sat::SolveGuard::Unsat(guard) => sat::SolveGuard::Unsat(guard),
            sat::SolveGuard::Unknown(guard) => sat::SolveGuard::Unknown(guard),
        })
    }
}

impl<Propagator> From<CaDiCaLWithPropagatorInitState<Propagator>>
    for CaDiCaLWithPropagatorState<super::Input, Propagator>
where
    Propagator: ExternalPropagate,
{
    fn from(value: CaDiCaLWithPropagatorInitState<Propagator>) -> Self {
        Self::wrap(value.solver.into(), value.propagator)
    }
}

impl<Propagator> sat::Sat for CaDiCaLWithPropagatorState<super::Sat, Propagator>
where
    Propagator: ExternalPropagate,
{
    fn variable_value(&self, var: Var) -> rustsat::types::TernaryVal {
        self.solver.variable_value(var)
    }
}

impl<Propagator> From<CaDiCaLWithPropagatorState<super::Sat, Propagator>>
    for CaDiCaLWithPropagatorState<super::Input, Propagator>
{
    fn from(value: CaDiCaLWithPropagatorState<super::Sat, Propagator>) -> Self {
        Self {
            solver: value.solver.into(),
            propagator: value.propagator,
            ipasirup_data: value.ipasirup_data,
        }
    }
}

impl<Propagator> sat::UnsatIncremental for CaDiCaLWithPropagatorState<super::Unsat, Propagator>
where
    Propagator: ExternalPropagate,
{
    fn core(&mut self) -> &[Lit] {
        self.solver.core()
    }

    fn failed(&mut self, assumption: Lit) -> bool {
        self.solver.failed(assumption)
    }
}

impl<Propagator> From<CaDiCaLWithPropagatorState<super::Unsat, Propagator>>
    for CaDiCaLWithPropagatorState<super::Input, Propagator>
{
    fn from(value: CaDiCaLWithPropagatorState<super::Unsat, Propagator>) -> Self {
        Self {
            solver: value.solver.into(),
            propagator: value.propagator,
            ipasirup_data: value.ipasirup_data,
        }
    }
}

impl<Propagator> From<CaDiCaLWithPropagatorState<super::Unknown, Propagator>>
    for CaDiCaLWithPropagatorState<super::Input, Propagator>
{
    fn from(value: CaDiCaLWithPropagatorState<super::Unknown, Propagator>) -> Self {
        Self {
            solver: value.solver.into(),
            propagator: value.propagator,
            ipasirup_data: value.ipasirup_data,
        }
    }
}

impl super::CaDiCaLState<super::Input> {
    /// Connects an external propagator to the solver
    ///
    /// Note that CaDiCaL allows for only connecting one propagator at a time
    pub fn connect_propagator<Propagator>(
        self,
        propagator: Propagator,
    ) -> CaDiCaLWithPropagatorState<super::Input, Propagator>
    where
        Propagator: ExternalPropagate,
    {
        CaDiCaLWithPropagatorState::wrap(self, propagator)
    }
}
