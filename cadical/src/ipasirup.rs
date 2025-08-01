//! # IPASIR-UP Interface

use std::{
    marker::PhantomData,
    os::raw::{c_int, c_void},
};

use rustsat::types::{Assignment, Clause, Lit, Var};

use crate::ffi;

/// Trait representing the IPASIR-UP interface
pub trait ExternalPropagate {
    /// True if the propagator only checks complete assignments
    const IS_LAZY: bool = false;

    /// True if reason external clauses can be deleted
    const HAS_FORGETTABLE_REASONS: bool = false;

    /// Notify the propagator about assignments to observed variables. The notification is not
    /// necessarily eager. It usually happens before the call of propagator callbacks and when a
    /// driving clause is leading to an assignment.
    fn assignment(&mut self, lits: AssignmentIter<'_>);

    /// Notify the propagator about a new decision level
    fn new_decision_level(&mut self);

    /// Notify the propagator of backtracking to a given level
    fn backtrack(&mut self, new_level: usize);

    /// Checks the satisfiability of the current model
    ///
    /// # Requirements
    ///
    /// If this method is implemented differently from the default implementation,
    /// [`Self::external_clause`] also needs to be implemented.
    #[must_use]
    fn check_found_solution(&mut self, _solution: &Assignment) -> bool {
        true
    }

    /// Ask the external propagator for the next decision literal. If it returns 0, the solver
    /// makes its own choice.
    #[must_use]
    fn decide(&mut self) -> Option<Lit> {
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
    fn propagate(&mut self) -> Option<Lit> {
        None
    }

    /// Ask the external propagator for the reason clause of a previous external propagation step
    /// (done by `propagate`). The clause must contain the propagated literal.
    #[must_use]
    #[allow(unused_variables)]
    fn reason_clause(&mut self, propagated_lit: Lit) -> Clause {
        Clause::default()
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
    fn external_clause(&mut self) -> Option<ExternalClause> {
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
    #[cfg(not(cadical_feature = "old-ipasir-up"))]
    #[must_use]
    pub fn forgettable(clause: Clause) -> Self {
        ExternalClause {
            clause,
            forgettable: false,
        }
    }
}

/// A handle to an attached external propagator in order to be able to detach it again
#[must_use = "memory is leaked when not explicitly disconnecting a propagator"]
#[derive(Debug)]
pub struct PropagatorHandle<Prop>(*mut ffi::ipasirup::Data, PhantomData<Prop>);

impl super::CaDiCaL<'_, '_> {
    /// Connects an external propagator to the solver
    ///
    /// The returned handle allows for disconnecting the propagator again via
    /// [`Self::disconnect_propagator`].
    ///
    /// Only one propagator can be connected at a time,
    ///
    /// **Note**: If the propagator is not explicitly disconnected, its memory is leaked.
    // FIXME: consider storing the propagator handle and freeing it if the solver is dropped
    pub fn connect_propagator<Prop>(&mut self, propagator: Prop) -> PropagatorHandle<Prop>
    where
        Prop: ExternalPropagate + 'static,
    {
        let propagator: Box<dyn DynCompatExternalPropagate> = Box::new(propagator);
        let propagator = Box::into_raw(propagator);
        let data = Box::new(ffi::ipasirup::Data::new(propagator));
        let data = Box::into_raw(data);
        unsafe {
            ffi::ccadical_connect_external_propagator(
                self.handle,
                data.cast::<c_void>(),
                ffi::ipasirup::DISPATCH_CALLBACKS,
                c_int::from(Prop::IS_LAZY),
                c_int::from(Prop::HAS_FORGETTABLE_REASONS),
            );
        };
        PropagatorHandle(data, PhantomData)
    }

    /// Disconnects an external propagator from the solver
    ///
    /// Disconnecting a propagator resets all observed variables
    #[allow(clippy::needless_pass_by_value)]
    pub fn disconnect_propagator<Prop>(&mut self, handle: PropagatorHandle<Prop>) -> Prop {
        unsafe { ffi::ccadical_disconnect_external_propagator(self.handle) };
        let data = unsafe { Box::from_raw(handle.0) };
        *unsafe { Box::from_raw(data.prop.cast::<Prop>()) }
    }

    /// Marks a variable as observed by the external propagator
    pub fn add_observed_var(&mut self, var: Var) {
        unsafe { ffi::ccadical_add_observed_var(self.handle, var.to_ipasir()) };
    }

    /// Marks a variable as not observed by the external propagator
    pub fn remove_observed_var(&mut self, var: Var) {
        unsafe { ffi::ccadical_remove_observed_var(self.handle, var.to_ipasir()) };
    }

    /// Resets all variable observed by the external propagator
    pub fn reset_observed_vars(&mut self) {
        unsafe { ffi::ccadical_reset_observed_vars(self.handle) };
    }

    /// If `var` is an observed variable and was assigned by a decision during solving, returns
    /// `true`, otherwise `false`
    #[must_use]
    pub fn is_decision(&self, lit: Lit) -> bool {
        unsafe { ffi::ccadical_is_decision(self.handle, lit.to_ipasir()) != 0 }
    }
}

/// Dyn-compatible version of the [`ExternalPropagate`] trait for internal use
///
/// This does not have access to the associated consts
pub(crate) trait DynCompatExternalPropagate {
    fn assignment(&mut self, lits: AssignmentIter<'_>);
    fn new_decision_level(&mut self);
    fn backtrack(&mut self, new_level: usize);
    #[must_use]
    fn check_found_solution(&mut self, solution: &Assignment) -> bool;
    #[must_use]
    fn decide(&mut self) -> Option<Lit>;
    #[must_use]
    fn propagate(&mut self) -> Option<Lit>;
    #[must_use]
    #[allow(unused_variables)]
    fn reason_clause(&mut self, propagated_lit: Lit) -> Clause;
    #[must_use]
    fn external_clause(&mut self) -> Option<ExternalClause>;
}

impl<Prop> DynCompatExternalPropagate for Prop
where
    Prop: ExternalPropagate,
{
    fn assignment(&mut self, lits: AssignmentIter<'_>) {
        ExternalPropagate::assignment(self, lits);
    }

    fn new_decision_level(&mut self) {
        ExternalPropagate::new_decision_level(self);
    }

    fn backtrack(&mut self, new_level: usize) {
        ExternalPropagate::backtrack(self, new_level);
    }

    fn check_found_solution(&mut self, solution: &Assignment) -> bool {
        ExternalPropagate::check_found_solution(self, solution)
    }

    fn decide(&mut self) -> Option<Lit> {
        ExternalPropagate::decide(self)
    }

    fn propagate(&mut self) -> Option<Lit> {
        ExternalPropagate::propagate(self)
    }

    fn reason_clause(&mut self, propagated_lit: Lit) -> Clause {
        ExternalPropagate::reason_clause(self, propagated_lit)
    }

    fn external_clause(&mut self) -> Option<ExternalClause> {
        ExternalPropagate::external_clause(self)
    }
}
