//! # CaDiCaL Proof Tracing Functionality

use std::{ffi::c_void, marker::PhantomData};

use rustsat::{
    solvers::SolverResult,
    types::{Clause, Lit},
};

use crate::ffi;

/// The ID of a clause internal to CaDiCaL
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ClauseId(pub(crate) u64);

/// A conclusion for an incremental proof
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Conclusion {
    /// The solver found a conflict of the input clauses
    Conflict,
    /// The solver found the input clauses to be unsatisfiable with the assumptions
    Assumptions,
    /// The solver found the input clauses to be unsatisfiable with the temporary constraint
    Constraint,
}

/// Trait that must be implement for a type that can be used to trace a proof generated by CaDiCaL
///
/// This is the equivalent to the proof tracer C++-API of CaDiCaL
#[allow(unused_variables)]
pub trait TraceProof {
    /// Notify the tracer that a original clause has been added.
    ///
    /// Includes ID and wether the clause is redundant or irredundant
    fn add_original_clause(
        &mut self,
        id: ClauseId,
        redundant: bool,
        clause: &Clause,
        restored: bool,
    ) {
    }

    /// Notify the observer that a new clause has been derived.
    ///
    /// Includes ID and wether the clause is redundant or irredundant
    /// If antecedents are derived they will be included here.
    fn add_derived_clause(
        &mut self,
        id: ClauseId,
        redundant: bool,
        clause: &Clause,
        antecedents: &[ClauseId],
    ) {
    }

    /// Notify the observer that a clause is deleted.
    ///
    /// Includes ID and redundant/irredundant
    fn delete_clause(&mut self, id: ClauseId, redundant: bool, clause: &Clause) {}

    /// Notify the observer to remember that the clause might be restored later
    fn weaken_minus(&mut self, id: ClauseId, clause: &Clause) {}

    /// Notify the observer that a clause is strengthened
    fn strengthen(&mut self, id: ClauseId) {}

    /// Notify the observer that the solve call ends with status [`SolverResult`]
    /// If the status is UNSAT and an empty clause has been derived, the second
    /// argument will contain its id.
    /// Note that the empty clause is already added through [`TraceProof::add_derived_clause`]
    /// and finalized with [`TraceProof::finalize_clause`]
    fn report_status(&mut self, status: SolverResult, id: ClauseId) {}

    /// Notify the observer that a clause is finalized.
    fn finalize_clause(&mut self, id: ClauseId, clause: &Clause) {}

    /// Notify the observer that the proof begins with a set of reserved ids
    /// for original clauses. Given ID is the first derived clause ID.
    fn begin_proof(&mut self, id: ClauseId) {}

    /// Notify the observer that an assumption has been added
    fn solve_query(&mut self) {}

    /// Notify the observer that an assumption has been added
    fn add_assumption(&mut self, assumption: Lit) {}

    /// Notify the observer that a constraint has been added
    // Arguments: Data, length, constraint_clause
    fn add_constraint(&mut self, constraint: &Clause) {}

    /// Notify the observer that assumptions and constraints are reset
    fn reset_assumptions(&mut self) {}

    /// Notify the observer that this clause could be derived, which
    /// is the negation of a core of failing assumptions/constraints.
    /// If antecedents are derived they will be included here.
    fn add_assumption_clause(&mut self, id: ClauseId, clause: &Clause, antecedents: &[ClauseId]) {}

    /// Notify the observer that conclude unsat was requested.
    /// will give either the id of the empty clause, the id of a failing
    /// assumption clause or the ids of the failing constrain clauses
    fn conclude_unsat(&mut self, conclusion: Conclusion, failing: &[ClauseId]) {}

    /// Notify the observer that conclude sat was requested.
    /// will give the complete model as a vector.
    fn conclude_sat(&mut self, solution: &rustsat::types::Assignment) {}
}

/// A handle to an attached proof tracer in order to be able to detach it again
#[derive(Clone, Copy, Debug)]
pub struct ProofTracerHandle<PT>(*mut ffi::CCaDiCaLTracer, PhantomData<PT>);

#[derive(Clone, Copy, Debug, thiserror::Error)]
#[error("the provided proof tracer handle is not connected to the solver")]
pub struct NotConnected<PT>(ProofTracerHandle<PT>);

impl super::CaDiCaL<'_, '_> {
    /// Connects a proof tracer to the solver
    pub fn connect_proof_tracer<PT>(
        &mut self,
        tracer: PT,
        antecedents: bool,
    ) -> ProofTracerHandle<PT>
    where
        PT: TraceProof,
    {
        let tracer: Box<dyn TraceProof> = Box::new(tracer);
        let tracer = Box::into_raw(tracer);
        let ptr = unsafe {
            ffi::ccadical_connect_proof_tracer(
                self.handle,
                tracer.cast::<c_void>(),
                ffi::tracer::DISPATCH_CALLBACKS,
                antecedents,
            )
        };
        ProofTracerHandle(ptr, PhantomData)
    }

    /// Disconnects a proof tracer from the solver
    ///
    /// # Errors
    ///
    /// If the handle is not connected to the given solver, returns [`NotConnected`]
    #[allow(clippy::missing_panics_doc)]
    pub fn disconnect_proof_tracer<PT>(
        &mut self,
        handle: ProofTracerHandle<PT>,
    ) -> Result<PT, NotConnected<PT>>
    where
        PT: TraceProof + 'static,
    {
        if !unsafe { ffi::ccadical_disconnect_proof_tracer(self.handle, handle.0) } {
            return Err(NotConnected(handle));
        }
        let tracer = unsafe { ffi::ccadical_get_tracer_data(handle.0) };
        let tracer = unsafe { Box::from_raw(tracer.cast::<Box<dyn std::any::Any>>()) };
        Ok(*tracer
            .downcast::<PT>()
            .expect("could not downcast tracer to type stored in handle"))
    }
}