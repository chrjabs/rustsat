//! # Low-Level Foreign Function Interface

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

use core::ffi::{c_int, c_void};

use rustsat::{solvers::ControlSignal, types::Lit, utils::from_raw_parts_maybe_null};

use super::{LearnCallbackPtr, TermCallbackPtr};

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// Raw callbacks forwarding to user callbacks
pub unsafe extern "C" fn rustsat_ccadical_terminate_cb(ptr: *mut c_void) -> c_int {
    let cb = &mut *ptr.cast::<TermCallbackPtr<'_>>();
    match cb() {
        ControlSignal::Continue => 0,
        ControlSignal::Terminate => 1,
    }
}

pub unsafe extern "C" fn rustsat_ccadical_learn_cb(ptr: *mut c_void, clause: *mut c_int) {
    let cb = &mut *ptr.cast::<LearnCallbackPtr<'_>>();

    let mut cnt: usize = 0;
    while *clause.offset(isize::try_from(cnt).expect("learned clauses is longer than `isize::MAX`"))
        != 0
    {
        cnt += 1;
    }
    let int_slice = from_raw_parts_maybe_null(clause, cnt);
    let clause = int_slice
        .iter()
        .map(|il| Lit::from_ipasir(*il).expect("Invalid literal in learned clause from CaDiCaL"))
        .collect();
    cb(clause);
}

pub unsafe extern "C" fn rustsat_cadical_collect_lits(vec: *mut c_void, lit: c_int) {
    let vec = vec.cast::<Vec<Lit>>();
    let lit = Lit::from_ipasir(lit).expect("got invalid IPASIR lit from CaDiCaL");
    (*vec).push(lit);
}

#[cfg(cadical_feature = "proof-tracer")]
pub mod prooftracer {
    use std::os::raw::{c_int, c_void};

    use rustsat::{types::Lit, utils::from_raw_parts_maybe_null};

    use crate::CaDiCaLAssignment;

    use super::super::{CaDiCaLClause, ClauseId, Conclusion, TraceProof};

    pub const DISPATCH_CALLBACKS: super::CCaDiCaLTraceCallbacks = super::CCaDiCaLTraceCallbacks {
        add_original_clause: Some(rustsat_ccadical_add_original_clause),
        add_derived_clause: Some(rustsat_ccadical_add_derived_clause),
        delete_clause: Some(rustsat_ccadical_delete_clause),
        weaken_minus: Some(rustsat_ccadical_weaken_minus),
        strengthen: Some(rustsat_ccadical_strengthen),
        report_status: Some(rustsat_ccadical_report_status),
        finalize_clause: Some(rustsat_ccadical_finalize_clause),
        begin_proof: Some(rustsat_ccadical_begin_proof),
        solve_query: Some(rustsat_ccadical_solve_query),
        add_assumption: Some(rustsat_ccadical_add_assumption),
        add_constraint: Some(rustsat_ccadical_add_constraint),
        reset_assumptions: Some(rustsat_ccadical_reset_assumptions),
        add_assumption_clause: Some(rustsat_ccadical_add_assumption_clause),
        conclude_unsat: Some(rustsat_ccadical_conclude_unsat),
        conclude_sat: Some(rustsat_ccadical_conclude_sat),
    };

    unsafe extern "C" fn rustsat_ccadical_add_original_clause(
        tracer: *mut c_void,
        id: u64,
        redundant: bool,
        cl_len: usize,
        cl_data: *const c_int,
        restored: bool,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.add_original_clause(ClauseId(id), redundant, &clause, restored);
    }

    unsafe extern "C" fn rustsat_ccadical_add_derived_clause(
        tracer: *mut c_void,
        id: u64,
        redundant: bool,
        cl_len: usize,
        cl_data: *const c_int,
        an_len: usize,
        an_data: *const u64,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        let antecedents = unsafe { from_raw_parts_maybe_null(an_data.cast::<ClauseId>(), an_len) };
        tracer.add_derived_clause(ClauseId(id), redundant, &clause, antecedents);
    }

    unsafe extern "C" fn rustsat_ccadical_delete_clause(
        tracer: *mut c_void,
        id: u64,
        redundant: bool,
        cl_len: usize,
        cl_data: *const c_int,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.delete_clause(ClauseId(id), redundant, &clause);
    }

    unsafe extern "C" fn rustsat_ccadical_weaken_minus(
        tracer: *mut c_void,
        id: u64,
        cl_len: usize,
        cl_data: *const c_int,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.weaken_minus(ClauseId(id), &clause);
    }

    unsafe extern "C" fn rustsat_ccadical_strengthen(tracer: *mut c_void, id: u64) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        tracer.strengthen(ClauseId(id));
    }

    unsafe extern "C" fn rustsat_ccadical_report_status(
        tracer: *mut c_void,
        status: c_int,
        id: u64,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let status = match status {
            0 => rustsat::solvers::SolverResult::Interrupted,
            10 => rustsat::solvers::SolverResult::Sat,
            20 => rustsat::solvers::SolverResult::Unsat,
            _ => panic!(
                "proof tracer (`report_status`) received unexpected status from CaDiCaL: {status}"
            ),
        };
        tracer.report_status(status, ClauseId(id));
    }

    unsafe extern "C" fn rustsat_ccadical_finalize_clause(
        tracer: *mut c_void,
        id: u64,
        cl_len: usize,
        cl_data: *const c_int,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.finalize_clause(ClauseId(id), &clause);
    }

    unsafe extern "C" fn rustsat_ccadical_begin_proof(tracer: *mut c_void, id: u64) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        tracer.begin_proof(ClauseId(id));
    }

    unsafe extern "C" fn rustsat_ccadical_solve_query(tracer: *mut c_void) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        tracer.solve_query();
    }

    unsafe extern "C" fn rustsat_ccadical_add_assumption(tracer: *mut c_void, assump: c_int) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        tracer.add_assumption(
            Lit::from_ipasir(assump).expect("proof tracer got invalid literal from CaDiCaL"),
        );
    }

    unsafe extern "C" fn rustsat_ccadical_add_constraint(
        tracer: *mut c_void,
        cl_len: usize,
        cl_data: *const c_int,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.add_constraint(&clause);
    }

    unsafe extern "C" fn rustsat_ccadical_reset_assumptions(tracer: *mut c_void) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        tracer.reset_assumptions();
    }

    unsafe extern "C" fn rustsat_ccadical_add_assumption_clause(
        tracer: *mut c_void,
        id: u64,
        cl_len: usize,
        cl_data: *const c_int,
        an_len: usize,
        an_data: *const u64,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        let antecedents = unsafe { from_raw_parts_maybe_null(an_data.cast::<ClauseId>(), an_len) };
        tracer.add_assumption_clause(ClauseId(id), &clause, antecedents);
    }

    unsafe extern "C" fn rustsat_ccadical_conclude_unsat(
        tracer: *mut c_void,
        concl: super::CCaDiCaLConclusionType,
        fail_len: usize,
        fail_data: *const u64,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let failing = from_raw_parts_maybe_null(fail_data.cast::<ClauseId>(), fail_len);
        let concl = match concl {
            super::CCaDiCaLConclusionType_CONFLICT => Conclusion::Conflict,
            super::CCaDiCaLConclusionType_ASSUMPTIONS => Conclusion::Assumptions,
            super::CCaDiCaLConclusionType_CONSTRAINT => Conclusion::Constraint,
            _ => panic!("proof tracer (`conclude_unsat`) received unexpected conclusion type from CaDiCaL: {concl}")
        };
        tracer.conclude_unsat(concl, failing);
    }

    unsafe extern "C" fn rustsat_ccadical_conclude_sat(
        tracer: *mut c_void,
        sol_len: usize,
        sol_data: *const c_int,
    ) {
        let tracer = &mut **tracer.cast::<*mut dyn TraceProof>();
        let assignment = CaDiCaLAssignment::new(sol_len, sol_data);
        tracer.conclude_sat(&assignment);
    }
}

#[cfg(cadical_feature = "ipasir-up")]
pub mod ipasirup {
    use std::os::raw::{c_int, c_void};

    use rustsat::types::{Assignment, Clause, Lit};

    use crate::ExternalPropagate;

    pub struct Data {
        pub prop: *mut dyn ExternalPropagate,
        reason_buffer: Option<Clause>,
        external_buffer: Option<Clause>,
    }

    impl Data {
        pub fn new(prop: *mut dyn ExternalPropagate) -> Self {
            Self {
                prop,
                reason_buffer: None,
                external_buffer: None,
            }
        }
    }

    pub const DISPATCH_CALLBACKS: super::CCaDiCaLExternalPropagatorCallbacks =
        super::CCaDiCaLExternalPropagatorCallbacks {
            notify_assignment: Some(rustsat_cadical_notify_assignment),
            notify_new_decision_level: Some(rustsat_cadical_notify_new_decision_level),
            notify_backtrack: Some(rustsat_cadical_notify_backtrack),
            cb_check_found_model: Some(rustsat_cadical_cb_check_found_model),
            cb_decide: Some(rustsat_cadical_cb_decide),
            cb_propagate: Some(rustsat_cadical_cb_propagate),
            cb_add_reason_clause_lit: Some(rustsat_cadical_cb_add_reason_clause_lit),
            cb_has_external_clause: Some(rustsat_cadical_cb_has_external_clause),
            cb_add_external_clause_lit: Some(rustsat_cadical_cb_add_external_clause_lit),
        };

    #[cfg(not(cadical_feature = "old-ipasir-up"))]
    unsafe extern "C" fn rustsat_cadical_notify_assignment(
        data: *mut c_void,
        lits: *const c_int,
        len: usize,
    ) {
        let c_lits = std::slice::from_raw_parts(lits, len);
        let mut lits = Vec::with_capacity(len);
        for c_lit in c_lits {
            lits.push(
                Lit::from_ipasir(c_lit).expect("external propagator got invalid lit from CaDiCaL"),
            );
        }
        (*(*data.cast::<Data>()).prop).assignment(&lits)
    }

    #[cfg(cadical_feature = "old-ipasir-up")]
    unsafe extern "C" fn rustsat_cadical_notify_assignment(
        data: *mut c_void,
        lit: c_int,
        _is_fixed: c_int,
    ) {
        (*(*data.cast::<Data>()).prop).assignment([
            Lit::from_ipasir(lit).expect("external propagator got invalid lit from CaDiCaL")
        ])
    }

    unsafe extern "C" fn rustsat_cadical_notify_new_decision_level(data: *mut c_void) {
        (*(*data.cast::<Data>()).prop).new_decision_level()
    }

    unsafe extern "C" fn rustsat_cadical_notify_backtrack(data: *mut c_void, new_level: usize) {
        (*(*data.cast::<Data>()).prop).backtrack(new_level)
    }

    unsafe extern "C" fn rustsat_cadical_cb_check_found_model(
        data: *mut c_void,
        model: *const c_int,
        model_len: usize,
    ) -> c_int {
        let model = std::slice::from_raw_parts(model, model_len);
        let sol: Assignment = model
            .iter()
            .map(|&l| {
                Lit::from_ipasir(l).expect("external propagator got invalid lit from CaDiCaL")
            })
            .collect();
        c_int::from((*(*data.cast::<Data>()).prop).check_found_solution(&sol))
    }

    unsafe extern "C" fn rustsat_cadical_cb_decide(data: *mut c_void) -> c_int {
        (*(*data.cast::<Data>()).prop)
            .decide()
            .map(Lit::to_ipasir)
            .unwrap_or(0)
    }

    unsafe extern "C" fn rustsat_cadical_cb_propagate(data: *mut c_void) -> c_int {
        (*(*data.cast::<Data>()).prop)
            .propagate()
            .map(Lit::to_ipasir)
            .unwrap_or(0)
    }

    unsafe extern "C" fn rustsat_cadical_cb_add_reason_clause_lit(
        data: *mut c_void,
        propagated_lit: c_int,
    ) -> c_int {
        todo!()
    }

    unsafe extern "C" fn rustsat_cadical_cb_has_external_clause(data: *mut c_void) -> c_int {
        todo!()
    }

    unsafe extern "C" fn rustsat_cadical_cb_add_external_clause_lit(data: *mut c_void) -> c_int {
        todo!()
    }
}
