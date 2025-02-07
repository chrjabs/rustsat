//! # Low-Level Foreign Function Interface

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

use core::ffi::{c_int, c_void};
use std::slice;

use rustsat::{solvers::ControlSignal, types::Lit};

use super::{LearnCallbackPtr, TermCallbackPtr};

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// Raw callbacks forwarding to user callbacks
pub extern "C" fn rustsat_ccadical_terminate_cb(ptr: *mut c_void) -> c_int {
    let cb = unsafe { &mut *ptr.cast::<TermCallbackPtr<'_>>() };
    match cb() {
        ControlSignal::Continue => 0,
        ControlSignal::Terminate => 1,
    }
}

pub extern "C" fn rustsat_ccadical_learn_cb(ptr: *mut c_void, clause: *mut c_int) {
    let cb = unsafe { &mut *ptr.cast::<LearnCallbackPtr<'_>>() };

    let mut cnt = 0;
    for n in 0.. {
        if unsafe { *clause.offset(n) } != 0 {
            cnt += 1;
        }
    }
    let int_slice = unsafe { slice::from_raw_parts(clause, cnt) };
    let clause = int_slice
        .iter()
        .map(|il| Lit::from_ipasir(*il).expect("Invalid literal in learned clause from CaDiCaL"))
        .collect();
    cb(clause);
}

pub extern "C" fn rustsat_cadical_collect_lits(vec: *mut c_void, lit: c_int) {
    let vec = vec.cast::<Vec<Lit>>();
    let lit = Lit::from_ipasir(lit).expect("got invalid IPASIR lit from CaDiCaL");
    unsafe { (*vec).push(lit) };
}

// >= 2.0.0
#[cfg(all(
    not(feature = "v1-5-0"),
    not(feature = "v1-5-1"),
    not(feature = "v1-5-2"),
    not(feature = "v1-5-3"),
    not(feature = "v1-5-4"),
    not(feature = "v1-5-5"),
    not(feature = "v1-5-6"),
    not(feature = "v1-6-0"),
    not(feature = "v1-7-0"),
    not(feature = "v1-7-1"),
    not(feature = "v1-7-2"),
    not(feature = "v1-7-3"),
    not(feature = "v1-7-4"),
    not(feature = "v1-7-5"),
    not(feature = "v1-8-0"),
    not(feature = "v1-9-0"),
    not(feature = "v1-9-1"),
    not(feature = "v1-9-2"),
    not(feature = "v1-9-3"),
    not(feature = "v1-9-4"),
    not(feature = "v1-9-5"),
))]
pub mod tracer {
    use std::os::raw::{c_int, c_void};

    use rustsat::types::Lit;

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

    extern "C" fn rustsat_ccadical_add_original_clause(
        tracer: *mut c_void,
        id: u64,
        redundant: bool,
        cl_len: usize,
        cl_data: *const c_int,
        restored: bool,
    ) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.add_original_clause(ClauseId(id), redundant, &clause, restored);
    }

    extern "C" fn rustsat_ccadical_add_derived_clause(
        tracer: *mut c_void,
        id: u64,
        redundant: bool,
        cl_len: usize,
        cl_data: *const c_int,
        an_len: usize,
        an_data: *const u64,
    ) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        let antecedents = unsafe { std::slice::from_raw_parts(an_data.cast::<ClauseId>(), an_len) };
        tracer.add_derived_clause(ClauseId(id), redundant, &clause, antecedents);
    }

    extern "C" fn rustsat_ccadical_delete_clause(
        tracer: *mut c_void,
        id: u64,
        redundant: bool,
        cl_len: usize,
        cl_data: *const c_int,
    ) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.delete_clause(ClauseId(id), redundant, &clause);
    }

    extern "C" fn rustsat_ccadical_weaken_minus(
        tracer: *mut c_void,
        id: u64,
        cl_len: usize,
        cl_data: *const c_int,
    ) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.weaken_minus(ClauseId(id), &clause);
    }

    extern "C" fn rustsat_ccadical_strengthen(tracer: *mut c_void, id: u64) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        tracer.strengthen(ClauseId(id));
    }

    extern "C" fn rustsat_ccadical_report_status(tracer: *mut c_void, status: c_int, id: u64) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
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

    extern "C" fn rustsat_ccadical_finalize_clause(
        tracer: *mut c_void,
        id: u64,
        cl_len: usize,
        cl_data: *const c_int,
    ) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.finalize_clause(ClauseId(id), &clause);
    }

    extern "C" fn rustsat_ccadical_begin_proof(tracer: *mut c_void, id: u64) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        tracer.begin_proof(ClauseId(id));
    }

    extern "C" fn rustsat_ccadical_solve_query(tracer: *mut c_void) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        tracer.solve_query();
    }

    extern "C" fn rustsat_ccadical_add_assumption(tracer: *mut c_void, assump: c_int) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        tracer.add_assumption(
            Lit::from_ipasir(assump).expect("proof tracer got invalid literal from CaDiCaL"),
        );
    }

    extern "C" fn rustsat_ccadical_add_constraint(
        tracer: *mut c_void,
        cl_len: usize,
        cl_data: *const c_int,
    ) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        tracer.add_constraint(&clause);
    }

    extern "C" fn rustsat_ccadical_reset_assumptions(tracer: *mut c_void) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        tracer.reset_assumptions();
    }

    extern "C" fn rustsat_ccadical_add_assumption_clause(
        tracer: *mut c_void,
        id: u64,
        cl_len: usize,
        cl_data: *const c_int,
        an_len: usize,
        an_data: *const u64,
    ) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        let clause = CaDiCaLClause::new(cl_len, cl_data);
        let antecedents = unsafe { std::slice::from_raw_parts(an_data.cast::<ClauseId>(), an_len) };
        tracer.add_assumption_clause(ClauseId(id), &clause, antecedents);
    }

    extern "C" fn rustsat_ccadical_conclude_unsat(
        tracer: *mut c_void,
        concl: super::CCaDiCaLConclusionType,
        fail_len: usize,
        fail_data: *const u64,
    ) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        let failing = unsafe { std::slice::from_raw_parts(fail_data.cast::<ClauseId>(), fail_len) };
        let concl = match concl {
            super::CCaDiCaLConclusionType_CONFLICT => Conclusion::Conflict,
            super::CCaDiCaLConclusionType_ASSUMPTIONS => Conclusion::Assumptions,
            super::CCaDiCaLConclusionType_CONSTRAINT => Conclusion::Constraint,
            _ => panic!("proof tracer (`conclude_unsat`) received unexpected conclusion type from CaDiCaL: {concl}")
        };
        tracer.conclude_unsat(concl, failing);
    }

    extern "C" fn rustsat_ccadical_conclude_sat(
        tracer: *mut c_void,
        sol_len: usize,
        sol_data: *const c_int,
    ) {
        let tracer = unsafe { &mut **tracer.cast::<*mut dyn TraceProof>() };
        let assignment = CaDiCaLAssignment::new(sol_len, sol_data);
        tracer.conclude_sat(&assignment);
    }
}
