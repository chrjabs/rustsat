//! # Low-Level Foreign Function Interface

#![expect(non_upper_case_globals)]
#![expect(non_camel_case_types)]

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

#[cfg(cadical_version = "v2.0")]
pub mod prooftracer;

#[cfg(cadical_version = "v1.6")]
pub mod ipasirup;
