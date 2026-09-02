//! # Low-Level Foreign Function Interface

// these are intentionally not `expect` since they are not fulfilled for all CaDiCaL versions
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]

use core::ffi::c_int;
use core::ffi::c_void;

use rustsat::types::Lit;

pub mod prooftracer;

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// Raw callbacks forwarding to user callbacks
pub unsafe extern "C" fn rustsat_ccadical_terminate_cb(ptr: *mut c_void) -> c_int {
    let cb = unsafe { &mut *ptr.cast::<crate::TermCallbackPtr<'_>>() };
    match cb() {
        rustsat::solvers::ControlSignal::Continue => 0,
        rustsat::solvers::ControlSignal::Terminate => 1,
    }
}

pub unsafe extern "C" fn rustsat_ccadical_learn_cb(ptr: *mut c_void, clause: *mut c_int) {
    let cb = unsafe { &mut *ptr.cast::<crate::LearnCallbackPtr<'_>>() };

    let mut cnt: usize = 0;
    while unsafe {
        *clause.offset(isize::try_from(cnt).expect("learned clauses is longer than `isize::MAX`"))
    } != 0
    {
        cnt += 1;
    }
    let int_slice = unsafe { rustsat::utils::from_raw_parts_maybe_null(clause, cnt) };
    let clause = int_slice
        .iter()
        .map(|il| Lit::from_ipasir(*il).expect("Invalid literal in learned clause from CaDiCaL"))
        .collect();
    cb(clause);
}

pub unsafe extern "C" fn rustsat_cadical_collect_lits(vec: *mut c_void, lit: c_int) {
    let vec = vec.cast::<Vec<Lit>>();
    let lit = Lit::from_ipasir(lit).expect("got invalid IPASIR lit from CaDiCaL");
    unsafe { &mut *vec }.push(lit);
}
