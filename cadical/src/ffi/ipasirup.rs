//! # FFI Functionality for IPASIR-UP

use std::os::raw::{c_int, c_void};

use rustsat::{
    types::{Assignment, Lit},
    utils::from_raw_parts_maybe_null,
};

use crate::ipasirup::{
    AssignmentIter, BacktrackableContext, DynCompatExternalPropagate, SolvingContext,
};

#[derive(Debug)]
pub struct Data {
    pub prop: *mut dyn DynCompatExternalPropagate,
    cadical_handle: *mut super::CCaDiCaL,
    reason_buffer: Option<std::vec::IntoIter<Lit>>,
    external_buffer: Option<std::vec::IntoIter<Lit>>,
}

impl Data {
    pub fn new(
        cadical_handle: *mut super::CCaDiCaL,
        prop: *mut dyn DynCompatExternalPropagate,
    ) -> Self {
        Self {
            prop,
            cadical_handle,
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

#[inline]
unsafe fn to_data<'a>(data: *mut c_void) -> &'a mut Data {
    &mut *data.cast::<Data>()
}

#[inline]
pub fn from_ipasir_panic(lit: c_int) -> Lit {
    Lit::from_ipasir(lit).expect("external propagator got invalid lit from CaDiCaL")
}

#[cfg(cadical_version = "v2.1")]
unsafe extern "C" fn rustsat_cadical_notify_assignment(
    data: *mut c_void,
    lits: *const c_int,
    len: usize,
) {
    let data = to_data(data);
    let lits = from_raw_parts_maybe_null(lits, len);
    let mut context = SolvingContext::new(data.cadical_handle);
    (*data.prop).assignment(AssignmentIter::new(lits), &mut context);
}

#[cfg(not(cadical_version = "v2.1"))]
unsafe extern "C" fn rustsat_cadical_notify_assignment(
    data: *mut c_void,
    lit: c_int,
    _is_fixed: c_int,
) {
    let data = to_data(data);
    let mut context = SolvingContext::new(data.cadical_handle);
    (*data.prop).assignment(AssignmentIter::new(&[from_ipasir_panic(lit)]), &mut context);
}

unsafe extern "C" fn rustsat_cadical_notify_new_decision_level(data: *mut c_void) {
    let data = to_data(data);
    let mut context = SolvingContext::new(data.cadical_handle);
    (*data.prop).new_decision_level(&mut context);
}

unsafe extern "C" fn rustsat_cadical_notify_backtrack(data: *mut c_void, new_level: usize) {
    let data = to_data(data);
    let mut context = SolvingContext::new(data.cadical_handle);
    (*data.prop).backtrack(new_level, &mut context);
}

unsafe extern "C" fn rustsat_cadical_cb_check_found_model(
    data: *mut c_void,
    model: *const c_int,
    model_len: usize,
) -> c_int {
    let data = to_data(data);
    let model = from_raw_parts_maybe_null(model, model_len);
    let sol: Assignment = model.iter().copied().map(from_ipasir_panic).collect();
    let mut context = BacktrackableContext::new(data.cadical_handle);
    c_int::from((*data.prop).check_found_solution(&sol, &mut context))
}

unsafe extern "C" fn rustsat_cadical_cb_decide(data: *mut c_void) -> c_int {
    let data = to_data(data);
    let mut context = BacktrackableContext::new(data.cadical_handle);
    (*data.prop).decide(&mut context).map_or(0, Lit::to_ipasir)
}

unsafe extern "C" fn rustsat_cadical_cb_propagate(data: *mut c_void) -> c_int {
    let data = to_data(data);
    let mut context = SolvingContext::new(data.cadical_handle);
    (*data.prop)
        .propagate(&mut context)
        .map_or(0, Lit::to_ipasir)
}

unsafe extern "C" fn rustsat_cadical_cb_add_reason_clause_lit(
    data: *mut c_void,
    propagated_lit: c_int,
) -> c_int {
    let data = to_data(data);
    if let Some(iter) = &mut data.reason_buffer {
        let Some(lit) = iter.next() else {
            data.reason_buffer = None;
            return 0;
        };
        lit.to_ipasir()
    } else {
        let mut context = SolvingContext::new(data.cadical_handle);
        let mut iter = (*data.prop)
            .reason_clause(from_ipasir_panic(propagated_lit), &mut context)
            .into_iter();
        let Some(lit) = iter.next() else {
            return 0;
        };
        data.reason_buffer = Some(iter);
        lit.to_ipasir()
    }
}

unsafe extern "C" fn rustsat_cadical_cb_has_external_clause(
    data: *mut c_void,
    is_forgettable: *mut c_int,
) -> c_int {
    let data = to_data(data);
    let mut context = SolvingContext::new(data.cadical_handle);
    let Some(crate::ExternalClause {
        clause,
        forgettable,
    }) = (*data.prop).external_clause(&mut context)
    else {
        data.external_buffer = None;
        return c_int::from(false);
    };
    data.external_buffer = Some(clause.into_iter());
    *is_forgettable = c_int::from(forgettable);
    c_int::from(true)
}

unsafe extern "C" fn rustsat_cadical_cb_add_external_clause_lit(data: *mut c_void) -> c_int {
    let data = to_data(data);
    let Some(iter) = &mut data.external_buffer else {
        return 0;
    };
    let Some(lit) = iter.next() else {
        return 0;
    };
    lit.to_ipasir()
}
