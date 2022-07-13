use crate::solvers::ControlSignal;
use crate::types::Lit;
use std::os::raw::{c_char, c_int, c_void};
use std::{mem, slice};

#[repr(C)]
pub struct IpasirHandle {
    _private: [u8; 0],
}

extern "C" {
    // Redefinitions of IPASIR functions
    pub fn ipasir_signature() -> *const c_char;
    pub fn ipasir_init() -> *mut IpasirHandle;
    pub fn ipasir_release(solver: *mut IpasirHandle);
    pub fn ipasir_add(solver: *mut IpasirHandle, lit_or_zero: c_int);
    pub fn ipasir_assume(solver: *mut IpasirHandle, lit: c_int);
    pub fn ipasir_solve(solver: *mut IpasirHandle) -> c_int;
    pub fn ipasir_val(solver: *mut IpasirHandle, lit: c_int) -> c_int;
    pub fn ipasir_failed(solver: *mut IpasirHandle, lit: c_int) -> c_int;
    pub fn ipasir_set_terminate(
        solver: *mut IpasirHandle,
        state: *const c_void,
        terminate: extern "C" fn(state: *const c_void) -> c_int,
    );
    pub fn ipasir_set_learn(
        solver: *mut IpasirHandle,
        state: *const c_void,
        max_length: c_int,
        learn: extern "C" fn(state: *const c_void, clause: *const c_int),
    );
}

// Raw callbacks forwarding to user callbacks
pub extern "C" fn ipasir_terminate_cb(ptr: *const c_void) -> c_int {
    let cb: &mut Box<dyn FnMut() -> ControlSignal> = unsafe { mem::transmute(ptr) };
    match cb() {
        ControlSignal::Continue => 0,
        ControlSignal::Terminate => 1,
    }
}

pub extern "C" fn ipasir_learn_cb(ptr: *const c_void, clause: *const c_int) {
    let cb: &mut Box<dyn FnMut(Vec<Lit>)> = unsafe { mem::transmute(ptr) };

    let mut cnt = 0;
    for n in 0.. {
        if unsafe { *clause.offset(n) } != 0 {
            cnt += 1;
        }
    }
    let int_slice = unsafe { slice::from_raw_parts(clause, cnt) };
    let clause: Vec<Lit> = int_slice
        .into_iter()
        .map(|il| Lit::from_ipasir(*il))
        .collect();
    cb(clause)
}
