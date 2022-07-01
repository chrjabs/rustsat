use std::os::raw::{c_char, c_int, c_void};

#[repr(C)]
pub struct IpasirHandle {
    _private: [u8; 0],
}

extern "C" {
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
