use core::ffi::c_char;
use core::ffi::c_int;
use core::ffi::c_void;

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
        terminate: Option<unsafe extern "C" fn(state: *const c_void) -> c_int>,
    );
    pub fn ipasir_set_learn(
        solver: *mut IpasirHandle,
        state: *const c_void,
        max_length: c_int,
        learn: Option<unsafe extern "C" fn(state: *const c_void, clause: *const c_int)>,
    );
}

// Raw callbacks forwarding to user callbacks
pub unsafe extern "C" fn ipasir_terminate_cb(ptr: *const c_void) -> c_int {
    let cb = &mut *(ptr as *mut crate::TermCallbackPtr<'_>);
    match cb() {
        rustsat::solvers::ControlSignal::Continue => 0,
        rustsat::solvers::ControlSignal::Terminate => 1,
    }
}

pub unsafe extern "C" fn ipasir_learn_cb(ptr: *const c_void, clause: *const c_int) {
    let cb = unsafe { &mut *(ptr as *mut crate::LearnCallbackPtr<'_>) };

    let mut cnt: usize = 0;
    while *clause.offset(isize::try_from(cnt).expect("learned clauses is longer than `isize::MAX`"))
        != 0
    {
        cnt += 1;
    }
    let int_slice = rustsat::utils::from_raw_parts_maybe_null(clause, cnt);
    let clause = int_slice
        .iter()
        .map(|il| {
            rustsat::types::Lit::from_ipasir(*il)
                .expect("Invalid literal in learned clause from IPASIR solver")
        })
        .collect();
    cb(clause);
}
