include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

// Raw callbacks forwarding to user callbacks
pub extern "C" fn kissat_terminate_cb(ptr: *mut core::ffi::c_void) -> core::ffi::c_int {
    let cb = unsafe { &mut *ptr.cast::<crate::TermCallbackPtr>() };
    match cb() {
        rustsat::solvers::ControlSignal::Continue => 0,
        rustsat::solvers::ControlSignal::Terminate => 1,
    }
}
