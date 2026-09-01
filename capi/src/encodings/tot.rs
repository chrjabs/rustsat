//! # Totalizer C-API

use core::ffi::c_int;
use core::ffi::c_void;

use rustsat::encodings::card::Totalizer;

#[cfg(doc)]
use super::card::tot_drop;
#[cfg(doc)]
use super::card::tot_new;

/// Gets the output literal (`lit`) of the totalizer corresponding to a certain value
///
/// Note that the literal might be `0` if the output is not encoded
///
/// # Safety
///
/// - `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on
/// - it must be safe for this function to write to `lit`
#[unsafe(no_mangle)]
pub unsafe extern "C" fn tot_get_output(
    tot: *mut Totalizer,
    value: usize,
    lit: *mut c_int,
) -> super::MaybeError {
    let Ok(ret) = unsafe { &mut *tot }.output(value) else {
        return super::MaybeError::NotEncoded;
    };
    unsafe {
        *lit = ret.map_or(0, rustsat::types::Lit::to_ipasir);
    }
    super::MaybeError::Ok
}

/// Gets all output literals of the totalizer
///
/// Note that literals might be `0` if an output is not encoded
///
/// # Safety
///
/// `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn tot_get_outputs(
    tot: *mut Totalizer,
    collector: super::COutputCollector,
    collector_data: *mut c_void,
) -> super::MaybeError {
    let Ok(iter) = unsafe { &mut *tot }.outputs() else {
        return super::MaybeError::NotEncoded;
    };
    for (val, lit) in iter {
        collector(
            val,
            lit.map_or(0, rustsat::types::Lit::to_ipasir),
            collector_data,
        );
    }
    super::MaybeError::Ok
}
