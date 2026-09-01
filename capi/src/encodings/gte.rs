//! # Totalizer C-API

use core::ffi::c_int;
use core::ffi::c_void;

use rustsat::encodings::pb::GeneralizedTotalizer;

#[cfg(doc)]
use super::pb::gte_drop;
#[cfg(doc)]
use super::pb::gte_new;

/// Gets the output literal (`lit`) of the generalized totalizer corresponding to a certain value
///
/// Note that the literal might be `0` if the output is not encoded
///
/// # Safety
///
/// `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn gte_get_output(
    gte: *mut GeneralizedTotalizer,
    value: usize,
    lit: *mut c_int,
) -> super::MaybeError {
    let Ok(ret) = (*gte).output(value) else {
        return super::MaybeError::NotEncoded;
    };
    *lit = ret.map_or(0, rustsat::types::Lit::to_ipasir);
    super::MaybeError::Ok
}

/// Gets all output literals of the generalized totalizer
///
/// Note that literals might be `0` if an output is not encoded
///
/// # Safety
///
/// `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn gte_get_outputs(
    gte: *mut GeneralizedTotalizer,
    collector: super::COutputCollector,
    collector_data: *mut c_void,
) -> super::MaybeError {
    let Ok(iter) = (*gte).outputs() else {
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
