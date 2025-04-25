//! # Dynamic Poly Watchdog C-API

use std::ffi::c_void;

use rustsat::encodings::pb::{BoundUpper, DynamicPolyWatchdog};

use super::{CClauseCollector, ClauseCollector, MaybeError};

#[cfg(doc)]
use super::pb::{dpw_drop, dpw_new};

/// Gets the next smaller upper bound value that can be encoded without setting tares. This is used
/// for coarse convergence.
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_coarse_ub(dpw: *mut DynamicPolyWatchdog, ub: usize) -> usize {
    (*dpw).coarse_ub(ub)
}

/// Set the precision at which to build the encoding at. With `divisor = 8` the encoding will
/// effectively be built such that the weight of every input literal is divided by `divisor`
/// (integer division, rounding down). Divisor values must be powers of 2. After building the
/// encoding, the precision can only be increased, i.e., only call this function with _decreasing_
/// divisor values.
///
/// # Errors
///
/// - If `divisor` is not a power of 2, [`MaybeError::PrecisionNotPow2`] is returned
/// - If `divisor` is larger than the last divisor, i.e., precision is attempted to be decreased,
///   [`MaybeError::PrecisionDecreased`] is returned
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_set_precision(
    dpw: *mut DynamicPolyWatchdog,
    divisor: usize,
) -> MaybeError {
    (*dpw).set_precision(divisor).into()
}

/// Gets the next possible precision divisor value
///
/// Note that this is not the next possible precision value from the last _set_ precision but from
/// the last _encoded_ precision. The divisor value will always be a power of two so that calling
/// `set_precision` and then encoding will produce the smallest non-empty next segment of the
/// encoding.
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_next_precision(dpw: *mut DynamicPolyWatchdog) -> usize {
    (*dpw).next_precision()
}

/// Checks whether the encoding is already at the maximum precision
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_is_max_precision(dpw: *mut DynamicPolyWatchdog) -> bool {
    (*dpw).is_max_precision()
}

/// Given a range of output values to limit the encoding to, returns additional clauses that
/// "shrink" the encoding through hardening
///
/// The output value range must be a range considering _all_ input literals, not only the encoded
/// ones.
///
/// This is intended for, e.g., a MaxSAT solving application where a global lower bound is derived
/// and parts of the encoding can be hardened.
///
/// The min and max bounds are inclusive. After a call to [`dpw_limit_range`] with `min_value=2`
/// and `max_value=4`, the encoding is valid for the value range `2 <= range <= 4`.
///
/// To not specify a bound, pass `0` for the lower bound or `SIZE_MAX` for the upper bound.
///
/// Clauses are returned via the `collector`. The `collector` function should expect clauses to be
/// passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
/// passed as the first argument and the `collector_data` as a second.
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
///
/// # Panics
///
/// If `min_bound <= max_bound`.
#[no_mangle]
pub unsafe extern "C" fn dpw_limit_range(
    dpw: *mut DynamicPolyWatchdog,
    min_value: usize,
    max_value: usize,
    collector: CClauseCollector,
    collector_data: *mut c_void,
) {
    assert!(min_value <= max_value);
    let mut collector = ClauseCollector::new(collector, collector_data);
    (*dpw)
        .limit_range(min_value..=max_value, &mut collector)
        .expect("CClauseCollector cannot report out of memory");
}
