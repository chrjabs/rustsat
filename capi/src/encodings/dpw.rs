//! # Dynamic Poly Watchdog C-API

use std::ffi::{c_int, c_void};

use rustsat::{
    encodings::pb::{BoundUpper, BoundUpperIncremental, DynamicPolyWatchdog, EncodeIncremental},
    types::Lit,
};

use super::{CAssumpCollector, CClauseCollector, ClauseCollector, MaybeError, VarManager};

/// Creates a new [`DynamicPolyWatchdog`] cardinality encoding
#[no_mangle]
pub extern "C" fn dpw_new() -> *mut DynamicPolyWatchdog {
    Box::into_raw(Box::default())
}

/// Adds a new input literal to a [`DynamicPolyWatchdog`].
///
/// # Errors
///
/// - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
///     [`MaybeError::InvalidLiteral`] is returned
/// - If a literal is added _after_ the encoding is build, [`MaybeError::InvalidState`] is returned
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_add(
    dpw: *mut DynamicPolyWatchdog,
    lit: c_int,
    weight: usize,
) -> MaybeError {
    let Ok(lit) = Lit::from_ipasir(lit) else {
        return MaybeError::InvalidLiteral;
    };
    if unsafe { (*dpw).add_input(lit, weight) }.is_ok() {
        MaybeError::Ok
    } else {
        MaybeError::InvalidState
    }
}

/// Lazily builds the _change in_ pseudo-boolean encoding to enable upper bounds from within the
/// range. A change might only be a change in bounds, the [`DynamicPolyWatchdog`] does not support
/// adding literals at the moment.
///
/// The min and max bounds are inclusive. After a call to [`dpw_encode_ub`] with `min_bound=2` and
/// `max_bound=4`, bounds satisfying `2 <= bound <= 4` can be enforced.
///
/// Clauses are returned via the `collector`. The `collector` function should expect clauses to be
/// passed similarly to `ipasir_add`, as a 0-terminated sequence of literals where the literals are
/// passed as the first argument and the `collector_data` as a second.
///
/// `n_vars_used` must be the number of variables already used and will be incremented by the
/// number of variables used up in the encoding.
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
///
/// # Panics
///
/// - If `min_bound > max_bound`.
/// - If the encoding ran out of memory
#[no_mangle]
pub unsafe extern "C" fn dpw_encode_ub(
    dpw: *mut DynamicPolyWatchdog,
    min_bound: usize,
    max_bound: usize,
    n_vars_used: &mut u32,
    collector: CClauseCollector,
    collector_data: *mut c_void,
) {
    assert!(min_bound <= max_bound);
    let mut collector = ClauseCollector::new(collector, collector_data);
    let mut var_manager = VarManager::new(n_vars_used);
    unsafe { (*dpw).encode_ub_change(min_bound..=max_bound, &mut collector, &mut var_manager) }
        .expect("clause collector returned out of memory");
}

/// Returns assumptions/units for enforcing an upper bound (`sum of lits <= ub`). Make sure that
/// [`dpw_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
/// [`MaybeError::NotEncoded`] will be returned.
///
/// Assumptions are returned via the collector callback. There is _no_ terminating zero, all
/// assumptions are passed when [`dpw_enforce_ub`] returns.
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_enforce_ub(
    dpw: *mut DynamicPolyWatchdog,
    ub: usize,
    collector: CAssumpCollector,
    collector_data: *mut c_void,
) -> MaybeError {
    match unsafe { (*dpw).enforce_ub(ub) } {
        Ok(assumps) => {
            for l in assumps {
                collector(l.to_ipasir(), collector_data);
            }
            MaybeError::Ok
        }
        Err(err) => err.into(),
    }
}

/// Gets the next smaller upper bound value that can be encoded without setting tares. This is used
/// for coarse convergence.
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_coarse_ub(dpw: *mut DynamicPolyWatchdog, ub: usize) -> usize {
    unsafe { (*dpw).coarse_ub(ub) }
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
///     [`MaybeError::PrecisionDecreased`] is returned
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_set_precision(
    dpw: *mut DynamicPolyWatchdog,
    divisor: usize,
) -> MaybeError {
    unsafe { (*dpw).set_precision(divisor) }.into()
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
    unsafe { (*dpw).next_precision() }
}

/// Checks whether the encoding is already at the maximum precision
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_is_max_precision(dpw: *mut DynamicPolyWatchdog) -> bool {
    unsafe { (*dpw).is_max_precision() }
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
/// - If `min_bound <= max_bound`.
/// - If the encoding ran out of memory
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
    unsafe { (*dpw).limit_range(min_value..=max_value, &mut collector) }
        .expect("clause collector returned out of memory");
}

/// Reserves all auxiliary variables that the encoding might need
///
/// All calls to [`dpw_encode_ub`] following a call to this function are guaranteed to not increase
/// the value of `n_vars_used`. This does _not_ hold if [`dpw_add`] is called in between
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn dpw_reserve(dpw: *mut DynamicPolyWatchdog, n_vars_used: &mut u32) {
    let mut var_manager = VarManager::new(n_vars_used);
    unsafe { (*dpw).reserve(&mut var_manager) };
}

/// Frees the memory associated with a [`DynamicPolyWatchdog`]
///
/// # Safety
///
/// `dpw` must be a return value of [`dpw_new`] and cannot be used afterwards again.
#[no_mangle]
pub unsafe extern "C" fn dpw_drop(dpw: *mut DynamicPolyWatchdog) {
    drop(unsafe { Box::from_raw(dpw) });
}

// TODO: figure out how to get these to work on windows
#[cfg(all(test, not(target_os = "windows")))]
mod tests {
    use inline_c::assert_c;

    #[test]
    fn new_drop() {
        (assert_c! {
            #include <assert.h>
            #include "rustsat.h"

            int main() {
                DynamicPolyWatchdog *dpw = dpw_new();
                assert(dpw != NULL);
                dpw_drop(dpw);
                return 0;
            }
        })
        .success();
    }

    #[test]
    fn basic() {
        (assert_c! {
            #include <assert.h>
            #include "rustsat.h"

            void clause_counter(int lit, void *data) {
                if (!lit) {
                    int *cnt = (int *)data;
                    (*cnt)++;
                }
            }

            int main() {
                DynamicPolyWatchdog *dpw = dpw_new();
                assert(dpw_add(dpw, 1, 1) == Ok);
                assert(dpw_add(dpw, 2, 1) == Ok);
                assert(dpw_add(dpw, 3, 2) == Ok);
                assert(dpw_add(dpw, 4, 2) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                dpw_encode_ub(dpw, 0, 6, &n_used, &clause_counter, &n_clauses);
                dpw_drop(dpw);
                assert(n_used == 13);
                assert(n_clauses == 13);
                return 0;
            }
        })
        .success();
    }

    #[test]
    fn reserve() {
        (assert_c! {
            #include <assert.h>
            #include "rustsat.h"

            void clause_counter(int lit, void *data) {
                if (!lit) {
                    int *cnt = (int *)data;
                    (*cnt)++;
                }
            }

            int main() {
                DynamicPolyWatchdog *dpw = dpw_new();
                assert(dpw_add(dpw, 1, 1) == Ok);
                assert(dpw_add(dpw, 2, 1) == Ok);
                assert(dpw_add(dpw, 3, 2) == Ok);
                assert(dpw_add(dpw, 4, 2) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                dpw_reserve(dpw, &n_used);
                assert(n_used == 15);
                dpw_encode_ub(dpw, 2, 6, &n_used, &clause_counter, &n_clauses);
                assert(n_used == 15);
                dpw_encode_ub(dpw, 0, 4, &n_used, &clause_counter, &n_clauses);
                assert(n_used == 15);
                dpw_drop(dpw);
                return 0;
            }
        })
        .success();
    }

    #[test]
    fn coarse_convergence() {
        (assert_c! {
            #include <assert.h>
            #include "rustsat.h"

            void assump_counter(int lit, void *data) {
                assert(lit);
                int *cnt = (int *) data;
                (*cnt)++;
            }

            void clause_counter(int lit, void *data) {
                if (!lit) {
                    int *cnt = (int *)data;
                    (*cnt)++;
                }
            }

            int main() {
                DynamicPolyWatchdog *dpw = dpw_new();
                assert(dpw_add(dpw, 1, 5) == Ok);
                assert(dpw_add(dpw, 2, 3) == Ok);
                assert(dpw_add(dpw, 3, 8) == Ok);
                assert(dpw_add(dpw, 4, 7) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                dpw_encode_ub(dpw, 0, 23, &n_used, &clause_counter, &n_clauses);
                for (size_t ub = 7; ub < 23; ub++) {
                    size_t coarse_ub = dpw_coarse_ub(dpw, ub);
                    assert(coarse_ub <= ub);
                    if (ub % 8 == 7) assert(coarse_ub == ub);
                    int n_assumps = 0;
                    assert(dpw_enforce_ub(dpw, coarse_ub, &assump_counter, &n_assumps) == Ok);
                    assert(n_assumps == 1);
                }
            }
        })
        .success();
    }
}
