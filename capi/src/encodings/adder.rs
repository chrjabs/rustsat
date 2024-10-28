//! # Binary Adder C-API

use std::ffi::{c_int, c_void};

use rustsat::{
    encodings::pb::{
        BinaryAdder, BoundLower, BoundLowerIncremental, BoundUpper, BoundUpperIncremental,
        EncodeIncremental,
    },
    types::Lit,
};

use super::{CAssumpCollector, CClauseCollector, ClauseCollector, MaybeError, VarManager};

/// Creates a new [`BinaryAdder`] cardinality encoding
#[no_mangle]
pub extern "C" fn bin_adder_new() -> *mut BinaryAdder {
    Box::into_raw(Box::default())
}

/// Adds a new input literal to a [`BinaryAdder`].
///
/// # Errors
///
/// - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
///     [`MaybeError::InvalidLiteral`] is returned
///
/// # Safety
///
/// `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
/// called on.
#[no_mangle]
pub unsafe extern "C" fn bin_adder_add(
    adder: *mut BinaryAdder,
    lit: c_int,
    weight: usize,
) -> MaybeError {
    let Ok(lit) = Lit::from_ipasir(lit) else {
        return MaybeError::InvalidLiteral;
    };
    unsafe { (*adder).extend([(lit, weight)]) };
    MaybeError::Ok
}

/// Lazily builds the _change in_ pseudo-boolean encoding to enable upper bounds from within the
/// range.
///
/// The min and max bounds are inclusive. After a call to [`bin_adder_encode_ub`] with
/// `min_bound=2` and `max_bound=4`, bounds satisfying `2 <= bound <= 4` can be enforced.
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
/// `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
/// called on.
///
/// # Panics
///
/// - If `min_bound > max_bound`.
/// - If the encoding ran out of memory
#[no_mangle]
pub unsafe extern "C" fn bin_adder_encode_ub(
    adder: *mut BinaryAdder,
    min_bound: usize,
    max_bound: usize,
    n_vars_used: &mut u32,
    collector: CClauseCollector,
    collector_data: *mut c_void,
) {
    assert!(min_bound <= max_bound);
    let mut collector = ClauseCollector::new(collector, collector_data);
    let mut var_manager = VarManager::new(n_vars_used);
    unsafe { (*adder).encode_ub_change(min_bound..=max_bound, &mut collector, &mut var_manager) }
        .expect("clause collector returned out of memory");
}

/// Returns assumptions/units for enforcing an upper bound (`sum of lits <= ub`). Make sure that
/// [`bin_adder_encode_ub`] has been called adequately and nothing has been called afterwards,
/// otherwise [`MaybeError::NotEncoded`] will be returned.
///
/// Assumptions are returned via the collector callback. There is _no_ terminating zero, all
/// assumptions are passed when [`bin_adder_enforce_ub`] returns.
///
/// # Safety
///
/// `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
/// called on.
#[no_mangle]
pub unsafe extern "C" fn bin_adder_enforce_ub(
    adder: *mut BinaryAdder,
    ub: usize,
    collector: CAssumpCollector,
    collector_data: *mut c_void,
) -> MaybeError {
    match unsafe { (*adder).enforce_ub(ub) } {
        Ok(assumps) => {
            for l in assumps {
                collector(l.to_ipasir(), collector_data);
            }
            MaybeError::Ok
        }
        Err(err) => err.into(),
    }
}

/// Lazily builds the _change in_ pseudo-boolean encoding to enable lower bounds from within the
/// range.
///
/// The min and max bounds are inclusive. After a call to [`bin_adder_encode_lb`] with
/// `min_bound=2` and `max_bound=4`, bounds satisfying `2 <= bound <= 4` can be enforced.
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
/// `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
/// called on.
///
/// # Panics
///
/// If `min_bound > max_bound`.
#[no_mangle]
pub unsafe extern "C" fn bin_adder_encode_lb(
    adder: *mut BinaryAdder,
    min_bound: usize,
    max_bound: usize,
    n_vars_used: &mut u32,
    collector: CClauseCollector,
    collector_data: *mut c_void,
) {
    assert!(min_bound <= max_bound);
    let mut collector = ClauseCollector::new(collector, collector_data);
    let mut var_manager = VarManager::new(n_vars_used);
    unsafe { (*adder).encode_lb_change(min_bound..=max_bound, &mut collector, &mut var_manager) }
        .expect("clause collector returned out of memory");
}

/// Returns assumptions/units for enforcing an upper bound (`sum of lits >= lb`). Make sure that
/// [`bin_adder_encode_lb`] has been called adequately and nothing has been called afterwards,
/// otherwise [`MaybeError::NotEncoded`] will be returned.
///
/// Assumptions are returned via the collector callback. There is _no_ terminating zero, all
/// assumptions are passed when [`bin_adder_enforce_lb`] returns.
///
/// # Safety
///
/// `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
/// called on.
#[no_mangle]
pub unsafe extern "C" fn bin_adder_enforce_lb(
    adder: *mut BinaryAdder,
    ub: usize,
    collector: CAssumpCollector,
    collector_data: *mut c_void,
) -> MaybeError {
    match unsafe { (*adder).enforce_lb(ub) } {
        Ok(assumps) => {
            for l in assumps {
                collector(l.to_ipasir(), collector_data);
            }
            MaybeError::Ok
        }
        Err(err) => err.into(),
    }
}

/// Reserves all auxiliary variables that the encoding might need
///
/// All calls to [`bin_adder_encode_ub`] or [`bin_adder_encode_lb`] following a call to this
/// function are guaranteed to not increase the value of `n_vars_used`. This does _not_ hold if
/// [`bin_adder_add`] is called in between
///
/// # Safety
///
/// `adder` must be a return value of [`bin_adder_new`] that [`bin_adder_drop`] has not yet been
/// called on.
#[no_mangle]
pub unsafe extern "C" fn bin_adder_reserve(adder: *mut BinaryAdder, n_vars_used: &mut u32) {
    let mut var_manager = VarManager::new(n_vars_used);
    unsafe { (*adder).reserve(&mut var_manager) };
}

/// Frees the memory associated with a [`BinaryAdder`]
///
/// # Safety
///
/// `adder` must be a return value of [`bin_adder_new`] and cannot be used
/// afterwards again.
#[no_mangle]
pub unsafe extern "C" fn bin_adder_drop(adder: *mut BinaryAdder) {
    drop(unsafe { Box::from_raw(adder) });
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
                BinaryAdder *adder = bin_adder_new();
                assert(adder != NULL);
                bin_adder_drop(adder);
                return 0;
            }
        })
        .success();
    }

    #[test]
    fn basic_ub() {
        (assert_c! {
            #include <assert.h>
            #include <stdio.h>
            #include "rustsat.h"

            void clause_counter(int lit, void *data) {
                if (!lit) {
                    int *cnt = (int *)data;
                    (*cnt)++;
                }
            }

            int main() {
                BinaryAdder *adder = bin_adder_new();
                assert(bin_adder_add(adder, 1, 1) == Ok);
                assert(bin_adder_add(adder, 2, 2) == Ok);
                assert(bin_adder_add(adder, 3, 3) == Ok);
                assert(bin_adder_add(adder, 4, 4) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                bin_adder_encode_ub(adder, 0, 6, &n_used, &clause_counter, &n_clauses);
                bin_adder_drop(adder);
                printf("%d", n_used);
                assert(n_used == 17);
                assert(n_clauses == 32);
                return 0;
            }
        })
        .success();
    }

    #[test]
    fn basic_lb() {
        (assert_c! {
            #include <assert.h>
            #include <stdio.h>
            #include "rustsat.h"

            void clause_counter(int lit, void *data) {
                if (!lit) {
                    int *cnt = (int *)data;
                    (*cnt)++;
                }
            }

            int main() {
                BinaryAdder *adder = bin_adder_new();
                assert(bin_adder_add(adder, 1, 1) == Ok);
                assert(bin_adder_add(adder, 2, 2) == Ok);
                assert(bin_adder_add(adder, 3, 3) == Ok);
                assert(bin_adder_add(adder, 4, 4) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                bin_adder_encode_lb(adder, 0, 6, &n_used, &clause_counter, &n_clauses);
                bin_adder_drop(adder);
                printf("%d", n_used);
                assert(n_used == 16);
                assert(n_clauses == 27);
                return 0;
            }
        })
        .success();
    }
}
