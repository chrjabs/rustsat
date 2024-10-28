//! # Generalized Totalizer C-API

use std::ffi::{c_int, c_void};

use rustsat::{
    encodings::pb::{BoundUpper, BoundUpperIncremental, DbGte, EncodeIncremental as _},
    types::Lit,
};

use super::{CAssumpCollector, CClauseCollector, ClauseCollector, MaybeError, VarManager};

/// Creates a new [`DbGte`] cardinality encoding
#[no_mangle]
pub extern "C" fn gte_new() -> *mut DbGte {
    Box::into_raw(Box::default())
}

/// Adds a new input literal to a [`DbGte`].
///
/// # Errors
///
/// - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
///     [`MaybeError::InvalidLiteral`] is returned
///
/// # Safety
///
/// `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn gte_add(gte: *mut DbGte, lit: c_int, weight: usize) -> MaybeError {
    let Ok(lit) = Lit::from_ipasir(lit) else {
        return MaybeError::InvalidLiteral;
    };
    unsafe { (*gte).extend([(lit, weight)]) };
    MaybeError::Ok
}

/// Lazily builds the _change in_ pseudo-boolean encoding to enable upper bounds from within the
/// range.
///
/// The min and max bounds are inclusive. After a call to [`gte_encode_ub`] with `min_bound=2` and
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
/// `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
///
/// # Panics
///
/// - If `min_bound > max_bound`.
/// - If the encoding ran out of memory
#[no_mangle]
pub unsafe extern "C" fn gte_encode_ub(
    gte: *mut DbGte,
    min_bound: usize,
    max_bound: usize,
    n_vars_used: &mut u32,
    collector: CClauseCollector,
    collector_data: *mut c_void,
) {
    assert!(min_bound <= max_bound);
    let mut collector = ClauseCollector::new(collector, collector_data);
    let mut var_manager = VarManager::new(n_vars_used);
    unsafe { (*gte).encode_ub_change(min_bound..=max_bound, &mut collector, &mut var_manager) }
        .expect("clause collector returned out of memory");
}

/// Returns assumptions/units for enforcing an upper bound (`sum of lits <= ub`). Make sure that
/// [`gte_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
/// [`MaybeError::NotEncoded`] will be returned.
///
/// Assumptions are returned via the collector callback. There is _no_ terminating zero, all
/// assumptions are passed when [`gte_enforce_ub`] returns.
///
/// # Safety
///
/// `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn gte_enforce_ub(
    gte: *mut DbGte,
    ub: usize,
    collector: CAssumpCollector,
    collector_data: *mut c_void,
) -> MaybeError {
    match unsafe { (*gte).enforce_ub(ub) } {
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
/// All calls to [`gte_encode_ub`] following a call to this function are guaranteed to not increase
/// the value of `n_vars_used`. This does _not_ hold if [`gte_add`] is called in between
///
/// # Safety
///
/// `gte` must be a return value of [`gte_new`] that [`gte_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn gte_reserve(gte: *mut DbGte, n_vars_used: &mut u32) {
    let mut var_manager = VarManager::new(n_vars_used);
    unsafe { (*gte).reserve(&mut var_manager) };
}

/// Frees the memory associated with a [`DbGte`]
///
/// # Safety
///
/// `gte` must be a return value of [`gte_new`] and cannot be used
/// afterwards again.
#[no_mangle]
pub unsafe extern "C" fn gte_drop(gte: *mut DbGte) {
    drop(unsafe { Box::from_raw(gte) });
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
                DbGte *gte = gte_new();
                assert(gte != NULL);
                gte_drop(gte);
                return 0;
            }
        })
        .success();
    }

    #[test]
    fn basic() {
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
                DbGte *gte = gte_new();
                assert(gte_add(gte, 1, 1) == Ok);
                assert(gte_add(gte, 2, 2) == Ok);
                assert(gte_add(gte, 3, 3) == Ok);
                assert(gte_add(gte, 4, 4) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                gte_encode_ub(gte, 0, 6, &n_used, &clause_counter, &n_clauses);
                gte_drop(gte);
                printf("%d", n_used);
                assert(n_used == 24);
                assert(n_clauses == 25);
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
                DbGte *gte = gte_new();
                assert(gte_add(gte, 1, 1) == Ok);
                assert(gte_add(gte, 2, 1) == Ok);
                assert(gte_add(gte, 3, 2) == Ok);
                assert(gte_add(gte, 4, 2) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                gte_reserve(gte, &n_used);
                assert(n_used == 14);
                gte_encode_ub(gte, 2, 6, &n_used, &clause_counter, &n_clauses);
                assert(n_used == 14);
                gte_encode_ub(gte, 0, 4, &n_used, &clause_counter, &n_clauses);
                assert(n_used == 14);
                gte_drop(gte);
                return 0;
            }
        })
        .success();
    }
}
