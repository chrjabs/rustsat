//! # Totalizer C-API

use std::ffi::{c_int, c_void};

use rustsat::{
    encodings::card::{BoundUpper, BoundUpperIncremental, DbTotalizer},
    types::Lit,
};

use super::{CClauseCollector, ClauseCollector, MaybeError, VarManager};

/// Creates a new [`DbTotalizer`] cardinality encoding
#[no_mangle]
pub extern "C" fn tot_new() -> *mut DbTotalizer {
    Box::into_raw(Box::default())
}

/// Adds a new input literal to a [`DbTotalizer`]
///
/// # Errors
///
/// - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
///     [`MaybeError::InvalidLiteral`] is returned
///
/// # Safety
///
/// `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
///
/// # Panics
///
/// If the passed `lit` is an invalid IPASIR literal
#[no_mangle]
pub unsafe extern "C" fn tot_add(tot: *mut DbTotalizer, lit: c_int) -> MaybeError {
    let Ok(lit) = Lit::from_ipasir(lit) else {
        return MaybeError::InvalidLiteral;
    };
    unsafe { (*tot).extend([lit]) };
    MaybeError::Ok
}

/// Lazily builds the _change in_ cardinality encoding to enable upper bounds in a given range. A
/// change might be added literals or changed bounds.
///
/// The min and max bounds are inclusive. After a call to [`tot_encode_ub`] with `min_bound=2` and
/// `max_bound=4` bound including `<= 2` and `<= 4` can be enforced.
///
/// A call to `var_manager` must yield a new variable. The encoding will be returned via the given
/// callback function as 0-terminated clauses (in the same way as IPASIR's `add`).
///
/// # Safety
///
/// `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
///
/// # Panics
///
/// If `min_bound > max_bound`.
#[no_mangle]
pub unsafe extern "C" fn tot_encode_ub(
    tot: *mut DbTotalizer,
    min_bound: usize,
    max_bound: usize,
    n_vars_used: &mut u32,
    collector: CClauseCollector,
    collector_data: *mut c_void,
) {
    assert!(min_bound <= max_bound);
    let mut collector = ClauseCollector::new(collector, collector_data);
    let mut var_manager = VarManager::new(n_vars_used);
    unsafe { (*tot).encode_ub_change(min_bound..=max_bound, &mut collector, &mut var_manager) }
        .expect("clause collector returned out of memory");
}

/// Returns an assumption/unit for enforcing an upper bound (`sum of lits <= ub`). Make sure that
/// [`tot_encode_ub`] has been called adequately and nothing has been called afterwards, otherwise
/// [`MaybeError::NotEncoded`] will be returned.
///
/// # Safety
///
/// `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on.
#[no_mangle]
pub unsafe extern "C" fn tot_enforce_ub(
    tot: *mut DbTotalizer,
    ub: usize,
    assump: &mut c_int,
) -> MaybeError {
    match unsafe { (*tot).enforce_ub(ub) } {
        Ok(assumps) => {
            debug_assert_eq!(assumps.len(), 1);
            *assump = assumps[0].to_ipasir();
            MaybeError::Ok
        }
        Err(err) => err.into(),
    }
}

/// Frees the memory associated with a [`DbTotalizer`]
///
/// # Safety
///
/// `tot` must be a return value of [`tot_new`] and cannot be used afterwards again.
#[no_mangle]
pub unsafe extern "C" fn tot_drop(tot: *mut DbTotalizer) {
    drop(unsafe { Box::from_raw(tot) });
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
                DbTotalizer *tot = tot_new();
                assert(tot != NULL);
                tot_drop(tot);
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
                DbTotalizer *tot = tot_new();
                tot_add(tot, 1);
                tot_add(tot, 2);
                tot_add(tot, 3);
                tot_add(tot, 4);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                tot_encode_ub(tot, 0, 4, &n_used, &clause_counter, &n_clauses);
                tot_drop(tot);
                assert(n_used == 12);
                assert(n_clauses == 14);
                return 0;
            }
        })
        .success();
    }
}
