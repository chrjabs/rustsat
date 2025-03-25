//! # Pairwise At-Most-One C-API

use std::ffi::{c_int, c_void};

use rustsat::{
    encodings::am1::{Encode, Pairwise},
    types::Lit,
};

use super::{CClauseCollector, ClauseCollector, MaybeError, VarManager};

/// Creates a new [`Pairwise`] at-most-one encoding
#[no_mangle]
#[allow(clippy::missing_safety_doc)]
pub unsafe extern "C" fn pairwise_new() -> *mut Pairwise {
    Box::into_raw(Box::default())
}

/// Adds a new input literal to a [`Pairwise`]
///
/// # Errors
///
/// - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
///     [`MaybeError::InvalidLiteral`] is returned
///
/// # Safety
///
/// `pairwise` must be a return value of [`pairwise_new`] that [`pairwise_drop`] has not yet been
/// called on
#[no_mangle]
pub unsafe extern "C" fn pairwise_add(pairwise: *mut Pairwise, lit: c_int) -> MaybeError {
    let Ok(lit) = Lit::from_ipasir(lit) else {
        return MaybeError::InvalidLiteral;
    };
    (*pairwise).extend([lit]);
    MaybeError::Ok
}

/// Builds the pairwise at-most-one encoding
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
/// `pairwise` must be a return value of [`pairwise_new`] that [`pairwise_drop`] has not yet been called on.
///
/// # Panics
///
/// If the encoding ran out of memory
#[no_mangle]
pub unsafe extern "C" fn pairwise_encode(
    pairwise: *mut Pairwise,
    n_vars_used: &mut u32,
    collector: CClauseCollector,
    collector_data: *mut c_void,
) {
    let mut collector = ClauseCollector::new(collector, collector_data);
    let mut var_manager = VarManager::new(n_vars_used);
    (*pairwise)
        .encode(&mut collector, &mut var_manager)
        .expect("clause collector returned out of memory");
}

/// Frees the memory associated with a [`Pairwise`]
///
/// # Safety
///
/// `pairwise` must be a return value of [`pairwise_new`] and cannot be used afterwards again.
#[no_mangle]
pub unsafe extern "C" fn pairwise_drop(pairwise: *mut Pairwise) {
    drop(Box::from_raw(pairwise));
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
                Pairwise *pairwise = pairwise_new();
                assert(pairwise != NULL);
                pairwise_drop(pairwise);
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
                Pairwise *pairwise = pairwise_new();
                assert(pairwise_add(pairwise, 1) == Ok);
                assert(pairwise_add(pairwise, 2) == Ok);
                assert(pairwise_add(pairwise, 3) == Ok);
                assert(pairwise_add(pairwise, 4) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                pairwise_encode(pairwise, &n_used, &clause_counter, &n_clauses);
                pairwise_drop(pairwise);
                assert(n_used == 4);
                assert(n_clauses == 6);
                return 0;
            }
        })
        .success();
    }
}
