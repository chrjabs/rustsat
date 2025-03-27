//! # Bimander At-Most-One C-API

use std::ffi::{c_int, c_void};

use rustsat::{
    encodings::am1::{self, Encode},
    types::Lit,
};

use super::{CClauseCollector, ClauseCollector, MaybeError, VarManager};

/// Implementation of the bimander at-most-1 encoding.
///
/// The sub encoding is fixed to the pairwise encoding and the size of the splits to 4.
///
/// # References
///
/// - Van-Hau Nguyen and Son Thay Mai: _A New Method to Encode the At-Most-One Constraint into SAT,
///   SOICT 2015.
#[derive(Default)]
pub struct Bimander(am1::Bimander);

/// Creates a new [`Bimander`] at-most-one encoding
#[no_mangle]
#[allow(clippy::missing_safety_doc)]
pub unsafe extern "C" fn bimander_new() -> *mut Bimander {
    Box::into_raw(Box::default())
}

/// Adds a new input literal to a [`Bimander`]
///
/// # Errors
///
/// - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
///     [`MaybeError::InvalidLiteral`] is returned
///
/// # Safety
///
/// `bimander` must be a return value of [`bimander_new`] that [`bimander_drop`] has not yet been
/// called on
#[no_mangle]
pub unsafe extern "C" fn bimander_add(bimander: *mut Bimander, lit: c_int) -> MaybeError {
    let Ok(lit) = Lit::from_ipasir(lit) else {
        return MaybeError::InvalidLiteral;
    };
    (*bimander).0.extend([lit]);
    MaybeError::Ok
}

/// Builds the bimander at-most-one encoding
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
/// `bimander` must be a return value of [`bimander_new`] that [`bimander_drop`] has not yet been called on.
///
/// # Panics
///
/// If the encoding ran out of memory
#[no_mangle]
pub unsafe extern "C" fn bimander_encode(
    bimander: *mut Bimander,
    n_vars_used: &mut u32,
    collector: CClauseCollector,
    collector_data: *mut c_void,
) {
    let mut collector = ClauseCollector::new(collector, collector_data);
    let mut var_manager = VarManager::new(n_vars_used);
    (*bimander)
        .0
        .encode(&mut collector, &mut var_manager)
        .expect("clause collector returned out of memory");
}

/// Frees the memory associated with a [`Bimander`]
///
/// # Safety
///
/// `bimander` must be a return value of [`bimander_new`] and cannot be used afterwards again.
#[no_mangle]
pub unsafe extern "C" fn bimander_drop(bimander: *mut Bimander) {
    drop(Box::from_raw(bimander));
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
                Bimander *bimander = bimander_new();
                assert(bimander != NULL);
                bimander_drop(bimander);
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
                Bimander *bimander = bimander_new();
                assert(bimander_add(bimander, 1) == Ok);
                assert(bimander_add(bimander, 2) == Ok);
                assert(bimander_add(bimander, 3) == Ok);
                assert(bimander_add(bimander, 4) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                bimander_encode(bimander, &n_used, &clause_counter, &n_clauses);
                bimander_drop(bimander);
                assert(n_used == 5);
                assert(n_clauses == 10);
                return 0;
            }
        })
        .success();
    }
}
