//! # Commander At-Most-One C-API

use std::ffi::{c_int, c_void};

use rustsat::{
    encodings::am1::{self, Encode},
    types::Lit,
};

use super::{CClauseCollector, ClauseCollector, MaybeError, VarManager};

/// Implementations of the commander at-most-1 encoding.
///
/// The sub encoding is fixed to the pairwise encoding and the size of the splits to 4.
///
/// # References
///
/// - Will Klieber and Gihwon Kwon: _Efficient CNF Encoding for Selecting 1 from N Objects, CFV
///   2007.
#[derive(Default)]
pub struct Commander(am1::Commander);

/// Creates a new [`Commander`] at-most-one encoding
#[no_mangle]
#[allow(clippy::missing_safety_doc)]
pub unsafe extern "C" fn commander_new() -> *mut Commander {
    Box::into_raw(Box::default())
}

/// Adds a new input literal to a [`Commander`]
///
/// # Errors
///
/// - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),
///     [`MaybeError::InvalidLiteral`] is returned
///
/// # Safety
///
/// `commander` must be a return value of [`commander_new`] that [`commander_drop`] has not yet been
/// called on
#[no_mangle]
pub unsafe extern "C" fn commander_add(commander: *mut Commander, lit: c_int) -> MaybeError {
    let Ok(lit) = Lit::from_ipasir(lit) else {
        return MaybeError::InvalidLiteral;
    };
    (*commander).0.extend([lit]);
    MaybeError::Ok
}

/// Builds the commander at-most-one encoding
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
/// `commander` must be a return value of [`commander_new`] that [`commander_drop`] has not yet been called on.
///
/// # Panics
///
/// If the encoding ran out of memory
#[no_mangle]
pub unsafe extern "C" fn commander_encode(
    commander: *mut Commander,
    n_vars_used: &mut u32,
    collector: CClauseCollector,
    collector_data: *mut c_void,
) {
    let mut collector = ClauseCollector::new(collector, collector_data);
    let mut var_manager = VarManager::new(n_vars_used);
    (*commander)
        .0
        .encode(&mut collector, &mut var_manager)
        .expect("clause collector returned out of memory");
}

/// Frees the memory associated with a [`Commander`]
///
/// # Safety
///
/// `commander` must be a return value of [`commander_new`] and cannot be used afterwards again.
#[no_mangle]
pub unsafe extern "C" fn commander_drop(commander: *mut Commander) {
    drop(Box::from_raw(commander));
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
                Commander *commander = commander_new();
                assert(commander != NULL);
                commander_drop(commander);
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
                Commander *commander = commander_new();
                assert(commander_add(commander, 1) == Ok);
                assert(commander_add(commander, 2) == Ok);
                assert(commander_add(commander, 3) == Ok);
                assert(commander_add(commander, 4) == Ok);
                uint32_t n_used = 4;
                uint32_t n_clauses = 0;
                commander_encode(commander, &n_used, &clause_counter, &n_clauses);
                commander_drop(commander);
                assert(n_used == 5);
                assert(n_clauses == 10);
                return 0;
            }
        })
        .success();
    }
}
