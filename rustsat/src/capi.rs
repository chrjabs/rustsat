//! # C-API For RustSAT
//!
//! In the C-API, literals are represented as IPASIR literals.
//!
//! This is the C-API for RustSAT. Currently this API is very minimal and not
//! the focus of this project. For now, only the API of certain encodings is
//! available.

pub mod encodings {
    //! # C-API For Encodings

    use std::ffi::{c_int, c_void};

    use crate::{
        encodings::{self, CollectClauses},
        instances::ManageVars,
        types::{Clause, Var},
    };

    #[repr(C)]
    pub enum MaybeError {
        /// No error
        Ok,
        /// Encode was not called before using the encoding
        NotEncoded,
        /// The requested encoding is unsatisfiable
        Unsat,
        /// The encoding is in an invalid state to perform this action
        InvalidState,
    }

    impl From<encodings::Error> for MaybeError {
        fn from(value: encodings::Error) -> Self {
            match value {
                encodings::Error::NotEncoded => MaybeError::NotEncoded,
                encodings::Error::Unsat => MaybeError::Unsat,
            }
        }
    }

    pub type CClauseCollector = extern "C" fn(lit: c_int, data: *mut c_void);
    pub type CAssumpCollector = extern "C" fn(lit: c_int, data: *mut c_void);

    struct ClauseCollector {
        n_clauses: usize,
        ccol: CClauseCollector,
        cdata: *mut c_void,
    }

    impl ClauseCollector {
        pub fn new(ccol: CClauseCollector, cdata: *mut c_void) -> Self {
            Self {
                n_clauses: 0,
                ccol,
                cdata,
            }
        }
    }

    impl CollectClauses for ClauseCollector {
        fn n_clauses(&self) -> usize {
            self.n_clauses
        }
    }

    impl Extend<Clause> for ClauseCollector {
        fn extend<T: IntoIterator<Item = Clause>>(&mut self, iter: T) {
            iter.into_iter().for_each(|cl| {
                cl.into_iter()
                    .for_each(|l| (self.ccol)(l.to_ipasir(), self.cdata));
                (self.ccol)(0, self.cdata);
            })
        }
    }

    struct VarManager<'a> {
        n_vars_used: &'a mut c_int,
    }

    impl<'a> VarManager<'a> {
        pub fn new(n_vars_used: &'a mut c_int) -> Self {
            Self { n_vars_used }
        }
    }

    impl<'a> ManageVars for VarManager<'a> {
        fn new_var(&mut self) -> Var {
            let var = Var::new(*self.n_vars_used as u32);
            *self.n_vars_used += 1;
            var
        }

        fn max_var(&self) -> Option<Var> {
            if *self.n_vars_used == 0 {
                None
            } else {
                Some(Var::new(*self.n_vars_used as u32) - 1)
            }
        }

        fn increase_next_free(&mut self, v: Var) -> bool {
            let v_idx = v.idx32();
            if v_idx > *self.n_vars_used as u32 {
                *self.n_vars_used = v_idx as c_int;
                return true;
            }
            false
        }

        fn combine(&mut self, _other: Self)
        where
            Self: Sized,
        {
            panic!("cannot combine this var manager")
        }

        fn n_used(&self) -> u32 {
            *self.n_vars_used as u32
        }

        fn forget_from(&mut self, min_var: Var) {
            *self.n_vars_used =
                std::cmp::min(*self.n_vars_used, min_var.idx32().try_into().unwrap())
        }
    }

    pub mod totalizer {
        //! # Totalizer C-API

        use std::ffi::{c_int, c_void};

        use crate::{
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
        /// # Safety
        ///
        /// `tot` must be a return value of [`tot_new`] that [`tot_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn tot_add(tot: *mut DbTotalizer, lit: c_int) {
            let mut boxed = unsafe { Box::from_raw(tot) };
            boxed.extend([Lit::from_ipasir(lit).expect("invalid IPASIR literal")]);
            Box::into_raw(boxed);
        }

        /// Lazily builds the _change in_ cardinality encoding to enable upper
        /// bounds in a given range. A change might be added literals or changed
        /// bounds.
        ///
        /// The min and max bounds are inclusive. After a call to
        /// [`tot_encode_ub`] with `min_bound=2` and `max_bound=4` bound
        /// including `<= 2` and `<= 4` can be enforced.
        ///
        /// A call to `var_manager` must yield a new variable. The
        /// encoding will be returned via the given callback function as
        /// 0-terminated clauses (in the same way as IPASIR's `add`).
        ///
        /// # Safety
        ///
        /// `tot` must be a return value of [`tot_new`] that [`tot_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn tot_encode_ub(
            tot: *mut DbTotalizer,
            min_bound: usize,
            max_bound: usize,
            n_vars_used: &mut c_int,
            collector: CClauseCollector,
            collector_data: *mut c_void,
        ) {
            assert!(min_bound <= max_bound);
            let mut collector = ClauseCollector::new(collector, collector_data);
            let mut var_manager = VarManager::new(n_vars_used);
            let mut boxed = unsafe { Box::from_raw(tot) };
            boxed.encode_ub_change(min_bound..=max_bound, &mut collector, &mut var_manager);
            Box::into_raw(boxed);
        }

        /// Returns an assumption/unit for enforcing an upper bound (`sum of
        /// lits <= ub`). Make sure that [`tot_encode_ub`] has been called
        /// adequately and nothing has been called afterwards, otherwise
        /// [`MaybeError::NotEncoded`] will be returned.
        ///
        /// # Safety
        ///
        /// `tot` must be a return value of [`tot_new`] that [`tot_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn tot_enforce_ub(
            tot: *mut DbTotalizer,
            ub: usize,
            assump: &mut c_int,
        ) -> MaybeError {
            let boxed = unsafe { Box::from_raw(tot) };
            let ret = match boxed.enforce_ub(ub) {
                Ok(assumps) => {
                    debug_assert_eq!(assumps.len(), 1);
                    *assump = assumps[0].to_ipasir();
                    MaybeError::Ok
                }
                Err(err) => err.into(),
            };
            Box::into_raw(boxed);
            ret
        }

        /// Frees the memory associated with a [`DbTotalizer`]
        ///
        /// # Safety
        ///
        /// `tot` must be a return value of [`tot_new`] and cannot be used
        /// afterwards again.
        #[no_mangle]
        pub unsafe extern "C" fn tot_drop(tot: *mut DbTotalizer) {
            drop(unsafe { Box::from_raw(tot) })
        }

        #[cfg(test)]
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
                        int n_used = 4;
                        int n_clauses = 0;
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
    }

    mod dpw {
        //! # Dynamic Poly Watchdog C-API

        use std::ffi::{c_int, c_void};

        use crate::{
            encodings::pb::{BoundUpper, BoundUpperIncremental, DynamicPolyWatchdog},
            types::Lit,
        };

        use super::{CAssumpCollector, CClauseCollector, ClauseCollector, MaybeError, VarManager};

        /// Creates a new [`DynamicPolyWatchdog`] cardinality encoding
        #[no_mangle]
        pub extern "C" fn dpw_new() -> *mut DynamicPolyWatchdog {
            Box::into_raw(Box::default())
        }

        /// Adds a new input literal to a [`DynamicPolyWatchdog`]. Input
        /// literals can only be added _before_ the encoding is built for the
        /// first time. Otherwise [`MaybeError::InvalidState`] is returned.
        ///
        /// # Safety
        ///
        /// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn dpw_add(
            dpw: *mut DynamicPolyWatchdog,
            lit: c_int,
            weight: usize,
        ) -> MaybeError {
            let mut boxed = unsafe { Box::from_raw(dpw) };
            if boxed.structure.is_some() {
                return MaybeError::InvalidState;
            }
            boxed.in_lits.insert(
                Lit::from_ipasir(lit).expect("invalid IPASIR literal"),
                weight,
            );
            boxed.weight_sum += weight;
            Box::into_raw(boxed);
            MaybeError::Ok
        }

        /// Lazily builds the _change in_ pseudo-boolean encoding to enable
        /// upper bounds from within the range. A change might only be a change
        /// in bounds, the [`DynamicPolyWatchdog`] does not support adding
        /// literals at the moment.
        ///
        /// The min and max bounds are inclusive. After a call to
        /// [`dpw_encode_ub`] with `min_bound=2` and `max_bound=4` bound
        /// including `<= 2` and `<= 4` can be enforced.
        ///
        /// A call to `var_manager` must yield a new variable. The
        /// encoding will be returned via the given callback function as
        /// 0-terminated clauses (in the same way as IPASIR's `add`).
        ///
        /// # Safety
        ///
        /// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn dpw_encode_ub(
            dpw: *mut DynamicPolyWatchdog,
            min_bound: usize,
            max_bound: usize,
            n_vars_used: &mut c_int,
            collector: CClauseCollector,
            collector_data: *mut c_void,
        ) {
            assert!(min_bound <= max_bound);
            let mut collector = ClauseCollector::new(collector, collector_data);
            let mut var_manager = VarManager::new(n_vars_used);
            let mut boxed = unsafe { Box::from_raw(dpw) };
            boxed.encode_ub_change(min_bound..=max_bound, &mut collector, &mut var_manager);
            Box::into_raw(boxed);
        }

        /// Returns assumptions/units for enforcing an upper bound (`sum of lits
        /// <= ub`). Make sure that [`dpw_encode_ub`] has been called adequately
        /// and nothing has been called afterwards, otherwise
        /// [`MaybeError::NotEncoded`] will be returned.
        ///
        /// Assumptions are returned via the collector callback. There is _no_
        /// terminating zero, all assumptions are passed when [`dpw_enforce_ub`]
        /// returns.
        ///
        /// # Safety
        ///
        /// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn dpw_enforce_ub(
            dpw: *mut DynamicPolyWatchdog,
            ub: usize,
            collector: CAssumpCollector,
            collector_data: *mut c_void,
        ) -> MaybeError {
            let boxed = unsafe { Box::from_raw(dpw) };
            let ret = match boxed.enforce_ub(ub) {
                Ok(assumps) => {
                    assumps.into_iter().for_each(|l| {
                        collector(l.to_ipasir(), collector_data);
                    });
                    MaybeError::Ok
                }
                Err(err) => err.into(),
            };
            Box::into_raw(boxed);
            ret
        }

        /// Gets the next smaller upper bound value that can be encoded without
        /// setting tares. This is used for coarse convergence.
        ///
        /// # Safety
        ///
        /// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn dpw_coarse_ub(dpw: *mut DynamicPolyWatchdog, ub: usize) -> usize {
            let boxed = unsafe { Box::from_raw(dpw) };
            let ret = boxed.coarse_ub(ub);
            Box::into_raw(boxed);
            ret
        }

        /// Frees the memory associated with a [`DynamicPolyWatchdog`]
        ///
        /// # Safety
        ///
        /// `dpw` must be a return value of [`dpw_new`] and cannot be used
        /// afterwards again.
        #[no_mangle]
        pub unsafe extern "C" fn dpw_drop(dpw: *mut DynamicPolyWatchdog) {
            drop(unsafe { Box::from_raw(dpw) })
        }

        #[cfg(test)]
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
                        dpw_add(dpw, 1, 1);
                        dpw_add(dpw, 2, 1);
                        dpw_add(dpw, 3, 2);
                        dpw_add(dpw, 4, 2);
                        int n_used = 4;
                        int n_clauses = 0;
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
                        dpw_add(dpw, 1, 5);
                        dpw_add(dpw, 2, 3);
                        dpw_add(dpw, 3, 8);
                        dpw_add(dpw, 4, 7);
                        int n_used = 4;
                        int n_clauses = 0;
                        dpw_encode_ub(dpw, 0, 23, &n_used, &clause_counter, &n_clauses);
                        for (size_t ub = 8; ub <= 23; ub++) {
                            size_t coarse_ub = dpw_coarse_ub(dpw, ub);
                            assert(coarse_ub <= ub);
                            int n_assumps = 0;
                            assert(dpw_enforce_ub(dpw, coarse_ub, &assump_counter, &n_assumps) == Ok);
                            assert(n_assumps == 1);
                        }
                    }
                })
                .success();
            }
        }
    }
}
