//! # C-API For RustSAT
//!
//! In the C-API, literals are represented as IPASIR literals.
//!
//! This is the C-API for RustSAT. Currently this API is very minimal and not the focus of this
//! project. For now, only the API of certain encodings is available.
//!
//! For the API itself, see `rustsat.h`. To use RustSAT from an external project, build this crate
//! and link against `librustsat_capi.a` (produced by `cargo` in `target/release`).

pub mod encodings {
    //! # C-API For Encodings

    use std::ffi::{c_int, c_void};

    use rustsat::{
        encodings::{self, CollectClauses},
        instances::ManageVars,
        types::{Clause, Var},
    };

    #[repr(C)]
    pub enum MaybeError {
        /// No error
        Ok = 0,
        /// Encode was not called before using the encoding
        NotEncoded,
        /// The requested encoding is unsatisfiable
        Unsat,
        /// The encoding is in an invalid state to perform this action
        InvalidState,
        /// Invalid IPASIR-style literal
        InvalidLiteral,
        /// Precision divisor is not a power of 2
        PrecisionNotPow2,
        /// Attempting to decrease precision
        PrecisionDecreased,
    }

    impl From<encodings::Error> for MaybeError {
        fn from(value: encodings::Error) -> Self {
            match value {
                encodings::Error::NotEncoded => MaybeError::NotEncoded,
                encodings::Error::Unsat => MaybeError::Unsat,
            }
        }
    }

    impl From<Result<(), encodings::pb::dpw::PrecisionError>> for MaybeError {
        fn from(value: Result<(), encodings::pb::dpw::PrecisionError>) -> Self {
            match value {
                Ok(_) => MaybeError::Ok,
                Err(err) => match err {
                    encodings::pb::dpw::PrecisionError::NotPow2 => MaybeError::PrecisionNotPow2,
                    encodings::pb::dpw::PrecisionError::PrecisionDecreased => {
                        MaybeError::PrecisionDecreased
                    }
                },
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

        fn extend_clauses<T>(&mut self, cl_iter: T) -> Result<(), rustsat::OutOfMemory>
        where
            T: IntoIterator<Item = Clause>,
        {
            cl_iter.into_iter().for_each(|cl| {
                cl.into_iter()
                    .for_each(|l| (self.ccol)(l.to_ipasir(), self.cdata));
                (self.ccol)(0, self.cdata);
            });
            Ok(())
        }

        fn add_clause(&mut self, cl: Clause) -> Result<(), rustsat::OutOfMemory> {
            cl.into_iter()
                .for_each(|l| (self.ccol)(l.to_ipasir(), self.cdata));
            (self.ccol)(0, self.cdata);
            Ok(())
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
        ///   [`MaybeError::InvalidLiteral`] is returned
        ///
        /// # Safety
        ///
        /// `tot` must be a return value of [`tot_new`] that [`tot_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn tot_add(tot: *mut DbTotalizer, lit: c_int) -> MaybeError {
            let mut boxed = unsafe { Box::from_raw(tot) };
            let lit = if let Ok(lit) = Lit::from_ipasir(lit) {
                lit
            } else {
                return MaybeError::InvalidLiteral;
            };
            boxed.extend([lit]);
            Box::into_raw(boxed);
            MaybeError::Ok
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
            boxed
                .encode_ub_change(min_bound..=max_bound, &mut collector, &mut var_manager)
                .expect("clause collector returned out of memory");
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

        use rustsat::{
            encodings::pb::{BoundUpper, BoundUpperIncremental, DynamicPolyWatchdog},
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
        ///   [`MaybeError::InvalidLiteral`] is returned
        /// - If a literal is added _after_ the encoding is build, [`MaybeError::InvalidState`] is
        ///   returned
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
            let lit = if let Ok(lit) = Lit::from_ipasir(lit) {
                lit
            } else {
                return MaybeError::InvalidLiteral;
            };
            let res = boxed.add_input(lit, weight);
            Box::into_raw(boxed);
            if res.is_ok() {
                MaybeError::Ok
            } else {
                MaybeError::InvalidState
            }
        }

        /// Lazily builds the _change in_ pseudo-boolean encoding to enable
        /// upper bounds from within the range. A change might only be a change
        /// in bounds, the [`DynamicPolyWatchdog`] does not support adding
        /// literals at the moment.
        ///
        /// The min and max bounds are inclusive. After a call to
        /// [`dpw_encode_ub`] with `min_bound=2` and `max_bound=4`, bounds
        /// satisfying `2 <= bound <= 4` can be enforced.
        ///
        /// Clauses are returned via the `collector`. The `collector` function should expect
        /// clauses to be passed similarly to `ipasir_add`, as a 0-terminated sequence of literals
        /// where the literals are passed as the first argument and the `collector_data` as a
        /// second.
        ///
        /// `n_vars_used` must be the number of variables already used and will be incremented by
        /// the number of variables used up in the encoding.
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
            boxed
                .encode_ub_change(min_bound..=max_bound, &mut collector, &mut var_manager)
                .expect("clause collector returned out of memory");
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

        /// Set the precision at which to build the encoding at. With `divisor = 8` the encoding will
        /// effectively be built such that the weight of every input literal is divided by `divisor`
        /// (interger division, rounding down). Divisor values must be powers of 2. After building
        /// the encoding, the precision can only be increased, i.e., only call this function with
        /// _decreasing_ divisor values.
        ///
        /// # Errors
        ///
        /// - If `divisor` is not a power of 2, [`MaybeError::PrecisionNotPow2`] is returned
        /// - If `divisor` is larger than the last divisor, i.e., precision is attemted to be
        ///   decreased, [`MaybeError::PrecisionDecreased`] is returned
        ///
        /// # Safety
        ///
        /// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn dpw_set_precision(
            dpw: *mut DynamicPolyWatchdog,
            divisor: usize,
        ) -> MaybeError {
            let mut boxed = unsafe { Box::from_raw(dpw) };
            let ret = boxed.set_precision(divisor).into();
            Box::into_raw(boxed);
            ret
        }

        /// Gets the next possible precision divisor value
        ///
        /// Note that this is not the next possible precision value from the last _set_ precision but
        /// from the last _encoded_ precision. The divisor value will always be a power of two so that
        /// calling `set_precision` and then encoding will produce the smalles non-empty next segment
        /// of the encoding.
        ///
        /// # Safety
        ///
        /// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn dpw_next_precision(dpw: *mut DynamicPolyWatchdog) -> usize {
            let boxed = unsafe { Box::from_raw(dpw) };
            let ret = boxed.next_precision();
            Box::into_raw(boxed);
            ret
        }

        /// Checks whether the encoding is already at the maximum precision
        ///
        /// # Safety
        ///
        /// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
        /// not yet been called on.
        #[no_mangle]
        pub unsafe extern "C" fn dpw_is_max_precision(dpw: *mut DynamicPolyWatchdog) -> bool {
            let boxed = unsafe { Box::from_raw(dpw) };
            let ret = boxed.is_max_precision();
            Box::into_raw(boxed);
            ret
        }

        /// Given a range of output values to limit the encoding to, returns additional clauses that
        /// "shrink" the encoding through hardening
        ///
        /// The output value range must be a range considering _all_ input literals, not only the
        /// encoded ones.
        ///
        /// This is intended for, e.g., a MaxSAT solving application where a global lower bound is
        /// derived and parts of the encoding can be hardened.
        ///
        /// The min and max bounds are inclusive. After a call to [`dpw_limit_range`] with
        /// `min_value=2` and `max_value=4`, the encoding is valid for the value range `2 <= range
        /// <= 4`.
        ///
        /// To not specify a bound, pass `0` for the lower bound or `SIZE_MAX` for the upper bound.
        ///
        /// Clauses are returned via the `collector`. The `collector` function should expect
        /// clauses to be passed similarly to `ipasir_add`, as a 0-terminated sequence of literals
        /// where the literals are passed as the first argument and the `collector_data` as a
        /// second.
        ///
        /// # Safety
        ///
        /// `dpw` must be a return value of [`dpw_new`] that [`dpw_drop`] has
        /// not yet been called on.
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
            let boxed = unsafe { Box::from_raw(dpw) };
            boxed
                .limit_range(min_value..=max_value, &mut collector)
                .expect("clause collector returned out of memory");
            Box::into_raw(boxed);
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
                        assert(dpw_add(dpw, 1, 5) == Ok);
                        assert(dpw_add(dpw, 2, 3) == Ok);
                        assert(dpw_add(dpw, 3, 8) == Ok);
                        assert(dpw_add(dpw, 4, 7) == Ok);
                        int n_used = 4;
                        int n_clauses = 0;
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
    }
}
