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
        types::{Clause, Lit, Var},
    };

    #[repr(C)]
    pub enum MaybeError {
        /// No error
        Ok,
        /// Encode was not called before using the encoding
        NotEncoded,
        /// The requested encoding is unsatisfiable
        Unsat,
    }

    impl From<encodings::Error> for MaybeError {
        fn from(value: encodings::Error) -> Self {
            match value {
                encodings::Error::NotEncoded => MaybeError::NotEncoded,
                encodings::Error::Unsat => MaybeError::NotEncoded,
            }
        }
    }

    pub type CClauseCollector = extern "C" fn(lit: c_int, data: *mut c_void);
    pub type CAssumpCollector = extern "C" fn(lit: c_int, data: *mut c_void);
    pub type CVarManager = extern "C" fn() -> c_int;

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

    struct VarManager {
        max_var: Option<Var>,
        cnew: CVarManager,
    }

    impl VarManager {
        pub fn new(cnew: CVarManager) -> Self {
            Self {
                max_var: None,
                cnew,
            }
        }
    }

    impl ManageVars for VarManager {
        fn new_var(&mut self) -> Var {
            self.max_var = Some(
                Lit::from_ipasir((self.cnew)())
                    .expect("invalid IPASIR lit")
                    .var(),
            );
            self.max_var.unwrap()
        }

        fn max_var(&self) -> Option<Var> {
            self.max_var
        }

        fn increase_next_free(&mut self, _v: Var) -> bool {
            false
        }

        fn combine(&mut self, _other: Self)
        where
            Self: Sized,
        {
            panic!("cannot combine this var manager")
        }

        fn n_used(&self) -> u32 {
            if let Some(mv) = self.max_var {
                mv.idx32() + 1
            } else {
                0
            }
        }
    }

    pub mod totalizer {
        //! # Totalizer C-API

        use std::ffi::{c_int, c_void};

        use crate::{
            encodings::card::{BoundUpper, BoundUpperIncremental, DbTotalizer},
            types::Lit,
        };

        use super::{CClauseCollector, CVarManager, ClauseCollector, MaybeError, VarManager};

        /// Creates a new [`DbTotalizer`] cardinality encoding
        #[no_mangle]
        pub extern "C" fn tot_new() -> *mut DbTotalizer {
            Box::into_raw(Box::new(DbTotalizer::default()))
        }

        /// Adds a new input literal to a [`DbTotalizer`]
        #[no_mangle]
        pub extern "C" fn tot_add(tot: *mut DbTotalizer, lit: c_int) {
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
        #[no_mangle]
        pub extern "C" fn tot_encode_ub(
            tot: *mut DbTotalizer,
            min_bound: usize,
            max_bound: usize,
            var_manager: CVarManager,
            collector: CClauseCollector,
            collector_data: *mut c_void,
        ) {
            assert!(min_bound <= max_bound);
            let mut collector = ClauseCollector::new(collector, collector_data);
            let mut var_manager = VarManager::new(var_manager);
            let mut boxed = unsafe { Box::from_raw(tot) };
            boxed.encode_ub_change(min_bound..max_bound, &mut collector, &mut var_manager);
            Box::into_raw(boxed);
        }

        /// Returns an assumption/unit for enforcing an upper bound (`sum of
        /// lits <= ub`). Make sure that [`tot_encode_ub`] has been called
        /// adequately and nothing has been called afterwards, otherwise
        /// [`MaybeError::NotEncoded`] will be returned.
        #[no_mangle]
        pub extern "C" fn tot_enforce_ub(
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
        #[no_mangle]
        pub extern "C" fn tot_drop(tot: *mut DbTotalizer) {
            drop(unsafe { Box::from_raw(tot) })
        }
    }

    mod dpw {
        //! # Dynamic Poly Watchdog C-API

        use std::ffi::{c_int, c_void};

        use crate::{encodings::pb::{DynamicPolyWatchdog, BoundUpperIncremental, BoundUpper}, types::Lit};

        use super::{
            CAssumpCollector, CClauseCollector, CVarManager, ClauseCollector, MaybeError,
            VarManager,
        };

        /// Creates a new [`DynamicPolyWatchdog`] cardinality encoding
        #[no_mangle]
        pub extern "C" fn dpw_new() -> *mut DynamicPolyWatchdog {
            Box::into_raw(Box::new(DynamicPolyWatchdog::default()))
        }

        /// Adds a new input literal to a [`DynamicPolyWatchdog`]
        #[no_mangle]
        pub extern "C" fn dpw_add(dpw: *mut DynamicPolyWatchdog, lit: c_int, weight: usize) {
            let mut boxed = unsafe { Box::from_raw(dpw) };
            boxed.extend([(
                Lit::from_ipasir(lit).expect("invalid IPASIR literal"),
                weight,
            )]);
            Box::into_raw(boxed);
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
        #[no_mangle]
        pub extern "C" fn dpw_encode_ub(
            dpw: *mut DynamicPolyWatchdog,
            min_bound: usize,
            max_bound: usize,
            var_manager: CVarManager,
            collector: CClauseCollector,
            collector_data: *mut c_void,
        ) {
            assert!(min_bound <= max_bound);
            let mut collector = ClauseCollector::new(collector, collector_data);
            let mut var_manager = VarManager::new(var_manager);
            let mut boxed = unsafe { Box::from_raw(dpw) };
            boxed.encode_ub_change(min_bound..max_bound, &mut collector, &mut var_manager);
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
        #[no_mangle]
        pub extern "C" fn dpw_enforce_ub(
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

        /// Frees the memory associated with a [`DynamicPolyWatchdog`]
        #[no_mangle]
        pub extern "C" fn dpw_drop(dpw: *mut DynamicPolyWatchdog) {
            drop(unsafe { Box::from_raw(dpw) })
        }
    }
}
