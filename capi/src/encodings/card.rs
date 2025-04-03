//! # Cardinality Encodings

use std::ffi::{c_int, c_void};

use rustsat::{
    encodings::card::{
        BoundLower, BoundLowerIncremental, BoundUpper, BoundUpperIncremental, EncodeIncremental,
        Totalizer,
    },
    types::Lit,
};

use super::{CClauseCollector, ClauseCollector, MaybeError, VarManager};

macro_rules! implement_capi {
    (basics, $type:ty, $id:ident) => {
        #[unsafe(export_name = concat!(stringify!($id), "_new"))]
        #[doc = concat!(" Creates a new [`", stringify!($type), "`] cadinality encoding")]
        #[allow(clippy::missing_safety_doc)]
        #[must_use]
        pub unsafe extern "C" fn new() -> *mut $type {
            Box::into_raw(Box::default())
        }

        #[unsafe(export_name = concat!(stringify!($id), "_drop"))]
        #[doc = concat!(" Frees memory associated with a [`", stringify!($type), "`]")]
        #[doc = ""]
        #[doc = " # Safety"]
        #[doc = ""]
        #[doc = concat!(" `", stringify!($id), "` must be a return value of [`", stringify!($id), "_new`] and cannot be used afterwards again.")]
        #[must_use]
        pub unsafe extern "C" fn drop($id: *mut $type) {
            drop(Box::from_raw($id));
        }

        #[doc = concat!(" Adds a new input literal to a [`", stringify!($type), "`]")]
        #[doc = ""]
        #[doc = " # Errors"]
        #[doc = ""]
        #[doc = " - If `lit` is not a valid IPASIR-style literal (e.g., `lit = 0`),"]
        #[doc = "     [`MaybeError::InvalidLiteral`] is returned"]
        #[doc = ""]
        #[doc = " # Safety"]
        #[doc = ""]
        #[doc = " `tot` must be a return value of [`tot_new`] that [`tot_drop`] has not yet been called on."]
        #[no_mangle]
        pub unsafe extern "C" fn add(tot: *mut Totalizer, lit: c_int) -> MaybeError {
            let Ok(lit) = Lit::from_ipasir(lit) else {
                return MaybeError::InvalidLiteral;
            };
            (*tot).extend([lit]);
            MaybeError::Ok
        }

        #[unsafe(export_name = concat!(stringify!($id), "_reserve"))]
        #[doc = " Reserves all auxiliary variables that the encoding might need"]
        #[doc = ""]
        #[doc = concat!(" All calls to [`", stringify!($id), "_encode_ub`] following a call to this function are guaranteed to not increase")]
        #[doc = concat!(" the value of `n_vars_used`. This does _not_ hold if [`", stringify!($id), "_add`] is called in between")]
        #[doc = ""]
        #[doc = " # Safety"]
        #[doc = ""]
        #[doc = concat!(" `", stringify!($id), "` must be a return value of [`", stringify!($id), "_new`] that [`", stringify!($id), "_drop`] has not yet been called on.")]
        pub unsafe extern "C" fn reserve(tot: *mut Totalizer, n_vars_used: &mut u32) {
            let mut var_manager = VarManager::new(n_vars_used);
            (*tot).reserve(&mut var_manager);
        }
    };
}

use implement_capi;

mod totalizer {
    use super::*;

    use rustsat::encodings::card::Totalizer;

    implement_capi!(basics, Totalizer, tot);
}
