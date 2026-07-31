#![expect(non_camel_case_types)]

use std::os::raw::c_void;

use rustsat::types::Lit;

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

impl From<Lit> for c_Lit {
    fn from(value: Lit) -> Self {
        unsafe { std::mem::transmute::<Lit, c_Lit>(value) }
    }
}

pub extern "C" fn rustsat_minisat_collect_lits(vec: *mut c_void, lit: c_Lit) {
    let vec = vec.cast::<Vec<Lit>>();
    unsafe { (*vec).push(std::mem::transmute::<c_Lit, Lit>(lit)) };
}
