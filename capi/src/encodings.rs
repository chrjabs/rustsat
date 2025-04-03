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

impl From<encodings::NotEncoded> for MaybeError {
    fn from(_: encodings::NotEncoded) -> Self {
        MaybeError::NotEncoded
    }
}

impl From<encodings::EnforceError> for MaybeError {
    fn from(value: encodings::EnforceError) -> Self {
        match value {
            encodings::EnforceError::NotEncoded => MaybeError::NotEncoded,
            encodings::EnforceError::Unsat => MaybeError::Unsat,
        }
    }
}

impl From<Result<(), encodings::pb::dpw::PrecisionError>> for MaybeError {
    fn from(value: Result<(), encodings::pb::dpw::PrecisionError>) -> Self {
        match value {
            Ok(()) => MaybeError::Ok,
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
        });
    }
}

struct VarManager<'a> {
    n_vars_used: &'a mut u32,
}

impl<'a> VarManager<'a> {
    pub fn new(n_vars_used: &'a mut u32) -> Self {
        Self { n_vars_used }
    }
}

impl ManageVars for VarManager<'_> {
    fn new_var(&mut self) -> Var {
        let var = Var::new(*self.n_vars_used);
        *self.n_vars_used += 1;
        var
    }

    fn max_var(&self) -> Option<Var> {
        if *self.n_vars_used == 0 {
            None
        } else {
            Some(Var::new(*self.n_vars_used) - 1)
        }
    }

    fn increase_next_free(&mut self, v: Var) -> bool {
        let v_idx = v.idx32();
        if v_idx > *self.n_vars_used {
            *self.n_vars_used = v_idx;
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
        *self.n_vars_used
    }

    fn forget_from(&mut self, min_var: Var) {
        *self.n_vars_used = std::cmp::min(*self.n_vars_used, min_var.idx32());
    }
}

/// Implementations of the commander at-most-1 encoding.
///
/// The sub encoding is fixed to the pairwise encoding and the size of the splits to 4.
///
/// # References
///
/// - Will Klieber and Gihwon Kwon: _Efficient CNF Encoding for Selecting 1 from N Objects, CFV
///   2007.
#[derive(Default)]
pub struct Commander(rustsat::encodings::am1::Commander);

/// Implementation of the bimander at-most-1 encoding.
///
/// The sub encoding is fixed to the pairwise encoding and the size of the splits to 4.
///
/// # References
///
/// - Van-Hau Nguyen and Son Thay Mai: _A New Method to Encode the At-Most-One Constraint into SAT,
///   SOICT 2015.
#[derive(Default)]
pub struct Bimander(rustsat::encodings::am1::Bimander);

pub mod am1;
pub mod card;
pub mod dpw;
pub mod pb;
