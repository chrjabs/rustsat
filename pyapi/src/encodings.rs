//! # Python API for RustSAT Encodings

use pyo3::prelude::*;

use rustsat::encodings::EnforceError;

pub mod am1;
pub mod card;
pub mod pb;

#[allow(clippy::needless_pass_by_value)]
fn convert_enforce_error(err: EnforceError) -> PyErr {
    match err {
        EnforceError::NotEncoded => {
            pyo3::exceptions::PyRuntimeError::new_err("not encoded to enforce bound")
        }
        EnforceError::Unsat => pyo3::exceptions::PyValueError::new_err("encoding is unsat"),
    }
}
