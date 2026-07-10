//! # Python API for RustSAT Encodings

use pyo3::prelude::*;

pub mod am1;
pub mod card;
pub mod pb;

fn convert_enforce_error(err: rustsat::encodings::EnforceError) -> PyErr {
    match err {
        rustsat::encodings::EnforceError::NotEncoded => {
            pyo3::exceptions::PyRuntimeError::new_err("not encoded to enforce bound")
        }
        rustsat::encodings::EnforceError::Unsat => {
            pyo3::exceptions::PyValueError::new_err("encoding is unsat")
        }
    }
}
