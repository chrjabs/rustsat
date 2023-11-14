//! # Python API for RustSAT
//!
//! This is the Python API for RustSAT. Currently this API is very minimal and
//! not the focus of this project. For now, only the API of certain encodings is
//! available.

use pyo3::prelude::*;

use crate::{
    encodings::card::DbTotalizer,
    instances::Cnf,
    types::{Clause, Lit},
};

#[pymodule]
fn rustsat(_py: Python<'_>, m: &PyModule) -> PyResult<()> {
    m.add_class::<Lit>()?;
    m.add_class::<Clause>()?;
    m.add_class::<Cnf>()?;
    m.add_class::<DbTotalizer>()?;
    Ok(())
}
