//! # Python API for RustSAT
//!
//! This is the Python API for RustSAT. Currently this API is very minimal and
//! not the focus of this project. For now, only the API of certain encodings is
//! available.
//!
//! ## Installation
//!
//! The Python bindings can be installed from [PyPI](https://pypi.org/project/rustsat/).
//!
//! ## Documentation
//!
//! Documentation for this API can be found [here](https://christophjabs.info/rustsat/pyapi/).

#![warn(clippy::pedantic)]
#![warn(missing_docs)]
#![allow(clippy::trivially_copy_pass_by_ref)]

use pyo3::prelude::*;

mod encodings;
mod instances;
mod types;

use crate::{
    encodings::{DynamicPolyWatchdog, GeneralizedTotalizer, Totalizer},
    instances::{Cnf, VarManager},
    types::{Clause, Lit},
};

#[derive(IntoPyObject)]
pub(crate) enum SingleOrList<T> {
    Single(T),
    List(Vec<T>),
}

/// Python bindings for the RustSAT library
#[pymodule]
fn rustsat(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Lit>()?;
    m.add_class::<Clause>()?;
    m.add_class::<Cnf>()?;
    m.add_class::<VarManager>()?;

    let encodings = PyModule::new(py, "rustsat.encodings")?;
    encodings.add_class::<Totalizer>()?;
    encodings.add_class::<GeneralizedTotalizer>()?;
    encodings.add_class::<DynamicPolyWatchdog>()?;
    m.add("encodings", &encodings)?;

    // To import encodings. Fix from https://github.com/PyO3/pyo3/issues/759
    py.import("sys")?
        .getattr("modules")?
        .set_item("rustsat.encodings", &encodings)?;

    Ok(())
}

macro_rules! handle_oom {
    ($result:expr) => {{
        match $result {
            Ok(val) => val,
            Err(err) => return Err(pyo3::exceptions::PyMemoryError::new_err(format!("{}", err))),
        }
    }};
}
pub(crate) use handle_oom;
