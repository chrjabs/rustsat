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

#![warn(missing_docs)]

use pyo3::{prelude::*, types::PySlice};

mod encodings;
mod instances;
mod types;

use crate::{
    encodings::{DynamicPolyWatchdog, GeneralizedTotalizer, Totalizer},
    instances::{Cnf, VarManager},
    types::{Clause, Lit},
};

#[derive(FromPyObject)]
pub(crate) enum SliceOrInt<'a> {
    Slice(&'a PySlice),
    Int(isize),
}

pub(crate) enum SingleOrList<T> {
    Single(T),
    List(Vec<T>),
}

impl<T> IntoPy<PyObject> for SingleOrList<T>
where
    T: IntoPy<PyObject>,
{
    fn into_py(self, py: Python<'_>) -> PyObject {
        match self {
            SingleOrList::Single(single) => single.into_py(py),
            SingleOrList::List(list) => list.into_py(py),
        }
    }
}

/// Python bindings for the RustSAT library
#[pymodule]
fn rustsat(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Lit>()?;
    m.add_class::<Clause>()?;
    m.add_class::<Cnf>()?;
    m.add_class::<VarManager>()?;

    let encodings = PyModule::new_bound(py, "rustsat.encodings")?;
    encodings.add_class::<Totalizer>()?;
    encodings.add_class::<GeneralizedTotalizer>()?;
    encodings.add_class::<DynamicPolyWatchdog>()?;
    m.add("encodings", &encodings)?;

    // To import encodings. Fix from https://github.com/PyO3/pyo3/issues/759
    py.import_bound("sys")?
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
