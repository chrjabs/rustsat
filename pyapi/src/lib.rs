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
#![expect(clippy::trivially_copy_pass_by_ref)]

use pyo3::prelude::*;

mod encodings;
mod instances;
mod types;

#[derive(IntoPyObject)]
pub(crate) enum SingleOrList<T> {
    Single(T),
    List(Vec<T>),
}

/// Python bindings for the RustSAT library
#[pymodule]
fn rustsat(py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<types::Lit>()?;
    m.add_class::<types::Clause>()?;
    m.add_class::<instances::Cnf>()?;
    m.add_class::<instances::VarManager>()?;

    let encodings = PyModule::new(py, "rustsat.encodings")?;
    let card = PyModule::new(py, "rustsat.encodings.card")?;
    card.add_class::<encodings::card::Totalizer>()?;
    let pb = PyModule::new(py, "rustsat.encodings.pb")?;
    pb.add_class::<encodings::pb::GeneralizedTotalizer>()?;
    pb.add_class::<encodings::pb::DynamicPolyWatchdog>()?;
    pb.add_class::<encodings::pb::BinaryAdder>()?;
    let am1 = PyModule::new(py, "rustsat.encodings.am1")?;
    am1.add_class::<encodings::am1::Bimander>()?;
    am1.add_class::<encodings::am1::Bitwise>()?;
    am1.add_class::<encodings::am1::Commander>()?;
    am1.add_class::<encodings::am1::Ladder>()?;
    am1.add_class::<encodings::am1::Pairwise>()?;
    encodings.add("card", &card)?;
    encodings.add("pb", &pb)?;
    encodings.add("am1", &am1)?;
    m.add("encodings", &encodings)?;

    // To import encodings. Fix from https://github.com/PyO3/pyo3/issues/759
    py.import("sys")?
        .getattr("modules")?
        .set_item("rustsat.encodings", &encodings)?;
    py.import("sys")?
        .getattr("modules")?
        .set_item("rustsat.encodings.pb", &pb)?;
    py.import("sys")?
        .getattr("modules")?
        .set_item("rustsat.encodings.card", &card)?;
    py.import("sys")?
        .getattr("modules")?
        .set_item("rustsat.encodings.am1", &am1)?;

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
