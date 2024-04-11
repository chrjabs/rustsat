//! # Module for File IO (Writing and Parsing)
//!
//! As the submodules have different APIs, it is recommended to parse and write
//! through the interface of instance types rather than using these functions
//! directly.

use std::{
    fs::File,
    io::{self, BufRead},
    path::Path,
};
use thiserror::Error;

use crate::types;

pub mod dimacs;
pub mod opb;

/// An error for when a requested objective does not exist
#[derive(Error, Debug, PartialEq, Eq, Clone, Copy)]
#[error("the file only has {0} objectives")]
pub struct ObjNoExist(usize);

/// Opens a reader for the file at Path.
/// With feature `compression` supports bzip2 and gzip compression.
pub(crate) fn open_compressed_uncompressed_read<P: AsRef<Path>>(
    path: P,
) -> Result<Box<dyn io::Read>, io::Error> {
    let path = path.as_ref();
    let raw_reader = File::open(path)?;
    #[cfg(feature = "compression")]
    if let Some(ext) = path.extension() {
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("bz2")) {
            return Ok(Box::new(bzip2::read::BzDecoder::new(raw_reader)));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("gz")) {
            return Ok(Box::new(flate2::read::GzDecoder::new(raw_reader)));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("xz")) {
            return Ok(Box::new(xz2::read::XzDecoder::new(raw_reader)));
        }
    }
    Ok(Box::new(raw_reader))
}

/// Opens a writer for the file at Path.
/// With feature `compression` supports bzip2 and gzip compression.
pub(crate) fn open_compressed_uncompressed_write<P: AsRef<Path>>(
    path: P,
) -> Result<Box<dyn io::Write>, io::Error> {
    let path = path.as_ref();
    let raw_writer = File::create(path)?;
    #[cfg(feature = "compression")]
    if let Some(ext) = path.extension() {
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("bz2")) {
            return Ok(Box::new(io::BufWriter::new(bzip2::write::BzEncoder::new(
                raw_writer,
                bzip2::Compression::fast(),
            ))));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("gz")) {
            return Ok(Box::new(io::BufWriter::new(flate2::write::GzEncoder::new(
                raw_writer,
                flate2::Compression::fast(),
            ))));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("xz")) {
            return Ok(Box::new(io::BufWriter::new(xz2::write::XzEncoder::new(
                raw_writer, 1,
            ))));
        }
    }
    Ok(Box::new(io::BufWriter::new(raw_writer)))
}

pub enum SolverOutput {
    Sat(types::Assignment),
    Unsat,
    Unknown,
}

#[derive(Debug)]
pub enum SatSolverOutputError {
    //The output of the SAT solver is incorrect.
    Nonsolution,
}

impl std::fmt::Display for SatSolverOutputError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nonsolution => write!(f, "The output of the SAT solver is incorrect."),
        }
    }
}

pub fn parse_sat_solver_output<R: BufRead>(reader: R) -> anyhow::Result<SolverOutput> {
    // Parsing code goes here
    // when encoutering vline, call `Assignment::from_vline`

    let sat_solver_output = SolverOutput::Sat(Default::default());

    for line in reader.lines() {
        let line_ls = line.as_ref().expect("Couldn't read SAT solution line");

        //Solution line
        if line_ls.starts_with('s') {
            match line_ls {
                line_ls if line_ls.contains("UNSATISFIABLE") => return Ok(SolverOutput::Unsat),
                line_ls if line_ls.contains("UNKNOWN") => return Ok(SolverOutput::Unknown),
                line_ls if line_ls.contains("SATISFIABLE") => (),
                _ => return Err(anyhow::anyhow!(SatSolverOutputError::Nonsolution)),
            }
        }

        //Value line
        if line_ls.starts_with('v') {
            // There is a solution and the literals have values
            //I assume that the output literal is 2*variable_index + signe
            let current_assignment = match sat_solver_output {
                SolverOutput::Sat(assign) => &assign,
                _ => return Err(anyhow::anyhow!(SatSolverOutputError::Nonsolution)),
            };

            current_assignment.from_vline(&line_ls);
        }
    }

    Ok(sat_solver_output)
}
