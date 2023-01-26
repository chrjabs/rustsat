//! # Module for File IO (Writing and Parsing)
//!
//! As the submodules have different APIs, it is recommended to parse and write
//! through the interface of instance types rather than using these functions
//! directly.

use std::{fmt, fs::File, io, path::Path};

pub mod dimacs;

pub mod opb;

/// Combined Parsing Errors
#[derive(Debug)]
pub enum ParsingError {
    /// IO Errors
    IO(std::io::Error),
    /// Dimacs Parsing Error
    Dimacs(dimacs::Error),
    /// OPB Parsing Error
    Opb(opb::Error),
}

impl From<dimacs::Error> for ParsingError {
    fn from(de: dimacs::Error) -> Self {
        ParsingError::Dimacs(de)
    }
}

impl From<opb::Error> for ParsingError {
    fn from(oe: opb::Error) -> Self {
        ParsingError::Opb(oe)
    }
}

impl fmt::Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParsingError::IO(ioe) => write!(f, "IO error: {}", ioe),
            ParsingError::Dimacs(de) => write!(f, "Dimacs error: {}", de),
            ParsingError::Opb(oe) => write!(f, "OPB error: {}", oe),
        }
    }
}

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
    }
    Ok(Box::new(raw_reader))
}

/// Opens a writer for the file at Path.
/// With feature `compression` supports bzip2 and gzip compression.
pub(crate) fn open_compressed_uncompressed_write<P: AsRef<Path>>(
    path: P,
) -> Result<Box<dyn io::Write>, io::Error> {
    let path = path.as_ref();
    let raw_reader = File::create(path)?;
    #[cfg(feature = "compression")]
    if let Some(ext) = path.extension() {
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("bz2")) {
            return Ok(Box::new(bzip2::write::BzEncoder::new(
                raw_reader,
                bzip2::Compression::fast(),
            )));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("gz")) {
            return Ok(Box::new(flate2::write::GzEncoder::new(
                raw_reader,
                flate2::Compression::fast(),
            )));
        }
    }
    Ok(Box::new(raw_reader))
}
