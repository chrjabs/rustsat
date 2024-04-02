//! # Module for File IO (Writing and Parsing)
//!
//! As the submodules have different APIs, it is recommended to parse and write
//! through the interface of instance types rather than using these functions
//! directly.

use std::{fs::File, io, path::Path};
use thiserror::Error;

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
