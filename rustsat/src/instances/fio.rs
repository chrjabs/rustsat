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

use crate::{
    solvers::Solve,
    types::{self, Assignment},
};

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

#[derive(Debug, PartialEq, Eq)]
pub enum SolverOutput {
    Sat(types::Assignment),
    Unsat,
    Unknown,
}

#[derive(Error, Debug)]
pub enum SatSolverOutputError {
    #[error("The output of the SAT solver is incorrect.")]
    Nonsolution,
    #[error("No solution line found in the output.")]
    NoSline,
    #[error("No value line found in the output.")]
    NoVline,
    #[error("Invalid solution line found in the output.")]
    InvalidSLine,
}

#[derive(Error, Debug)]
pub enum InvalidVLine {
    #[error("The value line does not start with 'v ' ")]
    InvalidTag(char),
    #[error("The output of the SAT solver assigned the same variable different values.")]
    ConflictingAssignment(types::Var),
    #[error("Empty value line.")]
    Emptyline,
}

//Parse a SAT solver's output
pub fn parse_sat_solver_output<R: BufRead>(reader: R) -> anyhow::Result<SolverOutput> {
    let mut is_sat = false;
    let mut solution: Option<Assignment> = None;

    for line in reader.lines() {
        let line = &line?;

        //Solution line
        if line.starts_with("s ") {
            let line = &line[1..].trim_start();
            match line {
                line if line.starts_with("UNSATISFIABLE") => return Ok(SolverOutput::Unsat),
                line if line.starts_with("UNKNOWN") || line.starts_with("INDETERMINATE") => {
                    return Ok(SolverOutput::Unknown)
                }
                line if line.starts_with("SATISFIABLE") => {
                    is_sat = true;
                }
                _ => anyhow::bail!(SatSolverOutputError::InvalidSLine),
            }
        }

        //Value line
        if line.starts_with("v ") {
            //Have we already see a vline?
            match &mut solution {
                Some(assign) => assign.extend_from_vline(&line)?,
                _ => solution = Some(Assignment::from_vline(&line)?),
            }
        }
    }

    //There is no solution line so we can not trust the output
    if !is_sat {
        return anyhow::bail!(SatSolverOutputError::NoSline);
    }

    if let Some(solution) = solution {
        return Ok(SolverOutput::Sat(solution));
    }

    anyhow::bail!(SatSolverOutputError::NoVline);
}

#[cfg(test)]
mod tests {
    use std::io;

    use crate::{
        instances::fio::SatSolverOutputError,
        types::{Assignment, TernaryVal},
    };

    use super::{parse_sat_solver_output, SolverOutput};

    #[test]
    fn parse_solver_output_sat() {
        let ground_truth = SolverOutput::Sat(Assignment::from(vec![
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::DontCare,
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::True,
        ]));

        let data = "c this is a comment\ns SATISFIABLE\nv 1 -2 4 -5 6 0\n";
        let reader = io::Cursor::new(data);
        let res = parse_sat_solver_output(reader).unwrap();
        assert_eq!(res, ground_truth);

        let data = "c this is a comment\nv 1 -2 4 -5 6 0\ns SATISFIABLE\n";
        let reader = io::Cursor::new(data);
        let res = parse_sat_solver_output(reader).unwrap();
        assert_eq!(res, ground_truth);

        let data = "c this is a comment\ns SATISFIABLE\nv 1 -2 4 \nv -5 6 0\n";
        let reader = io::Cursor::new(data);
        let res = parse_sat_solver_output(reader).unwrap();
        assert_eq!(res, ground_truth);
    }

    #[test]
    fn parse_solver_output_unsat() {
        let data = "c this is a comment\ns UNSATISFIABLE\n";
        let reader = io::Cursor::new(data);
        let res = parse_sat_solver_output(reader).unwrap();
        assert_eq!(res, SolverOutput::Unsat);
    }

    #[test]
    fn parse_solver_output_unknown() {
        let data = "c this is a comment\ns UNKNOWN\n";
        let reader = io::Cursor::new(data);
        let res = parse_sat_solver_output(reader).unwrap();
        assert_eq!(res, SolverOutput::Unknown);
    }

    #[test]
    fn parse_solver_output_indeterminate() {
        let data = "c this is a comment\ns INDETERMINATE\n";
        let reader = io::Cursor::new(data);
        let res = parse_sat_solver_output(reader).unwrap();
        assert_eq!(res, SolverOutput::Unknown);
    }

    #[test]
    fn parse_solver_output_noslinewithvline() {
        let data = "c this is a comment\nv 1 -2 4 -5 6 0\n";
        let reader = io::Cursor::new(data);
        let res = parse_sat_solver_output(reader);
        match res.unwrap_err().downcast::<SatSolverOutputError>() {
            Ok(err) => match err {
                SatSolverOutputError::NoSline => assert!(true),
                _ => panic!(),
            },
            Err(_) => panic!(),
        }
    }

    #[test]
    fn parse_solver_output_novlinewithsatisfy() {
        let data = "c this is a comment\ns SATISFIABLE\n";
        let reader = io::Cursor::new(data);
        let res = parse_sat_solver_output(reader);
        match res.unwrap_err().downcast::<SatSolverOutputError>() {
            Ok(err) => match err {
                SatSolverOutputError::NoVline => assert!(true),
                _ => panic!(),
            },
            Err(_) => panic!(),
        }
    }

    #[test]
    fn parse_solver_output_emptysolution() {
        let data = "c this is a comment\ns SATISFIABLE\nv 0\n";
        let reader = io::Cursor::new(data);
        let res = parse_sat_solver_output(reader).unwrap();
        assert_eq!(res, SolverOutput::Sat(Assignment::default()));
    }
}
