//! # Module for File IO (Writing and Parsing)
//!
//! As the sub-modules have different APIs, it is recommended to parse and write
//! through the interface of instance types rather than using these functions
//! directly.

use std::{
    fs::File,
    io::{self, BufRead},
    path::Path,
};
use thiserror::Error;

use crate::{
    solvers::{SolverResult, SolverState},
    types::{self, Assignment},
};

pub mod dimacs;
pub mod opb;

/// An error for when a requested objective does not exist
#[cfg(feature = "optimization")]
#[derive(Error, Debug, PartialEq, Eq, Clone, Copy)]
#[error("the file only has {0} objectives")]
pub struct ObjNoExist(usize);

/// Opens a reader for the file at Path.
/// With feature `compression` supports bzip2 and gzip compression.
///
/// # Errors
///
/// If opening the file fails, returns [`io::Error`]
pub fn open_compressed_uncompressed_read<P: AsRef<Path>>(
    path: P,
) -> Result<Box<dyn io::BufRead>, io::Error> {
    let path = path.as_ref();
    let raw_reader = File::open(path)?;
    #[cfg(feature = "compression")]
    if let Some(ext) = path.extension() {
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("bz2")) {
            return Ok(Box::new(io::BufReader::new(bzip2::read::BzDecoder::new(
                raw_reader,
            ))));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("gz")) {
            return Ok(Box::new(io::BufReader::new(flate2::read::GzDecoder::new(
                raw_reader,
            ))));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("xz")) {
            return Ok(Box::new(io::BufReader::new(xz2::read::XzDecoder::new(
                raw_reader,
            ))));
        }
    }
    Ok(Box::new(io::BufReader::new(raw_reader)))
}

/// Opens a writer for the file at Path.
/// With feature `compression` supports bzip2 and gzip compression.
///
/// # Errors
///
/// If opening the file fails, returns [`io::Error`]
pub fn open_compressed_uncompressed_write<P: AsRef<Path>>(
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

/// Possible results from SAT solver output parsing
#[derive(Debug, PartialEq, Eq)]
pub enum SolverOutput {
    /// The solver indicates satisfiability with the given assignment
    Sat(types::Assignment),
    /// The solver indicates unsatisfiability
    Unsat,
    /// The solver did not solve the instance
    Unknown,
}

impl SolverOutput {
    pub(crate) fn result(&self) -> SolverResult {
        match self {
            SolverOutput::Sat(_) => SolverResult::Sat,
            SolverOutput::Unsat => SolverResult::Unsat,
            SolverOutput::Unknown => SolverResult::Interrupted,
        }
    }

    pub(crate) fn state(&self) -> SolverState {
        match self {
            SolverOutput::Sat(_) => SolverState::Sat,
            SolverOutput::Unsat => SolverState::Unsat,
            SolverOutput::Unknown => SolverState::Unknown,
        }
    }
}

/// Possible errors in SAT solver output parsing
#[derive(Error, Debug)]
#[allow(clippy::enum_variant_names)]
pub enum SatSolverOutputError {
    /// The solver output does not contain an `s` line
    #[error("No solution line found in the output.")]
    NoSLine,
    /// The solver output does indicate satisfiability but does not contain an assignment
    #[error("No value line found in the output.")]
    NoVLine,
    /// The solver output contains an invalid `s` line
    #[error("Invalid solution line found in the output.")]
    InvalidSLine,
}

/// Parses SAT solver output
///
/// # Errors
///
/// Either [`SatSolverOutputError`], [`types::InvalidVLine`], or other parsing errors on invalid
/// input.
pub fn parse_sat_solver_output<R: BufRead>(reader: &mut R) -> anyhow::Result<SolverOutput> {
    let mut is_sat = false;
    let mut solution: Option<Assignment> = None;

    for line in reader.lines() {
        let line = &line?;

        // Solution line
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

        // Value line
        if line.starts_with("v ") {
            match &mut solution {
                Some(assign) => assign.extend_from_vline(line)?,
                _ => solution = Some(Assignment::from_vline(line)?),
            }
        }
    }

    // There is no solution line so we can not trust the output
    anyhow::ensure!(is_sat, SatSolverOutputError::NoSLine);

    if let Some(solution) = solution {
        return Ok(SolverOutput::Sat(solution));
    }

    anyhow::bail!(SatSolverOutputError::NoVLine);
}

#[cfg(test)]
mod tests {
    use std::io;

    use crate::{
        instances::SatInstance,
        types::{Assignment, TernaryVal},
    };

    use super::{parse_sat_solver_output, SatSolverOutputError, SolverOutput};

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
        let res = parse_sat_solver_output(&mut io::Cursor::new(data)).unwrap();
        assert_eq!(res, ground_truth);

        let data = "c this is a comment\nv 1 -2 4 -5 6 0\ns SATISFIABLE\n";
        let res = parse_sat_solver_output(&mut io::Cursor::new(data)).unwrap();
        assert_eq!(res, ground_truth);

        let data = "c this is a comment\ns SATISFIABLE\nv 1 -2 4 \nv -5 6 0\n";
        let res = parse_sat_solver_output(&mut io::Cursor::new(data)).unwrap();
        assert_eq!(res, ground_truth);
    }

    #[test]
    fn parse_solver_output_unsat() {
        let data = "c this is a comment\ns UNSATISFIABLE\n";
        let res = parse_sat_solver_output(&mut io::Cursor::new(data)).unwrap();
        assert_eq!(res, SolverOutput::Unsat);
    }

    #[test]
    fn parse_solver_output_unknown() {
        let data = "c this is a comment\ns UNKNOWN\n";
        let res = parse_sat_solver_output(&mut io::Cursor::new(data)).unwrap();
        assert_eq!(res, SolverOutput::Unknown);
    }

    #[test]
    fn parse_solver_output_indeterminate() {
        let data = "c this is a comment\ns INDETERMINATE\n";
        let res = parse_sat_solver_output(&mut io::Cursor::new(data)).unwrap();
        assert_eq!(res, SolverOutput::Unknown);
    }

    #[test]
    fn parse_solver_output_noslinewithvline() {
        let data = "c this is a comment\nv 1 -2 4 -5 6 0\n";
        let res = parse_sat_solver_output(&mut io::Cursor::new(data));
        assert!(matches!(
            res.unwrap_err().downcast::<SatSolverOutputError>(),
            Ok(SatSolverOutputError::NoSLine)
        ));
    }

    #[test]
    fn parse_solver_output_novlinewithsatisfy() {
        let data = "c this is a comment\ns SATISFIABLE\n";
        let res = parse_sat_solver_output(&mut io::Cursor::new(data));
        assert!(matches!(
            res.unwrap_err().downcast::<SatSolverOutputError>(),
            Ok(SatSolverOutputError::NoVLine)
        ));
    }

    #[test]
    fn parse_solver_output_emptysolution() {
        let data = "c this is a comment\ns SATISFIABLE\nv 0\n";
        let res = parse_sat_solver_output(&mut io::Cursor::new(data)).unwrap();
        assert_eq!(res, SolverOutput::Sat(Assignment::default()));
    }

    #[test]
    fn parse_solver_output_sat_logs() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let instance: SatInstance =
            SatInstance::from_dimacs_path(format!("{manifest}/data/AProVE11-12.cnf")).unwrap();

        let mut reader = super::open_compressed_uncompressed_read(format!(
            "{manifest}/data/gimsatul-AProVE11-12.log"
        ))
        .unwrap();
        let res = parse_sat_solver_output(&mut reader).unwrap();
        if let SolverOutput::Sat(sol) = res {
            assert_eq!(instance.evaluate(&sol), TernaryVal::True);
        } else {
            panic!()
        }

        let mut reader = super::open_compressed_uncompressed_read(format!(
            "{manifest}/data/kissat-AProVE11-12.log"
        ))
        .unwrap();
        let res = parse_sat_solver_output(&mut reader).unwrap();
        if let SolverOutput::Sat(sol) = res {
            assert_eq!(instance.evaluate(&sol), TernaryVal::True);
        } else {
            panic!()
        }

        let mut reader = super::open_compressed_uncompressed_read(format!(
            "{manifest}/data/cadical-AProVE11-12.log"
        ))
        .unwrap();
        let res = parse_sat_solver_output(&mut reader).unwrap();
        if let SolverOutput::Sat(sol) = res {
            assert_eq!(instance.evaluate(&sol), TernaryVal::True);
        } else {
            panic!()
        }
    }

    #[test]
    fn parse_solver_output_unsat_logs() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let mut reader = super::open_compressed_uncompressed_read(format!(
            "{manifest}/data/gimsatul-smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.log"
        ))
        .unwrap();
        assert_eq!(
            parse_sat_solver_output(&mut reader).unwrap(),
            SolverOutput::Unsat
        );
        let mut reader = super::open_compressed_uncompressed_read(format!(
            "{manifest}/data/kissat-smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.log"
        ))
        .unwrap();
        assert_eq!(
            parse_sat_solver_output(&mut reader).unwrap(),
            SolverOutput::Unsat
        );
        let mut reader = super::open_compressed_uncompressed_read(format!(
            "{manifest}/data/cadical-smtlib-qfbv-aigs-ext_con_032_008_0256-tseitin.log"
        ))
        .unwrap();
        assert_eq!(
            parse_sat_solver_output(&mut reader).unwrap(),
            SolverOutput::Unsat
        );
    }
}
