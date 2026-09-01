//! # Module for File IO (Writing and Parsing)
//!
//! As the sub-modules have different APIs, it is recommended to parse and write
//! through the interface of instance types rather than using these functions
//! directly.

use std::io::BufRead;

pub mod dimacs;
pub mod opb;

/// An error for when a requested objective does not exist
#[cfg(feature = "optimization")]
#[derive(thiserror::Error, Debug, PartialEq, Eq, Clone, Copy)]
#[error("the file only has {0} objectives")]
pub struct ObjNoExist(usize);

/// Errors occurring within the File IO module
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Error in parsing
    #[error("Parsing error: {0}")]
    Parsing(#[from] ParsingError),
    /// Input-output error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    /// Encountered an OPB objective line while parsing a decision instance
    #[cfg(feature = "optimization")]
    #[error("encountered an OPB objective line while parsing a decision instance")]
    ObjInSat,
    /// A single-objective OPB instance was found to not have an objective
    #[cfg(feature = "optimization")]
    #[error("single-objective OPB file does not have an objective")]
    NoObjective,
    /// A single-objective OPB instance was found to have more than one objective
    #[cfg(feature = "optimization")]
    #[error("single-objective OPB file has more than one objective")]
    MultipleObjectives,
    /// Converting an OPB maximization objective to a minimization objective resulted in an overflow
    #[cfg(feature = "optimization")]
    #[error("overflow in converting maximization objective to minimization objective")]
    ObjectiveConversionOverflow,
}

/// An error occurring during parsing
#[derive(Clone, Debug, thiserror::Error)]
pub struct ParsingError {
    message: String,
    span: std::ops::Range<usize>,
    input: String,
    line_start: usize,
}

impl ParsingError {
    /// Creates a new parsing error from a [`winnow::error::ParseError`] and context
    #[cfg_attr(feature = "_internals", visibility::make(pub))]
    #[must_use]
    pub(crate) fn from_parse(
        error: &winnow::error::ParseError<&str, winnow::error::ContextError>,
        input: &str,
        offset: usize,
        line_start: usize,
    ) -> Self {
        let message = error.inner().to_string();
        let input = input.to_owned();
        let start = error.offset() + offset;
        let end = (start + 1..=input.len())
            .find(|e| input.is_char_boundary(*e))
            .unwrap_or(start);
        Self {
            message,
            span: start..end,
            input,
            line_start,
        }
    }

    #[must_use]
    pub(crate) fn new(message: String, input: &str, offset: usize, line_start: usize) -> Self {
        let input = input.to_owned();
        let end = (offset + 1..=input.len())
            .find(|e| input.is_char_boundary(*e))
            .unwrap_or(offset);
        Self {
            message,
            span: offset..end,
            input,
            line_start,
        }
    }

    /// Provide a wider context and the offset of the old context in the new context
    pub fn extend_context(&mut self, new_context: String, offset_of_old: usize) {
        self.input = new_context;
        self.span = self.span.start + offset_of_old..self.span.end + offset_of_old;
    }

    /// Renders the error with a given [`annotate_snippets::Renderer`]
    #[must_use]
    pub fn render(&self, renderer: &annotate_snippets::Renderer) -> String {
        let report = &[annotate_snippets::Level::ERROR
            .primary_title(&self.message)
            .element(
                annotate_snippets::Snippet::source(&self.input)
                    .line_start(self.line_start)
                    .annotation(
                        annotate_snippets::AnnotationKind::Primary
                            .span(self.span.clone())
                            .label("here"),
                    ),
            )];
        renderer.render(report)
    }
}

impl std::fmt::Display for ParsingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.render(
            &annotate_snippets::Renderer::plain()
                .decor_style(annotate_snippets::renderer::DecorStyle::Unicode),
        )
        .fmt(f)
    }
}

/// Opens a reader for the file at Path.
/// With feature `compression` supports bzip2 and gzip compression.
///
/// # Errors
///
/// If opening the file fails, returns [`std::io::Error`]
pub fn open_compressed_uncompressed_read<P: AsRef<std::path::Path>>(
    path: P,
) -> Result<Box<dyn std::io::BufRead>, std::io::Error> {
    let path = path.as_ref();
    let raw_reader = std::fs::File::open(path)?;
    #[cfg(feature = "compression")]
    if let Some(ext) = path.extension() {
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("bz2")) {
            return Ok(Box::new(std::io::BufReader::new(
                bzip2::read::BzDecoder::new(raw_reader),
            )));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("gz")) {
            return Ok(Box::new(std::io::BufReader::new(
                flate2::read::GzDecoder::new(raw_reader),
            )));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("xz")) {
            return Ok(Box::new(std::io::BufReader::new(
                xz2::read::XzDecoder::new(raw_reader),
            )));
        }
    }
    Ok(Box::new(std::io::BufReader::new(raw_reader)))
}

/// Opens a writer for the file at Path.
/// With feature `compression` supports bzip2 and gzip compression.
///
/// # Errors
///
/// If opening the file fails, returns [`std::io::Error`]
pub fn open_compressed_uncompressed_write<P: AsRef<std::path::Path>>(
    path: P,
) -> Result<Box<dyn std::io::Write>, std::io::Error> {
    let path = path.as_ref();
    let raw_writer = std::fs::File::create(path)?;
    #[cfg(feature = "compression")]
    if let Some(ext) = path.extension() {
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("bz2")) {
            return Ok(Box::new(std::io::BufWriter::new(
                bzip2::write::BzEncoder::new(raw_writer, bzip2::Compression::fast()),
            )));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("gz")) {
            return Ok(Box::new(std::io::BufWriter::new(
                flate2::write::GzEncoder::new(raw_writer, flate2::Compression::fast()),
            )));
        }
        if ext.eq_ignore_ascii_case(std::ffi::OsStr::new("xz")) {
            return Ok(Box::new(std::io::BufWriter::new(
                xz2::write::XzEncoder::new(raw_writer, 1),
            )));
        }
    }
    Ok(Box::new(std::io::BufWriter::new(raw_writer)))
}

/// Possible results from SAT solver output parsing
#[derive(Debug, PartialEq, Eq)]
pub enum SolverOutput {
    /// The solver indicates satisfiability with the given assignment
    Sat(crate::types::Assignment),
    /// The solver indicates unsatisfiability
    Unsat,
    /// The solver did not solve the instance
    Unknown,
}

impl SolverOutput {
    pub(crate) fn result(&self) -> crate::solvers::SolverResult {
        match self {
            SolverOutput::Sat(_) => crate::solvers::SolverResult::Sat,
            SolverOutput::Unsat => crate::solvers::SolverResult::Unsat,
            SolverOutput::Unknown => crate::solvers::SolverResult::Interrupted,
        }
    }

    pub(crate) fn state(&self) -> crate::solvers::SolverState {
        match self {
            SolverOutput::Sat(_) => crate::solvers::SolverState::Sat,
            SolverOutput::Unsat => crate::solvers::SolverState::Unsat,
            SolverOutput::Unknown => crate::solvers::SolverState::Unknown,
        }
    }
}

/// Possible errors in SAT solver output parsing
#[derive(thiserror::Error, Debug)]
pub enum SatSolverOutputError {
    /// Input-output error
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    /// Invalid v-line
    #[error("Invalid v-line: {0}")]
    InvalidVLine(#[from] crate::types::InvalidVLine),
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
/// If reading the output of parsing it fails
pub fn parse_sat_solver_output<R: BufRead>(
    reader: R,
) -> Result<SolverOutput, SatSolverOutputError> {
    let mut is_sat = false;
    let mut solution: Option<crate::types::Assignment> = None;

    for line in reader.lines() {
        let line = &line?;

        // Solution line
        if line.starts_with("s ") {
            let line = &line[1..].trim_start();
            match line {
                line if line.starts_with("UNSATISFIABLE") => return Ok(SolverOutput::Unsat),
                line if line.starts_with("UNKNOWN") || line.starts_with("INDETERMINATE") => {
                    return Ok(SolverOutput::Unknown);
                }
                line if line.starts_with("SATISFIABLE") => {
                    is_sat = true;
                }
                _ => return Err(SatSolverOutputError::InvalidSLine),
            }
        }

        // Value line
        if line.starts_with("v ") {
            match &mut solution {
                Some(assign) => assign.extend_from_vline(line)?,
                _ => solution = Some(crate::types::Assignment::from_vline(line)?),
            }
        }
    }

    // There is no solution line so we can not trust the output
    if !is_sat {
        return Err(SatSolverOutputError::NoSLine);
    }

    if let Some(solution) = solution {
        return Ok(SolverOutput::Sat(solution));
    }

    Err(SatSolverOutputError::NoVLine)
}

#[cfg(test)]
mod tests {
    use crate::types::TernaryVal;

    use super::SatSolverOutputError;
    use super::SolverOutput;
    use super::parse_sat_solver_output;

    #[test]
    fn parse_solver_output_sat() {
        let ground_truth = SolverOutput::Sat(crate::types::Assignment::from(vec![
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::DontCare,
            TernaryVal::True,
            TernaryVal::False,
            TernaryVal::True,
        ]));

        let data = "c this is a comment\ns SATISFIABLE\nv 1 -2 4 -5 6 0\n";
        let res = parse_sat_solver_output(&mut std::io::Cursor::new(data)).unwrap();
        assert_eq!(res, ground_truth);

        let data = "c this is a comment\nv 1 -2 4 -5 6 0\ns SATISFIABLE\n";
        let res = parse_sat_solver_output(&mut std::io::Cursor::new(data)).unwrap();
        assert_eq!(res, ground_truth);

        let data = "c this is a comment\ns SATISFIABLE\nv 1 -2 4 \nv -5 6 0\n";
        let res = parse_sat_solver_output(&mut std::io::Cursor::new(data)).unwrap();
        assert_eq!(res, ground_truth);
    }

    #[test]
    fn parse_solver_output_unsat() {
        let data = "c this is a comment\ns UNSATISFIABLE\n";
        let res = parse_sat_solver_output(&mut std::io::Cursor::new(data)).unwrap();
        assert_eq!(res, SolverOutput::Unsat);
    }

    #[test]
    fn parse_solver_output_unknown() {
        let data = "c this is a comment\ns UNKNOWN\n";
        let res = parse_sat_solver_output(&mut std::io::Cursor::new(data)).unwrap();
        assert_eq!(res, SolverOutput::Unknown);
    }

    #[test]
    fn parse_solver_output_indeterminate() {
        let data = "c this is a comment\ns INDETERMINATE\n";
        let res = parse_sat_solver_output(&mut std::io::Cursor::new(data)).unwrap();
        assert_eq!(res, SolverOutput::Unknown);
    }

    #[test]
    fn parse_solver_output_noslinewithvline() {
        let data = "c this is a comment\nv 1 -2 4 -5 6 0\n";
        let res = parse_sat_solver_output(&mut std::io::Cursor::new(data));
        assert!(matches!(res.unwrap_err(), SatSolverOutputError::NoSLine));
    }

    #[test]
    fn parse_solver_output_novlinewithsatisfy() {
        let data = "c this is a comment\ns SATISFIABLE\n";
        let res = parse_sat_solver_output(&mut std::io::Cursor::new(data));
        assert!(matches!(res.unwrap_err(), SatSolverOutputError::NoVLine));
    }

    #[test]
    fn parse_solver_output_emptysolution() {
        let data = "c this is a comment\ns SATISFIABLE\nv 0\n";
        let res = parse_sat_solver_output(&mut std::io::Cursor::new(data)).unwrap();
        assert_eq!(res, SolverOutput::Sat(crate::types::Assignment::default()));
    }

    #[test]
    fn parse_solver_output_sat_logs() {
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        let instance: crate::instances::SatInstance =
            crate::instances::SatInstance::from_dimacs_path(format!(
                "{manifest}/data/AProVE11-12.cnf"
            ))
            .unwrap();

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

    #[test]
    fn parsing_error_format() {
        insta::assert_snapshot!(format!(
            "{}",
            super::ParsingError {
                message: String::from("parsing failed here"),
                span: 23..30,
                input: String::from("some string in which a failure occurred"),
                line_start: 42,
            }
        ));
    }
}
