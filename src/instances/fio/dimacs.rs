//! # Parsing and Writing DIMACS Files
//!
//! Internal module containing functions for parsing DIMACS files.
//! The approach is to accept input instances, even if they are not technically
//! in spec, as long as the input is still reasonable.
//!
//! ## References
//!
//! - [DIMACS CNF](http://www.satcompetition.org/2011/format-benchmarks2011.html)
//! - [DIMACS WCNF pre-22](https://maxsat-evaluations.github.io/2017/rules.html#input)
//! - [DIMACS WCNF post-22](https://maxsat-evaluations.github.io/2022/rules.html#input)

use std::io::{self, Write};

use winnow::{
    ascii::{dec_int, dec_uint, line_ending, space0, space1, till_line_ending},
    combinator::{alt, cut_err, eof, opt, separated, seq, terminated},
    error::StrContext,
    ModalResult, Parser as _,
};

use crate::{
    instances::Cnf,
    types::{Cl, Clause, Lit},
    utils,
};

use super::ParsingError;

#[cfg(feature = "optimization")]
use crate::types::WClsIter;

/// The main OPB parser iterator
///
/// Different parser variants are identified via the `Variant` generic type
#[derive(Debug)]
pub struct Parser<Variant, R> {
    /// The parser variant
    variant: Variant,
    /// Where input data is coming from
    reader: R,
    /// Buffer of read data
    buffer: String,
    /// The current line number
    line_num: usize,
}

impl<Variant, R> Parser<Variant, R> {
    /// Creates a new parser iterator from a reader and parsing settings
    pub fn new(reader: R) -> Self
    where
        Variant: Default,
        R: io::BufRead,
    {
        Self {
            variant: Variant::default(),
            reader,
            buffer: String::new(),
            line_num: 0,
        }
    }

    /// Destroys the parser and gets back the reader
    pub fn reader(self) -> R {
        self.reader
    }

    /// Loads the next non-empty line into the buffer
    fn read_line(&mut self) -> io::Result<bool>
    where
        R: io::BufRead,
    {
        debug_assert!(self.buffer.is_empty());
        loop {
            let read = self.reader.read_line(&mut self.buffer)?;
            if read == 0 {
                return Ok(true);
            }
            self.line_num += 1;
            if !self.buffer.trim().is_empty() {
                return Ok(false);
            }
            // tollerate empty lines
            self.buffer.clear();
        }
    }
}

/// Data returned at the transition from a CNF header to the body
#[derive(Debug)]
pub struct CnfHeaderData<R> {
    /// The number of variables in the file, as specified by the file header
    pub n_vars: u32,
    /// The number of clauses in the file, as specified by the file header
    pub n_clauses: usize,
    /// The CNF body parser to parse the rest of the file
    pub body_parser: Parser<CnfBody, R>,
}

/// Identifier type for the CNF header parser variant
///
/// This parser allows for iterating of all comment lines before the CNF header and then
/// transitions to a [`Parser<CnfBody, R>`].
#[derive(Debug, Default)]
pub struct CnfHeader {
    /// The data in the CNF header, if it has been encountered already
    header_data: Option<(u32, usize)>,
}

impl<R> Parser<CnfHeader, R>
where
    R: io::BufRead,
{
    /// Transitions the parser to the CNF body
    ///
    /// If not all comment lines before the header have been iterated over, they will be silently
    /// consumed
    ///
    /// # Errors
    ///
    /// If file access fails, the file ends before a CNF header is found, or an invalid header is
    /// encountered.
    #[expect(clippy::missing_panics_doc)]
    pub fn forward_to_body(mut self) -> Result<CnfHeaderData<R>, super::Error> {
        debug_assert!(self.buffer.is_empty());
        if let Some((n_vars, n_clauses)) = self.variant.header_data {
            return Ok(CnfHeaderData {
                n_vars,
                n_clauses,
                body_parser: Parser {
                    variant: CnfBody::default(),
                    reader: self.reader,
                    buffer: self.buffer,
                    line_num: self.line_num,
                },
            });
        }
        let mut trimmed_line;
        loop {
            if self.read_line()? {
                return Err(ParsingError::new(
                    String::from("missing CNF header"),
                    &self.buffer,
                    self.buffer.len(),
                    self.line_num + 1,
                )
                .into());
            }
            trimmed_line = self.buffer.trim();
            if !trimmed_line.starts_with('c') {
                break;
            }
            self.buffer.clear();
        }
        let (n_vars, n_clauses) = match cnf_p_line.parse(trimmed_line) {
            Err(err) => {
                return Err(ParsingError::from_parse(
                    &err,
                    &self.buffer,
                    // NOTE: `trimmed_line` is always part of `self.buffer`, so this will never
                    // panic
                    utils::substr_offset(&self.buffer, trimmed_line).unwrap(),
                    self.line_num,
                )
                .into());
            }
            Ok(data) => data,
        };
        self.buffer.clear();
        Ok(CnfHeaderData {
            n_vars,
            n_clauses,
            body_parser: Parser {
                variant: CnfBody::default(),
                reader: self.reader,
                buffer: self.buffer,
                line_num: self.line_num,
            },
        })
    }
}

#[derive(Debug)]
enum CnfHeaderLine {
    Comment(String),
    Header(u32, usize),
}

impl<R> Iterator for Parser<CnfHeader, R>
where
    R: io::BufRead,
{
    type Item = Result<String, super::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.variant.header_data.is_some() {
            return None;
        }
        match self.read_line() {
            Err(err) => return Some(Err(err.into())),
            Ok(true) => return None,
            Ok(_) => (),
        }

        let trimmed_line = self.buffer.trim();
        let data = match alt((
            comment.map(|c| CnfHeaderLine::Comment(c.to_owned())),
            cnf_p_line.map(|(n_vars, n_clauses)| CnfHeaderLine::Header(n_vars, n_clauses)),
        ))
        .context(StrContext::Label("cnf header line"))
        .parse(trimmed_line)
        {
            Err(err) => {
                return Some(Err(ParsingError::from_parse(
                    &err,
                    &self.buffer,
                    utils::substr_offset(&self.buffer, trimmed_line).unwrap(),
                    self.line_num,
                )
                .into()))
            }
            Ok(data) => data,
        };
        self.buffer.clear();
        match data {
            CnfHeaderLine::Comment(comment) => Some(Ok(comment)),
            CnfHeaderLine::Header(n_vars, n_clauses) => {
                self.variant.header_data = Some((n_vars, n_clauses));
                None
            }
        }
    }
}

/// Data that can appear in a CNF file body
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, PartialEq, Eq)]
pub enum CnfData {
    /// An input clause
    Clause(Clause),
    /// A comment line in the CNF body
    Comment(String),
}

/// Identifier type for the CNF body parser variant
#[derive(Debug, Default)]
pub struct CnfBody();

impl<R> Iterator for Parser<CnfBody, R>
where
    R: io::BufRead,
{
    type Item = Result<CnfData, super::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.read_line() {
            Err(err) => return Some(Err(err.into())),
            Ok(true) => return None,
            Ok(_) => (),
        }

        let trimmed_line = self.buffer.trim();
        let data = match alt((
            comment.map(|c| CnfData::Comment(c.to_owned())),
            clause.map(CnfData::Clause),
        ))
        .context(StrContext::Label("cnf body line"))
        .parse(trimmed_line)
        {
            Err(err) => {
                return Some(Err(ParsingError::from_parse(
                    &err,
                    &self.buffer,
                    utils::substr_offset(&self.buffer, trimmed_line).unwrap(),
                    self.line_num,
                )
                .into()))
            }
            Ok(data) => data,
        };
        self.buffer.clear();

        Some(Ok(data))
    }
}

/// Data returned at the transition from a WCNF header to the body
#[cfg(feature = "optimization")]
#[derive(Debug)]
pub enum WcnfHeaderData<R> {
    /// The file was determined to be in pre-2022 format
    Pre22 {
        /// The number of variables in the file, as specified by the file header
        n_vars: u32,
        /// The number of clauses in the file, as specified by the file header
        n_clauses: usize,
        /// The top value of the WCNF file
        top: usize,
        /// The WCNF body parser to parse the rest of the file
        body_parser: Parser<WcnfPre22Body, R>,
    },
    /// The file was determined to be in post-2022 format
    Post22(Parser<WcnfPost22, R>),
    /// Neither a pre-2022 header, nor a post-2022 clause was encountered before the file ended
    Empty(R),
}

#[cfg(feature = "optimization")]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug)]
enum WcnfInternalHeaderData {
    Pre22 {
        n_vars: u32,
        n_clauses: usize,
        top: usize,
    },
    Post22(WcnfData),
    Empty,
}

/// Identifier type for the WCNF header parser variant
///
/// This parser allows for iterating of all comment lines before the CNF header and then
/// transitions to either [`Parser<WcnfPre22Body, R>`] or [`Parser<WcnfPost22Body, R>`], where the
/// file type variant is detected from the header.
#[cfg(feature = "optimization")]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Default)]
pub struct WcnfHeader {
    /// The data in the CNF header, if it has been encountered already
    header_data: Option<WcnfInternalHeaderData>,
}

#[cfg(feature = "optimization")]
impl<R> Parser<WcnfHeader, R>
where
    R: io::BufRead,
{
    /// Transitions the parser to the CNF body
    ///
    /// If not all comment lines before the header have been iterated over, they will be silently
    /// consumed
    ///
    /// # Errors
    ///
    /// If file access fails, the file ends before a CNF header is found, or an invalid header is
    /// encountered.
    #[expect(clippy::missing_panics_doc)]
    pub fn forward_to_body(mut self) -> Result<WcnfHeaderData<R>, super::Error> {
        debug_assert!(self.buffer.is_empty());
        if let Some(header_data) = self.variant.header_data {
            return Ok(match header_data {
                WcnfInternalHeaderData::Pre22 {
                    n_vars,
                    n_clauses,
                    top,
                } => WcnfHeaderData::Pre22 {
                    n_vars,
                    n_clauses,
                    top,
                    body_parser: Parser {
                        variant: WcnfPre22Body { top },
                        reader: self.reader,
                        buffer: self.buffer,
                        line_num: self.line_num,
                    },
                },
                WcnfInternalHeaderData::Post22(data) => WcnfHeaderData::Post22(Parser {
                    variant: WcnfPost22(Some(data)),
                    reader: self.reader,
                    buffer: self.buffer,
                    line_num: self.line_num,
                }),
                WcnfInternalHeaderData::Empty => WcnfHeaderData::Empty(self.reader),
            });
        }
        let mut trimmed_line;
        loop {
            if self.read_line()? {
                return Ok(WcnfHeaderData::Empty(self.reader));
            }
            trimmed_line = self.buffer.trim();
            if !trimmed_line.starts_with('c') {
                break;
            }
            self.buffer.clear();
        }
        let post22_data = alt((
            hard_clause.map(WcnfData::HardClause),
            soft_clause.map(|(weight, clause)| WcnfData::SoftClause { weight, clause }),
        ))
        .parse(trimmed_line)
        .ok();
        if let Some(data) = post22_data {
            self.buffer.clear();
            return Ok(WcnfHeaderData::Post22(Parser {
                variant: WcnfPost22(Some(data)),
                reader: self.reader,
                buffer: self.buffer,
                line_num: self.line_num,
            }));
        }
        let (n_vars, n_clauses, top) = match wcnf_p_line.parse(trimmed_line) {
            Err(err) => {
                return Err(ParsingError::from_parse(
                    &err,
                    &self.buffer,
                    // NOTE: `trimmed_line` is always part of `self.buffer`, so this will never
                    // panic
                    utils::substr_offset(&self.buffer, trimmed_line).unwrap(),
                    self.line_num,
                )
                .into());
            }
            Ok(data) => data,
        };
        self.buffer.clear();
        Ok(WcnfHeaderData::Pre22 {
            n_vars,
            n_clauses,
            top,
            body_parser: Parser {
                variant: WcnfPre22Body { top },
                reader: self.reader,
                buffer: self.buffer,
                line_num: self.line_num,
            },
        })
    }
}

#[cfg(feature = "optimization")]
#[derive(Debug)]
enum WcnfHeaderLine {
    Comment(String),
    Header(u32, usize, usize),
    HardClause(Clause),
    SoftClause(usize, Clause),
}

#[cfg(feature = "optimization")]
impl<R> Iterator for Parser<WcnfHeader, R>
where
    R: io::BufRead,
{
    type Item = Result<String, super::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.variant.header_data.is_some() {
            return None;
        }
        match self.read_line() {
            Err(err) => return Some(Err(err.into())),
            Ok(true) => {
                self.variant.header_data = Some(WcnfInternalHeaderData::Empty);
                return None;
            }
            Ok(_) => (),
        }

        let trimmed_line = self.buffer.trim();
        // let data = match comment
        //     .context(StrContext::Label("cnf pre-header comment"))
        //     .parse(trimmed_line)
        let data = match alt((
            comment.map(|c| WcnfHeaderLine::Comment(c.to_owned())),
            hard_clause.map(WcnfHeaderLine::HardClause),
            soft_clause.map(|(weight, clause)| WcnfHeaderLine::SoftClause(weight, clause)),
            wcnf_p_line
                .map(|(n_vars, n_clauses, top)| WcnfHeaderLine::Header(n_vars, n_clauses, top)),
        ))
        .context(StrContext::Label("wcnf header line"))
        .parse(trimmed_line)
        {
            Err(err) => {
                return Some(Err(ParsingError::from_parse(
                    &err,
                    &self.buffer,
                    utils::substr_offset(&self.buffer, trimmed_line).unwrap(),
                    self.line_num,
                )
                .into()))
            }
            Ok(data) => data,
        };
        self.buffer.clear();

        match data {
            WcnfHeaderLine::Comment(comment) => Some(Ok(comment)),
            WcnfHeaderLine::Header(n_vars, n_clauses, top) => {
                self.variant.header_data = Some(WcnfInternalHeaderData::Pre22 {
                    n_vars,
                    n_clauses,
                    top,
                });
                None
            }
            WcnfHeaderLine::HardClause(clause) => {
                self.variant.header_data =
                    Some(WcnfInternalHeaderData::Post22(WcnfData::HardClause(clause)));
                None
            }
            WcnfHeaderLine::SoftClause(weight, clause) => {
                self.variant.header_data =
                    Some(WcnfInternalHeaderData::Post22(WcnfData::SoftClause {
                        weight,
                        clause,
                    }));
                None
            }
        }
    }
}

/// Data that can appear in a WCNF file body
#[cfg(feature = "optimization")]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, PartialEq, Eq)]
pub enum WcnfData {
    /// A hard input clause
    HardClause(Clause),
    /// A soft input clause with a given weight
    SoftClause {
        /// The weight of the clause
        weight: usize,
        /// The clause itself
        clause: Clause,
    },
    /// A comment line in the WCNF body
    Comment(String),
}

/// Identifier type for the WCNF pre-2022 body parser variant
#[cfg(feature = "optimization")]
#[derive(Debug)]
pub struct WcnfPre22Body {
    top: usize,
}

#[cfg(feature = "optimization")]
impl<R> Iterator for Parser<WcnfPre22Body, R>
where
    R: io::BufRead,
{
    type Item = Result<WcnfData, super::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.read_line() {
            Err(err) => return Some(Err(err.into())),
            Ok(true) => return None,
            Ok(_) => (),
        }

        let trimmed_line = self.buffer.trim();
        let data = match alt((
            comment.map(|c| WcnfData::Comment(c.to_owned())),
            soft_clause.map(|(weight, clause)| {
                if weight >= self.variant.top {
                    WcnfData::HardClause(clause)
                } else {
                    WcnfData::SoftClause { weight, clause }
                }
            }),
        ))
        .context(StrContext::Label("wcnf (pre22) body line"))
        .parse(trimmed_line)
        {
            Err(err) => {
                return Some(Err(ParsingError::from_parse(
                    &err,
                    &self.buffer,
                    utils::substr_offset(&self.buffer, trimmed_line).unwrap(),
                    self.line_num,
                )
                .into()))
            }
            Ok(data) => data,
        };
        self.buffer.clear();

        Some(Ok(data))
    }
}

/// Identifier type for the WCNF Post 2022 body parser variant
#[cfg(feature = "optimization")]
#[derive(Debug, Default)]
pub struct WcnfPost22(Option<WcnfData>);

#[cfg(feature = "optimization")]
impl<R> Iterator for Parser<WcnfPost22, R>
where
    R: io::BufRead,
{
    type Item = Result<WcnfData, super::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(data) = self.variant.0.take() {
            return Some(Ok(data));
        }
        match self.read_line() {
            Err(err) => return Some(Err(err.into())),
            Ok(true) => return None,
            Ok(_) => (),
        }

        let trimmed_line = self.buffer.trim();
        let data = match alt((
            comment.map(|c| WcnfData::Comment(c.to_owned())),
            hard_clause.map(WcnfData::HardClause),
            soft_clause.map(|(weight, clause)| WcnfData::SoftClause { weight, clause }),
        ))
        .context(StrContext::Label("wcnf (post22) body line"))
        .parse(trimmed_line)
        {
            Err(err) => {
                return Some(Err(ParsingError::from_parse(
                    &err,
                    &self.buffer,
                    utils::substr_offset(&self.buffer, trimmed_line).unwrap(),
                    self.line_num,
                )
                .into()))
            }
            Ok(data) => data,
        };
        self.buffer.clear();

        Some(Ok(data))
    }
}

/// Data that can appear in a MCNF file body
#[cfg(feature = "multiopt")]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, PartialEq, Eq)]
pub enum McnfData {
    /// A hard input clause
    HardClause(Clause),
    /// A soft input clause with a given weight
    SoftClause {
        /// The index of the objective
        obj_idx: usize,
        /// The weight of the clause
        weight: usize,
        /// The clause itself
        clause: Clause,
    },
    /// A comment line in the MCNF body
    Comment(String),
}

/// Identifier type for the MCNF body parser variant
#[cfg(feature = "multiopt")]
#[derive(Debug, Default)]
pub struct Mcnf();

#[cfg(feature = "multiopt")]
impl<R> Iterator for Parser<Mcnf, R>
where
    R: io::BufRead,
{
    type Item = Result<McnfData, super::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.read_line() {
            Err(err) => return Some(Err(err.into())),
            Ok(true) => return None,
            Ok(_) => (),
        }

        let trimmed_line = self.buffer.trim();
        let data = match alt((
            comment.map(|c| McnfData::Comment(c.to_owned())),
            hard_clause.map(McnfData::HardClause),
            mo_soft_clause.map(|(obj_idx, weight, clause)| McnfData::SoftClause {
                obj_idx,
                weight,
                clause,
            }),
        ))
        .context(StrContext::Label("mcnf body line"))
        .parse(trimmed_line)
        {
            Err(err) => {
                return Some(Err(ParsingError::from_parse(
                    &err,
                    &self.buffer,
                    utils::substr_offset(&self.buffer, trimmed_line).unwrap(),
                    self.line_num,
                )
                .into()))
            }
            Ok(data) => data,
        };
        self.buffer.clear();

        Some(Ok(data))
    }
}

fn cnf_p_line(input: &mut &str) -> ModalResult<(u32, usize)> {
    seq! { _: 'p', _: space1, _: cut_err("cnf"), _: space1, dec_uint, _: space1, dec_uint, _: space0 }
        .context(StrContext::Label("cnf p-line"))
        .parse_next(input)
}

#[cfg(feature = "optimization")]
fn wcnf_p_line(input: &mut &str) -> ModalResult<(u32, usize, usize)> {
    seq! { _: 'p', _: space1, _: cut_err("wcnf"), _: space1, dec_uint, _: space1, dec_uint, _: space1, dec_uint, _: space0 }
        .context(StrContext::Label("wcnf p-line"))
        .parse_next(input)
}

/// Matches a DIMACS comment
fn comment<'i>(input: &mut &'i str) -> ModalResult<&'i str> {
    seq! { 'c', till_line_ending, opt(line_ending) }
        .take()
        .parse_next(input)
}

fn clause(input: &mut &str) -> ModalResult<Clause> {
    terminated(separated(0.., lit, space1), clause_ending)
        .context(StrContext::Label("clause"))
        .parse_next(input)
}

#[cfg(feature = "optimization")]
fn hard_clause(input: &mut &str) -> ModalResult<Clause> {
    use winnow::combinator::cut_err;
    seq! { _: 'h', _: cut_err(space1), cut_err(clause) }
        .map(|(cl,)| cl)
        .context(StrContext::Label("hard clause"))
        .parse_next(input)
}

#[cfg(feature = "optimization")]
fn soft_clause(input: &mut &str) -> ModalResult<(usize, Clause)> {
    seq! { weight, _: space1, clause }
        .context(StrContext::Label("soft clause"))
        .parse_next(input)
}

#[cfg(feature = "multiopt")]
fn mo_soft_clause(input: &mut &str) -> ModalResult<(usize, usize, Clause)> {
    use winnow::combinator::cut_err;
    seq! { _: 'o', _: space0, cut_err(obj_idx), _: cut_err(space1), cut_err(weight), _: cut_err(space1), cut_err(clause) }
        .context(StrContext::Label("MO soft clause"))
        .parse_next(input)
}

#[cfg(feature = "optimization")]
/// Parses a soft clause weight, intentionally accepting `+` signs
fn weight(input: &mut &str) -> ModalResult<usize> {
    use winnow::ascii::dec_uint;

    dec_uint
        .context(StrContext::Label("soft clause weight"))
        .parse_next(input)
}

#[cfg(feature = "multiopt")]
fn obj_idx(input: &mut &str) -> ModalResult<usize> {
    use winnow::{ascii::digit0, token::one_of};

    (one_of('1'..='9'), digit0)
        .take()
        .try_map(str::parse)
        .context(StrContext::Label("objective index"))
        .parse_next(input)
}

fn lit(input: &mut &str) -> ModalResult<Lit> {
    dec_int::<&str, i32, _>
        .try_map(Lit::from_ipasir)
        .context(StrContext::Label("IPASIR literal"))
        .parse_next(input)
}

/// Parses a single DIMACS literal string
///
/// # Errors
///
/// If parsing fails
#[cfg(feature = "_internals")]
pub fn parse_lit(input: &str) -> Result<Lit, ParsingError> {
    lit.parse(input)
        .map_err(|e| ParsingError::from_parse(&e, input, 0, 1))
}

/// Parses the end of a clause
/// A '0' followed by a line-break, as well as a '0' followed by
/// white-space or only a line-break are treated as valid clause endings.
/// This is more lenient than the file format spec.
fn clause_ending<'i>(input: &mut &'i str) -> ModalResult<&'i str> {
    alt((
        (space0, alt((line_ending, eof))).take(),
        (
            space0,
            '0',
            alt(((space0, alt((line_ending, eof))).take(), space1)),
        )
            .take(),
    ))
    .context(StrContext::Label("clause ending"))
    .parse_next(input)
}

/// Writes a CNF to a DIMACS CNF file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
pub fn write_cnf_annotated<W: Write>(
    mut writer: W,
    cnf: &Cnf,
    n_vars: u32,
) -> Result<(), io::Error> {
    writeln!(writer, "c CNF file written by RustSAT")?;
    writeln!(writer, "p cnf {n_vars} {}", cnf.len())?;
    cnf.iter()
        .try_for_each(|cl| write_clause(&mut writer, cl))?;
    writer.flush()
}

/// Input data for writing a CNF instance
#[derive(Debug)]
pub enum CnfLine {
    /// The CNF header with the number of variables and clauses
    Header(u32, usize),
    /// A comment line
    Comment(String),
    /// A clause
    Clause(Clause),
}

impl CnfLine {
    /// Gets the clause on the given line
    #[must_use]
    pub fn clause(self) -> Option<Clause> {
        match self {
            CnfLine::Clause(cl) => Some(cl),
            _ => None,
        }
    }
}

/// Writes a CNF to a DIMACS CNF file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
pub fn write_cnf<W: Write, Iter: Iterator<Item = CnfLine>>(
    mut writer: W,
    mut data: Iter,
) -> Result<(), io::Error> {
    data.try_for_each(|dat| match dat {
        CnfLine::Header(n_vars, n_clauses) => writeln!(writer, "p {n_vars} {n_clauses}"),
        CnfLine::Comment(c) => write!(writer, "c {c}"),
        CnfLine::Clause(cl) => write_clause(&mut writer, &cl),
    })
}

#[cfg(feature = "optimization")]
/// Writes a CNF and soft clauses to a (post 22, no p line) DIMACS WCNF file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
pub fn write_wcnf_annotated<W: Write, CI: WClsIter>(
    mut writer: W,
    cnf: &Cnf,
    softs: (CI, isize),
    n_vars: Option<u32>,
) -> Result<(), io::Error> {
    let (soft_cls, offset) = softs;
    let soft_cls: Vec<(Clause, usize)> = soft_cls.into_iter().collect();
    writeln!(writer, "c WCNF file written by RustSAT")?;
    if let Some(n_vars) = n_vars {
        writeln!(writer, "c {n_vars} variables")?;
    }
    writeln!(writer, "c {} hard clauses", cnf.len())?;
    writeln!(writer, "c {} soft clauses", soft_cls.len())?;
    writeln!(writer, "c objective offset: {offset}")?;
    cnf.iter().try_for_each(|cl| {
        write!(writer, "h ")?;
        write_clause(&mut writer, cl)
    })?;
    soft_cls.into_iter().try_for_each(|(cl, w)| {
        write!(writer, "{w} ")?;
        write_clause(&mut writer, &cl)
    })?;
    writer.flush()
}

#[cfg(feature = "optimization")]
#[derive(Debug)]
/// Input data for writing a single-objective (WCNF) instance
pub enum WcnfLine {
    /// A comment line
    Comment(String),
    /// A hard clause
    Hard(Clause),
    /// A soft clause and its weight
    Soft(Clause, usize),
}

#[cfg(feature = "optimization")]
/// Writes a CNF and soft clauses to a (post 22, no p line) DIMACS WCNF file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
pub fn write_wcnf<W: Write, Iter: Iterator<Item = WcnfLine>>(
    mut writer: W,
    mut data: Iter,
) -> Result<(), io::Error> {
    data.try_for_each(|dat| match dat {
        WcnfLine::Comment(c) => write!(writer, "c {c}"),
        WcnfLine::Hard(cl) => {
            write!(writer, "h ")?;
            write_clause(&mut writer, &cl)
        }
        WcnfLine::Soft(cl, w) => {
            write!(writer, "{w} ")?;
            write_clause(&mut writer, &cl)
        }
    })
}

#[cfg(feature = "multiopt")]
/// Writes a CNF and multiple objectives as sets of soft clauses to a DIMACS MCNF file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
pub fn write_mcnf_annotated<W: Write, Iter: Iterator<Item = (CI, isize)>, CI: WClsIter>(
    mut writer: W,
    cnf: &Cnf,
    softs: Iter,
    n_vars: Option<u32>,
) -> Result<(), io::Error> {
    let (soft_cls, offsets) = softs.into_iter().unzip::<_, _, Vec<_>, Vec<_>>();
    let soft_cls: Vec<Vec<(Clause, usize)>> = soft_cls
        .into_iter()
        .map(|ci| ci.into_iter().collect())
        .collect();
    writeln!(writer, "c MCNF file written by RustSAT")?;
    if let Some(n_vars) = n_vars {
        writeln!(writer, "c {n_vars} variables")?;
    }
    writeln!(writer, "c {} hard clauses", cnf.len())?;
    writeln!(writer, "c {} objectives", soft_cls.len())?;
    write!(writer, "c ( ")?;
    soft_cls
        .iter()
        .try_for_each(|sc| write!(writer, "{} ", sc.len()))?;
    writeln!(writer, ") soft clauses")?;
    write!(writer, "c objective offsets: ( ")?;
    offsets
        .into_iter()
        .try_for_each(|o| write!(writer, "{o} "))?;
    writeln!(writer, ")")?;
    cnf.iter().try_for_each(|cl| {
        write!(writer, "h ")?;
        write_clause(&mut writer, cl)
    })?;
    soft_cls
        .into_iter()
        .enumerate()
        .try_for_each(|(idx, sft_cls)| {
            sft_cls.into_iter().try_for_each(|(cl, w)| {
                write!(writer, "o {} {} ", idx + 1, w)?;
                write_clause(&mut writer, &cl)
            })
        })?;
    writer.flush()
}

#[cfg(feature = "multiopt")]
#[derive(Debug)]
/// Input data for writing a multi-objective (MCNF) instance
pub enum McnfLine {
    /// A comment line
    Comment(String),
    /// A hard clause
    Hard(Clause),
    /// A soft clause, its weight, and its objective index
    Soft(Clause, usize, usize),
}

#[cfg(feature = "multiopt")]
/// Writes a multi-objective instance from an iterator
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
pub fn write_mcnf<W: Write, Iter: Iterator<Item = McnfLine>>(
    mut writer: W,
    mut data: Iter,
) -> Result<(), io::Error> {
    data.try_for_each(|dat| match dat {
        McnfLine::Comment(c) => writeln!(writer, "c {c}"),
        McnfLine::Hard(cl) => {
            write!(writer, "h ")?;
            write_clause(&mut writer, &cl)
        }
        McnfLine::Soft(cl, w, oidx) => {
            write!(writer, "o {} {} ", oidx + 1, w)?;
            write_clause(&mut writer, &cl)
        }
    })
}

fn write_clause<W, C>(writer: &mut W, clause: &C) -> Result<(), io::Error>
where
    W: Write,
    C: AsRef<Cl> + ?Sized,
{
    clause
        .as_ref()
        .into_iter()
        .try_for_each(|l| write!(writer, "{} ", l.to_ipasir()))?;
    writeln!(writer, "0")
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Seek};

    use winnow::Parser as _;

    use crate::{
        clause,
        instances::{Cnf, SatInstance},
        ipasir_lit,
    };

    use super::{
        clause_ending, cnf_p_line, lit, write_cnf_annotated, CnfBody, CnfData, CnfHeader,
        CnfHeaderData, Parser,
    };

    #[test]
    fn parse_lit_pass() {
        assert_eq!(lit.parse_peek("15 "), Ok((" ", ipasir_lit![15])));
        assert_eq!(lit.parse_peek("14 "), Ok((" ", ipasir_lit![14])));
        assert_eq!(lit.parse_peek("-42 "), Ok((" ", ipasir_lit![-42])));
        assert_eq!(lit.parse_peek("42 63"), Ok((" 63", ipasir_lit![42])));
    }

    #[test]
    fn parse_lit_fail() {
        assert!(lit.parse_peek("abc ").is_err());
        assert!(lit.parse_peek(" abc ").is_err());
    }

    #[test]
    fn parse_cnf_p_line_pass() {
        assert_eq!(cnf_p_line.parse_peek("p cnf 23 42"), Ok(("", (23, 42))));
    }

    #[test]
    fn parse_cnf_p_line_fail() {
        assert!(cnf_p_line.parse_peek("a cnf 23 42").is_err());
        assert!(cnf_p_line.parse_peek("p abc 23 42 52").is_err());
        assert!(cnf_p_line.parse_peek("p wcnf 23 42 52").is_err());
        assert!(cnf_p_line.parse_peek("p cnf ab").is_err());
        assert!(cnf_p_line.parse_peek("p wcnf ab").is_err());
    }

    #[test]
    fn parse_clause_ending_pass() {
        assert_eq!(clause_ending.parse_peek("0"), Ok(("", "0")));
        assert_eq!(clause_ending.parse_peek("0 test"), Ok(("test", "0 ")));
        assert_eq!(clause_ending.parse_peek("0\n"), Ok(("", "0\n")));
        assert_eq!(clause_ending.parse_peek("\n"), Ok(("", "\n")));
        assert_eq!(clause_ending.parse_peek("0 \n"), Ok(("", "0 \n")));
        assert_eq!(clause_ending.parse_peek(" \n"), Ok(("", " \n")));
        assert_eq!(clause_ending.parse_peek(""), Ok(("", "")));
    }

    #[test]
    fn parse_clause_ending_fail() {
        assert!(clause_ending.parse_peek("test").is_err());
        assert!(clause_ending.parse_peek("0test").is_err());
    }

    #[test]
    fn parse_cnf_line_pass() {
        assert!(Parser::<CnfBody, _>::new(Cursor::new("c test"))
            .next()
            .is_some_and(
                |res| res.is_ok_and(|parsed| parsed == CnfData::Comment(String::from("c test")))
            ));
        assert!(Parser::<CnfBody, _>::new(Cursor::new("42 34 -16 0"))
            .next()
            .is_some_and(|res| res.is_ok_and(|parsed| parsed
                == CnfData::Clause(clause![ipasir_lit![42], ipasir_lit![34], ipasir_lit![-16]]))));
        assert!(Parser::<CnfBody, _>::new(Cursor::new(" 42 34"))
            .next()
            .is_some_and(|res| res.is_ok_and(
                |parsed| parsed == CnfData::Clause(clause![ipasir_lit![42], ipasir_lit![34]])
            )));
    }

    #[test]
    fn parse_cnf_line_fail() {
        assert!(Parser::<CnfBody, _>::new(Cursor::new("42 34 0 -16 0"))
            .next()
            .is_some_and(|res| res.is_err()));
        assert!(Parser::<CnfBody, _>::new(Cursor::new("42 34 a -16 0"))
            .next()
            .is_some_and(|res| res.is_err()));
    }

    #[test]
    fn parse_cnf_preamble() {
        assert!(matches!(
            Parser::<CnfHeader, _>::new(Cursor::new("c test\np cnf 5 2\n1 2 0")).forward_to_body(),
            Ok(CnfHeaderData {
                n_vars: 5,
                n_clauses: 2,
                body_parser: _
            })
        ));
    }

    #[test]
    fn parse_cnf_body_pass() {
        let input = "1 2 0\n-3 4 5 0\n";

        let parser = Parser::<CnfBody, _>::new(Cursor::new(input));
        let data = parser.collect::<Result<Vec<_>, _>>().unwrap();

        #[cfg(feature = "serde")]
        insta::assert_yaml_snapshot!("cnf_body_pass", data, input);
        #[cfg(not(feature = "serde"))]
        assert_eq!(
            data,
            vec![
                CnfData::Clause(clause![ipasir_lit![1], ipasir_lit![2]]),
                CnfData::Clause(clause![!ipasir_lit![3], ipasir_lit![4], ipasir_lit![5]])
            ]
        );
    }

    #[test]
    fn parse_cnf_body_fail() {
        let input = "1 2 0\n-3 four 5 0\n";

        let parser = Parser::<CnfBody, _>::new(Cursor::new(input));
        let err = parser.collect::<Result<Vec<_>, _>>().unwrap_err();

        insta::assert_snapshot!("parse_cnf_body_fail", format!("{err}"), input);
    }

    #[test]
    fn parse_cnf() {
        let input = "p cnf 5 2\n1 2 0\n\n-3 4 5 0\n";

        let data =
            SatInstance::<crate::instances::BasicVarManager>::from_dimacs(Cursor::new(input))
                .unwrap();

        #[cfg(feature = "serde")]
        insta::assert_yaml_snapshot!("parse_cnf", data, input);

        #[cfg(not(feature = "serde"))]
        {
            let mut true_inst: SatInstance = SatInstance::new();
            true_inst.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
            true_inst.add_clause(clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

            assert_eq!(data, true_inst);
        }
    }

    #[test]
    fn cnf_empty() {
        let input = "c test\n";

        let err =
            SatInstance::<crate::instances::BasicVarManager>::from_dimacs(&mut Cursor::new(input))
                .unwrap_err();

        insta::assert_snapshot!("cnf_empty", err, input);
    }

    #[test]
    fn cnf_no_header() {
        let input = "c p cnf 5 2\n1 2 0\n-3 4 5 0\n";

        let err = SatInstance::<crate::instances::BasicVarManager>::from_dimacs(Cursor::new(input))
            .unwrap_err();

        insta::assert_snapshot!("cnf_no_header", format!("{err}"), input);
    }

    #[test]
    fn cnf_invalid_header() {
        let input = "p cnf five 2\n1 2 0\n-3 4 5 0\n";

        let err = SatInstance::<crate::instances::BasicVarManager>::from_dimacs(Cursor::new(input))
            .unwrap_err();

        insta::assert_snapshot!("cnf_invalid_header", format!("{err}"), input);
    }

    #[test]
    fn cnf_comments_before_header() {
        let input = "c test\np cnf 5 2\n1 2 0\n-3 4 5 0\n";

        let mut parser = Parser::<CnfHeader, _>::new(Cursor::new(input));
        let comments = (&mut parser).collect::<Result<Vec<_>, _>>().unwrap();

        assert_eq!(comments, vec!["c test"]);

        assert!(matches!(
            parser.forward_to_body(),
            Ok(CnfHeaderData {
                n_vars: 5,
                n_clauses: 2,
                body_parser: _
            })
        ));
    }

    #[test]
    fn cnf_invalid_before_header() {
        let input = "c test\nthis is an invalid line\np cnf 5 2\n1 2 0\n-3 4 5 0\n";

        let mut parser = Parser::<CnfHeader, _>::new(Cursor::new(input));
        let err = (&mut parser).collect::<Result<Vec<_>, _>>().unwrap_err();

        insta::assert_snapshot!("cnf_invalid_before_header", format!("{err}"), input);
    }

    #[test]
    fn write_parse_cnf() {
        let mut true_cnf = Cnf::new();
        true_cnf.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_cnf.add_clause(clause![ipasir_lit![2], ipasir_lit![1]]);

        let mut cursor = Cursor::new(vec![]);

        write_cnf_annotated(&mut cursor, &true_cnf, 2).unwrap();

        cursor.rewind().unwrap();

        let parsed_inst =
            SatInstance::<crate::instances::BasicVarManager>::from_dimacs(&mut cursor).unwrap();
        let (parsed_cnf, _) = parsed_inst.into_cnf();

        assert_eq!(parsed_cnf, true_cnf);
    }

    #[cfg(feature = "optimization")]
    mod opt {
        use std::io::{Cursor, Seek};

        use winnow::Parser as _;

        use crate::{
            clause,
            instances::{Objective, OptInstance, SatInstance},
            ipasir_lit,
        };

        use super::super::{
            obj_idx, wcnf_p_line, weight, write_wcnf_annotated, Parser, WcnfData, WcnfHeader,
            WcnfHeaderData, WcnfPost22, WcnfPre22Body,
        };

        #[test]
        fn parse_obj_idx_pass() {
            assert_eq!(obj_idx.parse_peek("15 "), Ok((" ", 15)));
            assert_eq!(obj_idx.parse_peek("42 63"), Ok((" 63", 42)));
        }

        #[test]
        fn parse_idx_fail() {
            assert!(obj_idx.parse_peek("0 ").is_err());
            assert!(obj_idx.parse_peek("-15 ").is_err());
            assert!(obj_idx.parse_peek("abc ").is_err());
            assert!(obj_idx.parse_peek(" abc ").is_err());
        }

        #[test]
        fn parse_weight_pass() {
            assert_eq!(weight.parse_peek("15 "), Ok((" ", 15)));
            assert_eq!(weight.parse_peek("42 63"), Ok((" 63", 42)));
            assert_eq!(weight.parse_peek("0 "), Ok((" ", 0)));
        }

        #[test]
        fn parse_weight_fail() {
            assert!(weight.parse_peek("-2 ").is_err());
            assert!(weight.parse_peek("abc ").is_err());
            assert!(weight.parse_peek(" abc ").is_err());
        }

        #[test]
        fn parse_wcnf_p_line_pass() {
            assert_eq!(
                wcnf_p_line.parse_peek("p wcnf 23 42 52"),
                Ok(("", (23, 42, 52)))
            );
        }

        #[test]
        fn parse_wcnf_p_line_fail() {
            assert!(wcnf_p_line.parse_peek("a cnf 23 42").is_err());
            assert!(wcnf_p_line.parse_peek("p abc 23 42 52").is_err());
            assert!(wcnf_p_line.parse_peek("p cnf 23 42").is_err());
            assert!(wcnf_p_line.parse_peek("p cnf ab").is_err());
            assert!(wcnf_p_line.parse_peek("p wcnf ab").is_err());
        }

        #[test]
        fn parse_wcnf_pre22_line_pass() {
            assert!((Parser {
                variant: WcnfPre22Body { top: 100 },
                reader: Cursor::new("c test"),
                buffer: String::new(),
                line_num: 0,
            })
            .next()
            .is_some_and(
                |res| res.is_ok_and(|parsed| parsed == WcnfData::Comment(String::from("c test")))
            ));
            assert!((Parser {
                variant: WcnfPre22Body { top: 100 },
                reader: Cursor::new("42 34 -16 0"),
                buffer: String::new(),
                line_num: 0,
            })
            .next()
            .is_some_and(|res| res.is_ok_and(|parsed| parsed
                == WcnfData::SoftClause {
                    weight: 42,
                    clause: clause![ipasir_lit![34], ipasir_lit![-16]]
                })));
            assert!((Parser {
                variant: WcnfPre22Body { top: 100 },
                reader: Cursor::new("100 34 -16 0"),
                buffer: String::new(),
                line_num: 0,
            })
            .next()
            .is_some_and(|res| res
                .is_ok_and(|parsed| parsed
                    == WcnfData::HardClause(clause![ipasir_lit![34], ipasir_lit![-16]]))));
        }

        #[test]
        fn parse_wcnf_post22_line_pass() {
            assert!(Parser::<WcnfPost22, _>::new(Cursor::new("c test"))
                .next()
                .is_some_and(|res| res
                    .is_ok_and(|parsed| parsed == WcnfData::Comment(String::from("c test")))));
            assert!(Parser::<WcnfPost22, _>::new(Cursor::new("42 34 -16 0"))
                .next()
                .is_some_and(|res| res.is_ok_and(|parsed| parsed
                    == WcnfData::SoftClause {
                        weight: 42,
                        clause: clause![ipasir_lit![34], ipasir_lit![-16]]
                    })));
            assert!(Parser::<WcnfPost22, _>::new(Cursor::new("h 42 34 -16 0"))
                .next()
                .is_some_and(|res| res.is_ok_and(|parsed| parsed
                    == WcnfData::HardClause(clause![
                        ipasir_lit![42],
                        ipasir_lit![34],
                        ipasir_lit![-16]
                    ]))));
        }

        #[test]
        fn parse_wcnf_pre22_preamble() {
            assert!(matches!(
                Parser::<WcnfHeader, _>::new(Cursor::new("c test\np wcnf 5 2 10\n1 2 0"))
                    .forward_to_body(),
                Ok(WcnfHeaderData::Pre22 {
                    n_vars: 5,
                    n_clauses: 2,
                    top: 10,
                    body_parser: _
                })
            ));
        }

        #[test]
        fn parse_wcnf_post22_preamble() {
            assert!(matches!(
                Parser::<WcnfHeader, _>::new(Cursor::new("c test\nh 5 2 0\n1 2 0"))
                    .forward_to_body(),
                Ok(WcnfHeaderData::Post22(_))
            ));
            assert!(matches!(
                Parser::<WcnfHeader, _>::new(Cursor::new("c test\n1 2 0\nh 5 2 0"))
                    .forward_to_body(),
                Ok(WcnfHeaderData::Post22(_))
            ));
            assert!(matches!(
                Parser::<WcnfHeader, _>::new(Cursor::new("c test")).forward_to_body(),
                Ok(WcnfHeaderData::Empty(_))
            ));
        }

        #[test]
        fn parse_wcnf_pre22_body_pass() {
            let data = "42 1 2 0\n10 -3 4 5 0\n";

            let parser = Parser {
                variant: WcnfPre22Body { top: 42 },
                reader: Cursor::new(data),
                buffer: String::new(),
                line_num: 0,
            };
            let clauses = parser.collect::<Result<Vec<_>, _>>().unwrap();

            assert_eq!(
                clauses,
                vec![
                    WcnfData::HardClause(clause![ipasir_lit![1], ipasir_lit![2]]),
                    WcnfData::SoftClause {
                        weight: 10,
                        clause: clause![!ipasir_lit![3], ipasir_lit![4], ipasir_lit![5]]
                    }
                ]
            );
        }

        #[test]
        fn parse_wcnf_pre22_body_fail() {
            let input = "42 1 2 0\n10 -3 four 5 0\n";

            let parser = Parser {
                variant: WcnfPre22Body { top: 42 },
                reader: Cursor::new(input),
                buffer: String::new(),
                line_num: 0,
            };
            let err = parser.collect::<Result<Vec<_>, _>>().unwrap_err();

            insta::assert_snapshot!("parse_wcnf_pre22_body_fail", format!("{err}"), input);
        }

        #[test]
        fn parse_wcnf_post22_body_pass() {
            let data = "h 1 2 0\n10 -3 4 5 0\n";

            let parser = Parser::<WcnfPost22, _>::new(Cursor::new(data));
            let clauses = parser.collect::<Result<Vec<_>, _>>().unwrap();

            assert_eq!(
                clauses,
                vec![
                    WcnfData::HardClause(clause![ipasir_lit![1], ipasir_lit![2]]),
                    WcnfData::SoftClause {
                        weight: 10,
                        clause: clause![!ipasir_lit![3], ipasir_lit![4], ipasir_lit![5]]
                    }
                ]
            );
        }

        #[test]
        fn parse_wcnf_post22_body_fail() {
            let input = "h 1 2 0\n10 -3 four 5 0\n";

            let parser = Parser::<WcnfPost22, _>::new(Cursor::new(input));
            let err = parser.collect::<Result<Vec<_>, _>>().unwrap_err();

            insta::assert_snapshot!("parse_wcnf_post22_body_fail", format!("{err}"), input);
        }

        #[test]
        fn parse_wcnf_pre22() {
            let input = "p wcnf 5 2 42\n42 1 2 0\n10 -3 4 5 0\n";

            let data =
                OptInstance::<crate::instances::BasicVarManager>::from_dimacs(Cursor::new(input))
                    .unwrap();

            #[cfg(feature = "serde")]
            insta::assert_yaml_snapshot!("parse_wcnf_pre22", data, input);

            #[cfg(not(feature = "serde"))]
            {
                use crate::{instances::ManageVars, types::Var};

                let mut true_constrs: SatInstance = SatInstance::new();
                let mut true_obj = Objective::new();
                true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
                true_constrs
                    .var_manager_mut()
                    .increase_next_free(Var::new(5));
                true_obj
                    .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

                assert_eq!(data, OptInstance::compose(true_constrs, true_obj));
            }
        }

        #[test]
        fn parse_wcnf_pre22_duplication() {
            let input = "p wcnf 3 5 42\n1 1 2 0\n1 1 2 0\n2 -3 0\n8 -3 0\n42 -3 0\n";

            let data =
                OptInstance::<crate::instances::BasicVarManager>::from_dimacs(Cursor::new(input))
                    .unwrap();

            #[cfg(feature = "serde")]
            insta::assert_yaml_snapshot!("parse_wcnf_pre22_duplication", data, input);

            #[cfg(not(feature = "serde"))]
            {
                use crate::{instances::ManageVars, types::Var};

                let mut true_constrs: SatInstance = SatInstance::new();
                let mut true_obj = Objective::new();
                true_constrs.add_clause(clause![ipasir_lit![-3]]);
                true_constrs
                    .var_manager_mut()
                    .increase_next_free(Var::new(3));
                true_obj.add_soft_clause(2, clause![ipasir_lit![1], ipasir_lit![2]]);
                true_obj.add_soft_lit(10, ipasir_lit![3]);

                assert_eq!(data, OptInstance::compose(true_constrs, true_obj));
            }
        }

        #[test]
        fn parse_wcnf_post22() {
            let input = "h 1 2 0\n10 -3 4 5 0\n";

            let data =
                OptInstance::<crate::instances::BasicVarManager>::from_dimacs(Cursor::new(input))
                    .unwrap();

            #[cfg(feature = "serde")]
            insta::assert_yaml_snapshot!("parse_wcnf_post22", data, input);

            #[cfg(not(feature = "serde"))]
            {
                let mut true_constrs: SatInstance = SatInstance::new();
                let mut true_obj = Objective::new();
                true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
                true_obj
                    .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

                assert_eq!(data, OptInstance::compose(true_constrs, true_obj));
            }
        }
        #[test]
        fn parse_wcnf_post22_duplication() {
            let input = "1 1 2 0\n1 1 2 0\n2 -3 0\n8 -3 0\nh -3 0\n";

            let data =
                OptInstance::<crate::instances::BasicVarManager>::from_dimacs(Cursor::new(input))
                    .unwrap();

            #[cfg(feature = "serde")]
            insta::assert_yaml_snapshot!("parse_wcnf_post22_duplication", data, input);

            #[cfg(not(feature = "serde"))]
            {
                let mut true_constrs: SatInstance = SatInstance::new();
                let mut true_obj = Objective::new();
                true_constrs.add_clause(clause![ipasir_lit![-3]]);
                true_obj.add_soft_clause(2, clause![ipasir_lit![1], ipasir_lit![2]]);
                true_obj.add_soft_lit(10, ipasir_lit![3]);

                assert_eq!(data, OptInstance::compose(true_constrs, true_obj));
            }
        }

        #[test]
        fn wcnf_pre22_invalid_header() {
            let input = "p wcnf five 2 42\n42 1 2 0\n10 -3 4 5 0\n";

            let parser = Parser::<WcnfHeader, _>::new(Cursor::new(input));
            let err = parser.collect::<Result<Vec<_>, _>>().unwrap_err();

            insta::assert_snapshot!("wcnf_pre22_invalid_header", format!("{err}"), input);
        }

        #[test]
        fn wcnf_pre22_invalid_header_2() {
            let input = "p wcnf five 2 42\n42 1 2 0\n10 -3 4 5 0\n";

            let err = OptInstance::<crate::instances::BasicVarManager>::from_dimacs(
                &mut Cursor::new(input),
            )
            .unwrap_err();

            insta::assert_snapshot!("wcnf_pre22_invalid_header_2", format!("{err}"), input);
        }

        #[test]
        fn wcnf_pre22_comments_before_header() {
            let input = "c test\np wcnf 5 2 42\n42 1 2 0\n10 -3 4 5 0\n";

            let mut parser = Parser::<WcnfHeader, _>::new(Cursor::new(input));
            let comments = (&mut parser).collect::<Result<Vec<_>, _>>().unwrap();

            assert_eq!(comments, vec!["c test"]);

            assert!(matches!(
                parser.forward_to_body(),
                Ok(WcnfHeaderData::Pre22 {
                    n_vars: 5,
                    n_clauses: 2,
                    top: 42,
                    body_parser: _
                })
            ));
        }

        #[test]
        fn wcnf_post22_comments_before_header() {
            let input = "c test\nh 1 2 0\n10 -3 4 5 0\n";

            let mut parser = Parser::<WcnfHeader, _>::new(Cursor::new(input));
            let comments = (&mut parser).collect::<Result<Vec<_>, _>>().unwrap();

            assert_eq!(comments, vec!["c test"]);

            assert!(matches!(
                parser.forward_to_body(),
                Ok(WcnfHeaderData::Post22(_))
            ));
        }

        #[test]
        fn wcnf_invalid_before_header() {
            let input =
                "c test\nthis is an invalid line\np wcnf five 2 42\n42 1 2 0\n10 -3 4 5 0\n";

            let mut parser = Parser::<WcnfHeader, _>::new(Cursor::new(input));
            let err = (&mut parser).collect::<Result<Vec<_>, _>>().unwrap_err();

            insta::assert_snapshot!("wcnf_invalid_before_header", format!("{err}"), input);
        }

        #[test]
        fn write_parse_wcnf() {
            let mut true_constrs: SatInstance = SatInstance::new();
            let mut true_obj = Objective::new();
            true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
            true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);
            let offset = true_obj.offset();

            let mut cursor = Cursor::new(vec![]);

            write_wcnf_annotated(
                &mut cursor,
                true_constrs.cnf(),
                (true_obj.iter_soft_cls(), offset),
                Some(5),
            )
            .unwrap();

            cursor.rewind().unwrap();

            let parsed_inst =
                OptInstance::<crate::instances::BasicVarManager>::from_dimacs(&mut cursor).unwrap();

            assert_eq!(parsed_inst, OptInstance::compose(true_constrs, true_obj));
        }
    }

    #[cfg(feature = "multiopt")]
    mod multiopt {
        use std::io::{Cursor, Seek};

        use crate::{
            clause,
            instances::{MultiOptInstance, Objective, SatInstance},
            ipasir_lit,
        };

        use super::super::{write_mcnf_annotated, Mcnf, McnfData, Parser};

        #[test]
        fn parse_mcnf_line_pass() {
            assert!(Parser::<Mcnf, _>::new(Cursor::new("c test"))
                .next()
                .is_some_and(|res| res
                    .is_ok_and(|parsed| parsed == McnfData::Comment(String::from("c test")))));
            assert!(Parser::<Mcnf, _>::new(Cursor::new("o 42 34 -16 0"))
                .next()
                .is_some_and(|res| res.is_ok_and(|parsed| parsed
                    == McnfData::SoftClause {
                        obj_idx: 42,
                        weight: 34,
                        clause: clause![ipasir_lit![-16]]
                    })));
            // old format for backwards compatibility
            assert!(Parser::<Mcnf, _>::new(Cursor::new("o42 34 -16 0"))
                .next()
                .is_some_and(|res| res.is_ok_and(|parsed| parsed
                    == McnfData::SoftClause {
                        obj_idx: 42,
                        weight: 34,
                        clause: clause![ipasir_lit![-16]]
                    })));
            assert!(Parser::<Mcnf, _>::new(Cursor::new("h 42 34 -16 0"))
                .next()
                .is_some_and(|res| res.is_ok_and(|parsed| parsed
                    == McnfData::HardClause(clause![
                        ipasir_lit![42],
                        ipasir_lit![34],
                        ipasir_lit![-16]
                    ]))));
        }

        #[test]
        fn parse_mcnf_body_pass() {
            let input = "h 1 2 0\no 2 10 -3 4 5 0\n";

            let parser = Parser::<Mcnf, _>::new(Cursor::new(input));
            let data = parser.collect::<Result<Vec<_>, _>>().unwrap();

            #[cfg(feature = "serde")]
            insta::assert_yaml_snapshot!("mcnf_body_pass", data, input);
            #[cfg(not(feature = "serde"))]
            assert_eq!(
                data,
                vec![
                    McnfData::HardClause(clause![ipasir_lit![1], ipasir_lit![2]]),
                    McnfData::SoftClause {
                        obj_idx: 2,
                        weight: 10,
                        clause: clause![!ipasir_lit![3], ipasir_lit![4], ipasir_lit![5]]
                    }
                ]
            );
        }

        #[test]
        fn parse_mcnf_body_fail() {
            let input = "h 1 2 0\no2 10 -3 four 5 0\n";

            let parser = Parser::<Mcnf, _>::new(Cursor::new(input));
            let err = parser.collect::<Result<Vec<_>, _>>().unwrap_err();

            insta::assert_snapshot!("parse_mcnf_body_fail", format!("{err}"), input);
        }

        #[test]
        fn parse_mcnf() {
            let input = "c test\nh 1 2 0\no 2 10 -3 4 5 0\no 1 3 -1 0\n";

            let data = MultiOptInstance::<crate::instances::BasicVarManager>::from_dimacs(
                Cursor::new(input),
            )
            .unwrap();

            #[cfg(feature = "serde")]
            insta::assert_yaml_snapshot!("parse_mcnf", data, input);

            #[cfg(not(feature = "serde"))]
            {
                let mut true_constrs: SatInstance = SatInstance::new();
                let mut true_obj0 = Objective::new();
                let mut true_obj1 = Objective::new();
                true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
                true_obj0.add_soft_clause(3, clause![ipasir_lit![-1]]);
                true_obj1
                    .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

                assert_eq!(
                    data,
                    MultiOptInstance::compose(true_constrs, vec![true_obj0, true_obj1])
                );
            }
        }

        #[test]
        fn parse_mcnf_duplication() {
            let input = "c test\nh 1 2 0\no 2 10 -3 4 5 0\no 2 10 -3 4 5 0\no 1 3 -1 0\no 1 3 -1 0";

            let data = MultiOptInstance::<crate::instances::BasicVarManager>::from_dimacs(
                Cursor::new(input),
            )
            .unwrap();

            #[cfg(feature = "serde")]
            insta::assert_yaml_snapshot!("parse_mcnf_duplication", data, input);

            #[cfg(not(feature = "serde"))]
            {
                let mut true_constrs: SatInstance = SatInstance::new();
                let mut true_obj0 = Objective::new();
                let mut true_obj1 = Objective::new();
                true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
                true_obj0.add_soft_lit(3, ipasir_lit![1]);
                // increasing an existing soft literal or soft clause causes the instance to become weighted.
                true_obj0.increase_soft_lit(3, ipasir_lit![1]);
                true_obj1
                    .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);
                true_obj1.increase_soft_clause(
                    10,
                    clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]],
                );

                assert_eq!(
                    data,
                    MultiOptInstance::compose(true_constrs, vec![true_obj0, true_obj1])
                );
            }
        }

        #[test]
        fn write_parse_mcnf() {
            let mut true_constrs: SatInstance = SatInstance::new();
            let mut true_obj0 = Objective::new();
            let mut true_obj1 = Objective::new();
            true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
            true_obj0.add_soft_clause(3, clause![ipasir_lit![-1]]);
            let offset0 = true_obj0.offset();
            true_obj1.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);
            let offset1 = true_obj1.offset();

            let mut cursor = Cursor::new(vec![]);

            write_mcnf_annotated(
                &mut cursor,
                true_constrs.cnf(),
                vec![
                    (true_obj0.iter_soft_cls(), offset0),
                    (true_obj1.iter_soft_cls(), offset1),
                ]
                .into_iter(),
                Some(5),
            )
            .unwrap();

            cursor.rewind().unwrap();

            let parsed_inst =
                MultiOptInstance::<crate::instances::BasicVarManager>::from_dimacs(&mut cursor)
                    .unwrap();

            assert_eq!(
                parsed_inst,
                MultiOptInstance::compose(true_constrs, vec![true_obj0, true_obj1])
            );
        }
    }
}
