//! # Parsing and Writing DIMACS Files
//!
//! Internal module containing functions for parsing DIMACS files.
//! The approach is to accept input instances, even if they are not technically
//! in spec, as long as the input is still reasonable.
//!
//! ## References
//!
//! - [DIMACS CNF](http://www.satcompetition.org/2011/format-benchmarks2011.html)
//! - [DIMACS WCNF pre22](https://maxsat-evaluations.github.io/2017/rules.html#input)
//! - [DIMACS WCNF post22](https://maxsat-evaluations.github.io/2022/rules.html#input)

use super::{SatInstance, CNF};
use crate::types::{Clause, Lit, RsHashMap, Var};
use nom::error::Error as NomError;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{i32, line_ending, multispace0, multispace1, u64},
    combinator::{all_consuming, map_res, recognize, success},
    error::{Error, ErrorKind, ParseError},
    multi::separated_list0,
    sequence::{pair, terminated, tuple},
    IResult,
};
use std::{
    convert::TryFrom,
    fmt,
    io::{self, BufRead, BufReader, Read, Write},
};

#[cfg(feature = "multiopt")]
use super::MultiOptInstance;
#[cfg(feature = "optimization")]
use super::{Objective, OptInstance};
#[cfg(feature = "optimization")]
use nom::sequence::separated_pair;

#[cfg(feature = "optimization")]
type BodyContent = (SatInstance, Vec<Objective>);
#[cfg(not(feature = "optimization"))]
type BodyContent = SatInstance;

/// Parses a CNF instance from a reader (typically a (compressed) file)
pub fn parse_cnf<R: Read>(reader: R) -> Result<SatInstance, DimacsError> {
    let reader = BufReader::new(reader);
    let content = parse_dimacs(reader)?;
    #[cfg(not(feature = "optimization"))]
    {
        Ok(content)
    }
    #[cfg(feature = "optimization")]
    {
        Ok(content.0)
    }
}

#[cfg(feature = "optimization")]
/// Parses a WCNF instance (old or new format) from a reader (typically a
/// (compressed) file). The objective with the index obj_idx is used.
pub fn parse_wcnf_with_idx<R: Read>(reader: R, obj_idx: usize) -> Result<OptInstance, DimacsError> {
    let reader = BufReader::new(reader);
    let (constrs, objs) = parse_dimacs(reader)?;
    if objs.is_empty() {
        return Err(DimacsError::InvalidInstanceType);
    } else if obj_idx >= objs.len() {
        return Err(DimacsError::ObjNoExist(objs.len()));
    }
    Ok(OptInstance::compose(
        constrs,
        objs.into_iter().skip(obj_idx).next().unwrap(),
    ))
}

#[cfg(feature = "multiopt")]
/// Parses a MCNF instance (old or new format) from a reader (typically a (compressed) file)
pub fn parse_mcnf<R: Read>(reader: R) -> Result<MultiOptInstance, DimacsError> {
    let reader = BufReader::new(reader);
    let (constrs, objs) = parse_dimacs(reader)?;
    if objs.is_empty() {
        return Err(DimacsError::InvalidInstanceType);
    }
    Ok(MultiOptInstance::compose(constrs, objs))
}

/// Errors occuring within the DIMACS parsing module
#[derive(Debug)]
pub enum DimacsError {
    /// Expected different instance type
    InvalidInstanceType,
    /// Invalid literal in the file
    Lit(String),
    /// Invalid ending of a clause
    ClauseEnding(String),
    /// Invalid objective index
    ObjIdx(String),
    /// Invalid weight
    Weight(String),
    /// A comment appeared in a clause
    CommentInClause(String),
    /// The preamble never ended
    PreambleNoEnd,
    /// P line value is too large to fit in a [`usize`]
    PValTooLarge(u64),
    /// Invalid p line
    PLine(String),
    /// The requested objective does not exist
    ObjNoExist(usize),
    /// IO error reading file
    IOError(io::Error),
    /// Base error from nom parsing
    NomError(String, ErrorKind),
    /// Incomplete nom error
    NomIncomplete,
}

impl PartialEq for DimacsError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Lit(l0), Self::Lit(r0)) => l0 == r0,
            (Self::ClauseEnding(l0), Self::ClauseEnding(r0)) => l0 == r0,
            (Self::ObjIdx(l0), Self::ObjIdx(r0)) => l0 == r0,
            (Self::Weight(l0), Self::Weight(r0)) => l0 == r0,
            (Self::CommentInClause(l0), Self::CommentInClause(r0)) => l0 == r0,
            (Self::ObjNoExist(l0), Self::ObjNoExist(r0)) => l0 == r0,
            (Self::IOError(_), Self::IOError(_)) => true,
            (Self::NomError(l0, l1), Self::NomError(r0, r1)) => l0 == r0 && l1 == r1,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

impl fmt::Display for DimacsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DimacsError::InvalidInstanceType => write!(f, "Expected different instance type"),
            DimacsError::Lit(str) => write!(f, "Invalid literal: {}", str),
            DimacsError::ClauseEnding(str) => write!(f, "Invalid clause ending: {}", str),
            DimacsError::ObjIdx(str) => write!(f, "Invalid objective index: {}", str),
            DimacsError::Weight(str) => write!(f, "Invalid weight: {}", str),
            DimacsError::CommentInClause(str) => write!(f, "Found comment in clause: {}", str),
            DimacsError::PreambleNoEnd => write!(f, "Preamble never ends"),
            DimacsError::PValTooLarge(val) => write!(
                f,
                "Value in p line is too large to fit in a `usize`: {}",
                val
            ),
            DimacsError::PLine(line) => write!(f, "Invalid p line: {}", line),
            DimacsError::ObjNoExist(n_obj) => write!(f, "The file only has {} objectives", n_obj),
            DimacsError::IOError(ioe) => write!(f, "{}", ioe),
            DimacsError::NomError(str, kind) => write!(f, "Nom error: {}, {:?}", str, kind),
            DimacsError::NomIncomplete => write!(f, "Nom parser requested more data"),
        }
    }
}

impl ParseError<&str> for DimacsError {
    fn from_error_kind(input: &str, kind: ErrorKind) -> Self {
        Self::NomError(String::from(input), kind)
    }

    fn append(_: &str, _: ErrorKind, other: Self) -> Self {
        // Other error always has precedence. This should prefer more meaningful
        // errors than [`DimacsError::NomError`]
        other
    }
}

/// Internal type of possible preambles
#[derive(PartialEq, Debug)]
enum Preamble {
    Cnf {
        n_vars: usize,
        n_clauses: usize,
    },
    #[cfg(feature = "optimization")]
    WcnfPre22 {
        n_vars: usize,
        n_clauses: usize,
        top: usize,
    },
    #[cfg(feature = "optimization")]
    NoPLine {
        first_line: String,
    },
}

/// Top level parser
fn parse_dimacs<R>(reader: R) -> Result<BodyContent, DimacsError>
where
    R: BufRead,
{
    let (reader, preamble) = parse_preamble(reader)?;
    let content = match preamble {
        Preamble::Cnf {
            n_vars: _,    // Intentionally ignored (lean acceptance)
            n_clauses: _, // Intentionally ignored (lean acceptance)
        } => parse_cnf_body(reader),
        #[cfg(feature = "optimization")]
        Preamble::WcnfPre22 {
            n_vars: _,    // Intentionally ignored (lean acceptance)
            n_clauses: _, // Intentionally ignored (lean acceptance)
            top,
        } => parse_wcnf_pre22_body(reader, top),
        #[cfg(feature = "optimization")]
        Preamble::NoPLine { first_line } => parse_no_pline_body(reader, &first_line),
    }?;
    Ok(content)
}

fn unwrap_dimacs_error(err: nom::Err<DimacsError>) -> DimacsError {
    match err {
        nom::Err::Incomplete(_) => DimacsError::NomIncomplete,
        nom::Err::Error(e) => e,
        nom::Err::Failure(e) => e,
    }
}

/// Parses preamble and determines type of instance/file format
fn parse_preamble<R: BufRead>(mut reader: R) -> Result<(R, Preamble), DimacsError> {
    loop {
        let mut buf = String::new();
        match reader.read_line(&mut buf) {
            Ok(len) => {
                if len == 0 {
                    return Err(DimacsError::PreambleNoEnd);
                }
            }
            Err(ioe) => return Err(DimacsError::IOError(ioe)),
        };
        if buf.starts_with('c') {
            continue;
        }
        if buf.starts_with('p') {
            let (_, preamble) = parse_p_line(&buf).map_err(unwrap_dimacs_error)?;
            return Ok((reader, preamble));
        }
        #[cfg(feature = "optimization")]
        return Ok((reader, Preamble::NoPLine { first_line: buf }));
        #[cfg(not(feature = "optimization"))]
        return Err(nom::Err::Failure(Error::new(reader, ErrorKind::Tag)));
    }
}

/// Main parser for CNF file
fn parse_cnf_body<R>(mut reader: R) -> Result<BodyContent, DimacsError>
where
    R: BufRead,
{
    let mut inst = SatInstance::new();
    loop {
        let mut buf = String::new();
        match reader.read_line(&mut buf) {
            Ok(len) => {
                if len == 0 {
                    #[cfg(feature = "optimization")]
                    return Ok((inst, vec![]));
                    #[cfg(not(feature = "optimization"))]
                    return Ok(inst);
                }
            }
            Err(ioe) => return Err(DimacsError::IOError(ioe)),
        };
        let (_, opt_clause) = parse_cnf_line(&buf).map_err(unwrap_dimacs_error)?;
        match opt_clause {
            Some(clause) => inst.add_clause(clause),
            None => (),
        }
    }
}

#[cfg(feature = "optimization")]
/// Main parser for WCNF pre 22 (with p line)
fn parse_wcnf_pre22_body<R>(mut reader: R, top: usize) -> Result<BodyContent, DimacsError>
where
    R: BufRead,
{
    let mut constrs = SatInstance::new();
    let mut obj = Objective::new();
    loop {
        let mut buf = String::new();
        match reader.read_line(&mut buf) {
            Ok(len) => {
                if len == 0 {
                    return Ok((constrs, if obj.is_empty() { vec![] } else { vec![obj] }));
                }
            }
            Err(ioe) => return Err(DimacsError::IOError(ioe)),
        };
        let (_, opt_wclause) = parse_wcnf_pre22_line(&buf).map_err(unwrap_dimacs_error)?;
        match opt_wclause {
            None => (),
            Some((w, clause)) => {
                if w >= top {
                    constrs.add_clause(clause);
                } else {
                    obj.add_soft_clause(w, clause);
                }
            }
        };
    }
}

#[cfg(feature = "optimization")]
/// Main parser for WCNF post 22 (without p line) and MCNF
fn parse_no_pline_body<R>(mut reader: R, first_line: &str) -> Result<BodyContent, DimacsError>
where
    R: BufRead,
{
    let mut constrs = SatInstance::new();
    let mut objs = Vec::new();
    let mut buf = first_line.to_string();
    loop {
        let (_, opt_wclause) = parse_mcnf_line(&buf).map_err(unwrap_dimacs_error)?;
        match opt_wclause {
            Some((opt_iw, clause)) => match opt_iw {
                Some((idx, w)) => {
                    if idx > objs.len() {
                        objs.resize(idx, Objective::new());
                    }
                    objs[idx - 1].add_soft_clause(w, clause);
                }
                None => constrs.add_clause(clause),
            },
            None => (),
        };
        buf.clear();
        match reader.read_line(&mut buf) {
            Ok(len) => {
                if len == 0 {
                    return Ok((constrs, objs));
                }
            }
            Err(ioe) => return Err(DimacsError::IOError(ioe)),
        };
    }
}

/// Parses p line and determine file format
fn parse_p_line(input: &str) -> IResult<&str, Preamble, DimacsError> {
    let full_p_line = String::from(input);
    let (input, _) = terminated::<_, _, _, NomError<_>, _, _>(tag("p"), multispace1)(input)
        .map_err(|e| e.map(|_| DimacsError::PLine(full_p_line.clone())))?;
    let (input, id_token) = alt((
        terminated::<_, _, _, NomError<_>, _, _>(tag("cnf"), multispace1),
        #[cfg(feature = "optimization")]
        terminated(tag("wcnf"), multispace1),
    ))(input)
    .map_err(|e| e.map(|_| DimacsError::PLine(full_p_line.clone())))?;
    if id_token == "cnf" {
        // Is CNF file
        let (input, (n_vars, _, n_clauses)) =
            tuple::<_, _, NomError<_>, _>((u64, multispace1, u64))(input)
                .map_err(|e| e.map(|_| DimacsError::PLine(full_p_line)))?;
        // Safe cast to usize
        let n_vars = match usize::try_from(n_vars) {
            Ok(v) => v,
            Err(_) => return Err(nom::Err::Error(DimacsError::PValTooLarge(n_vars))),
        };
        let n_clauses = match usize::try_from(n_clauses) {
            Ok(v) => v,
            Err(_) => return Err(nom::Err::Error(DimacsError::PValTooLarge(n_clauses))),
        };
        return Ok((input, Preamble::Cnf { n_vars, n_clauses }));
    }
    #[cfg(feature = "optimization")]
    if id_token == "wcnf" {
        // Is WCNF file
        let (input, (n_vars, _, n_clauses, _, top)) =
            tuple::<_, _, NomError<_>, _>((u64, multispace1, u64, multispace1, u64))(input)
                .map_err(|e| e.map(|_| DimacsError::PLine(full_p_line)))?;
        // Safe cast to usize
        let n_vars = match usize::try_from(n_vars) {
            Ok(v) => v,
            Err(_) => return Err(nom::Err::Error(DimacsError::PValTooLarge(n_vars))),
        };
        let n_clauses = match usize::try_from(n_clauses) {
            Ok(v) => v,
            Err(_) => return Err(nom::Err::Error(DimacsError::PValTooLarge(n_clauses))),
        };
        return Ok((
            input,
            Preamble::WcnfPre22 {
                n_vars,
                n_clauses,
                top: top.try_into().unwrap(),
            },
        ));
    }
    Err(nom::Err::Error(DimacsError::PLine(full_p_line)))
}

/// Parses a CNF line, either a comment or a clause
fn parse_cnf_line(input: &str) -> IResult<&str, Option<Clause>, DimacsError> {
    let (input, _) = multispace0(input)?;
    match tag::<&str, &str, Error<&str>>("c")(input) {
        Ok((input, _)) => Ok((input, None)),
        Err(_) => {
            // Line is not a comment
            let (input, clause) =
                terminated(separated_list0(multispace1, parse_lit), parse_clause_ending)(input)?;
            Ok((input, Some(Clause::from(clause.into_iter()))))
        }
    }
}

#[cfg(feature = "optimization")]
/// Parses a WCNF pre 22 line, either a comment or a clause
fn parse_wcnf_pre22_line(input: &str) -> IResult<&str, Option<(usize, Clause)>, DimacsError> {
    let (input, _) = multispace0(input)?;
    match tag::<&str, &str, Error<&str>>("c")(input) {
        Ok((input, _)) => Ok((input, None)),
        Err(_) => {
            // Line is not a comment
            let (input, (weight, opt_clause)) =
                separated_pair(parse_weight, multispace1, parse_cnf_line)(input)?;
            match opt_clause {
                Some(clause) => Ok((input, Some((weight, clause)))),
                None => Err(nom::Err::Error(DimacsError::CommentInClause(String::from(
                    input,
                )))),
            }
        }
    }
}

#[cfg(feature = "optimization")]
type McnfLine = Option<(Option<(usize, usize)>, Clause)>;

#[cfg(feature = "optimization")]
/// Parses a MCNF or WCNF post 22 line, either a comment or a clause with
/// objective index. If a line does not explicitly specify an objective index,
/// it is assumed to be 1. This enables for also parsing mcnf lines.
fn parse_mcnf_line(input: &str) -> IResult<&str, McnfLine, DimacsError> {
    let (input, _) = multispace0(input)?;
    match tag::<&str, &str, Error<&str>>("c")(input) {
        Ok((input, _)) => Ok((input, None)),
        Err(_) =>
        // Line is not a comment
        {
            match terminated(tag::<&str, &str, Error<&str>>("h"), multispace1)(input) {
                Ok((input, _)) => {
                    // Hard clause
                    let (input, opt_clause) = parse_cnf_line(input)?;
                    match opt_clause {
                        Some(clause) => Ok((input, Some((None, clause)))),
                        None => Err(nom::Err::Error(DimacsError::CommentInClause(String::from(
                            input,
                        )))),
                    }
                }
                Err(_) => {
                    // Soft clause
                    match tag::<&str, &str, Error<&str>>("o")(input) {
                        Ok((input, _)) => {
                            // MCNF soft (explicit obj index)
                            let (input, (idx, _, weight, _, opt_clause)) =
                                tuple((
                                    parse_idx,
                                    multispace1,
                                    parse_weight,
                                    multispace1,
                                    parse_cnf_line,
                                ))(input)?;
                            match opt_clause {
                                Some(clause) => Ok((input, Some((Some((idx, weight)), clause)))),
                                None => Err(nom::Err::Error(DimacsError::CommentInClause(
                                    String::from(input),
                                ))),
                            }
                        }
                        Err(_) => {
                            // WCNF soft (implicit obj index of 1)
                            let (input, (weight, opt_clause)) =
                                separated_pair(parse_weight, multispace1, parse_cnf_line)(input)?;
                            match opt_clause {
                                Some(clause) => Ok((input, Some((Some((1, weight)), clause)))),
                                None => Err(nom::Err::Error(DimacsError::CommentInClause(
                                    String::from(input),
                                ))),
                            }
                        }
                    }
                }
            }
        }
    }
}

#[cfg(feature = "optimization")]
/// Nuclear parser for weight value
fn parse_weight(input: &str) -> IResult<&str, usize, DimacsError> {
    map_res(u64, |w| w.try_into())(input)
        .map_err(|e| e.map(|e: NomError<&str>| DimacsError::Weight(String::from(e.input))))
}

#[cfg(feature = "optimization")]
/// Nuclear parser for objective index
fn parse_idx(input: &str) -> IResult<&str, usize, DimacsError> {
    map_res(u64, |w| {
        if w == 0 {
            return Err(());
        }
        w.try_into().map_err(|_| ())
    })(input)
    .map_err(|e| e.map(|e: NomError<&str>| DimacsError::ObjIdx(String::from(e.input))))
}

/// Nuclear parser for literal
fn parse_lit(input: &str) -> IResult<&str, Lit, DimacsError> {
    map_res(i32, Lit::from_ipasir)(input)
        .map_err(|e| e.map(|e: NomError<&str>| DimacsError::Lit(String::from(e.input))))
}

/// Parses the end of a clause
/// A '0' followed by a linebreak, as well as a '0' followed by
/// whitespace or only a linebreak are treated as valid clause endings.
/// This is more lean than the file format spec.
fn parse_clause_ending(input: &str) -> IResult<&str, &str, DimacsError> {
    recognize(pair(
        multispace0,
        alt((
            recognize(all_consuming(success(""))),
            recognize(all_consuming(tag("0"))),
            recognize(terminated(tag("0"), line_ending)),
            recognize(terminated(tag("0"), multispace1)),
            recognize(line_ending),
        )),
    ))(input)
    .map_err(|e| e.map(|e: NomError<&str>| DimacsError::ClauseEnding(String::from(e.input))))
}

/// Writes a CNF to a DIMACS CNF file
pub fn write_cnf<W: Write>(writer: &mut W, cnf: CNF, max_var: Var) -> Result<(), io::Error> {
    writeln!(writer, "c CNF file written by RustSAT")?;
    writeln!(
        writer,
        "p cnf {} {}",
        max_var.pos_lit().to_ipasir(),
        cnf.n_clauses()
    )?;
    cnf.into_iter()
        .try_for_each(|cl| write_clause(writer, cl))?;
    writer.flush()
}

#[cfg(feature = "optimization")]
/// Writes a CNF and soft clauses to a (post 22, no p line) DIMACS WCNF file
pub fn write_wcnf<W: Write>(
    writer: &mut W,
    cnf: CNF,
    soft_cls: RsHashMap<Clause, usize>,
    max_var: Option<Var>,
) -> Result<(), io::Error> {
    writeln!(writer, "c WCNF file written by RustSAT")?;
    if let Some(mv) = max_var {
        writeln!(writer, "c highest var: {}", mv.pos_lit().to_ipasir())?;
    }
    writeln!(writer, "c {} hard clauses", cnf.n_clauses())?;
    writeln!(writer, "c {} soft clauses", soft_cls.len())?;
    cnf.into_iter().try_for_each(|cl| {
        write!(writer, "h ")?;
        write_clause(writer, cl)
    })?;
    soft_cls.into_iter().try_for_each(|(cl, w)| {
        write!(writer, "{} ", w)?;
        write_clause(writer, cl)
    })?;
    writer.flush()
}

#[cfg(feature = "multiopt")]
/// Writes a CNF and multiple objectives as sets of soft clauses to a DIMACS MCNF file
pub fn write_mcnf<W: Write>(
    writer: &mut W,
    cnf: CNF,
    soft_cls: Vec<RsHashMap<Clause, usize>>,
    max_var: Option<Var>,
) -> Result<(), io::Error> {
    writeln!(writer, "c MCNF file written by RustSAT")?;
    if let Some(mv) = max_var {
        writeln!(writer, "c highest var: {}", mv.pos_lit().to_ipasir())?;
    }
    writeln!(writer, "c {} hard clauses", cnf.n_clauses())?;
    writeln!(writer, "c {} objectives", soft_cls.len())?;
    write!(writer, "c ( ")?;
    soft_cls
        .iter()
        .try_for_each(|sc| write!(writer, "{} ", sc.len()))?;
    writeln!(writer, ") soft clauses")?;
    cnf.into_iter().try_for_each(|cl| {
        write!(writer, "h ")?;
        write_clause(writer, cl)
    })?;
    soft_cls
        .into_iter()
        .enumerate()
        .try_for_each(|(idx, sft_cls)| {
            sft_cls.into_iter().try_for_each(|(cl, w)| {
                write!(writer, "o{} {} ", idx + 1, w)?;
                write_clause(writer, cl)
            })
        })?;
    writer.flush()
}

fn write_clause<W: Write>(writer: &mut W, clause: Clause) -> Result<(), io::Error> {
    clause
        .into_iter()
        .try_for_each(|l| write!(writer, "{} ", l.to_ipasir()))?;
    writeln!(writer, "0")
}

#[cfg(test)]
mod tests {
    use super::{
        parse_clause_ending, parse_cnf_line, parse_dimacs, parse_lit, parse_p_line, write_cnf,
        Preamble,
    };
    use crate::{
        clause,
        instances::{
            dimacs::{parse_cnf_body, parse_preamble},
            DimacsError, SatInstance, CNF,
        },
        ipasir_lit,
        types::{Clause, Lit, Var},
        var,
    };
    use std::io::{Cursor, Seek};

    #[cfg(feature = "optimization")]
    use super::{
        parse_idx, parse_mcnf_line, parse_no_pline_body, parse_wcnf_pre22_body,
        parse_wcnf_pre22_line, parse_weight, write_wcnf,
    };
    #[cfg(feature = "optimization")]
    use super::{Objective, OptInstance};

    #[cfg(feature = "multiopt")]
    use super::{write_mcnf, MultiOptInstance};

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_idx_pass() {
        assert_eq!(parse_idx("15 "), Ok((" ", 15)));
        assert_eq!(parse_idx("42 63"), Ok((" 63", 42)));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_idx_fail() {
        assert_eq!(
            parse_idx("0 "),
            Err(nom::Err::Error(DimacsError::ObjIdx(String::from("0 "))))
        );
        assert_eq!(
            parse_idx("-15 "),
            Err(nom::Err::Error(DimacsError::ObjIdx(String::from("-15 "))))
        );
        assert_eq!(
            parse_idx("abc "),
            Err(nom::Err::Error(DimacsError::ObjIdx(String::from("abc "))))
        );
        assert_eq!(
            parse_idx(" abc "),
            Err(nom::Err::Error(DimacsError::ObjIdx(String::from(" abc "))))
        );
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_weight_pass() {
        assert_eq!(parse_weight("15 "), Ok((" ", 15)));
        assert_eq!(parse_weight("42 63"), Ok((" 63", 42)));
        assert_eq!(parse_weight("0 "), Ok((" ", 0)));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_weight_fail() {
        assert_eq!(
            parse_weight("-2 "),
            Err(nom::Err::Error(DimacsError::Weight(String::from("-2 "))))
        );
        assert_eq!(
            parse_weight("abc "),
            Err(nom::Err::Error(DimacsError::Weight(String::from("abc "))))
        );
        assert_eq!(
            parse_weight(" abc "),
            Err(nom::Err::Error(DimacsError::Weight(String::from(" abc "))))
        );
    }

    #[test]
    fn parse_lit_pass() {
        assert_eq!(parse_lit("15 "), Ok((" ", ipasir_lit![15])));
        assert_eq!(parse_lit("14 "), Ok((" ", ipasir_lit![14])));
        assert_eq!(parse_lit("-42 "), Ok((" ", ipasir_lit![-42])));
        assert_eq!(parse_lit("42 63"), Ok((" 63", ipasir_lit![42])));
    }

    #[test]
    fn parse_lit_fail() {
        assert_eq!(
            parse_lit("abc "),
            Err(nom::Err::Error(DimacsError::Lit(String::from("abc "))))
        );
        assert_eq!(
            parse_lit(" abc "),
            Err(nom::Err::Error(DimacsError::Lit(String::from(" abc "))))
        );
    }

    #[test]
    fn parse_p_line_pass() {
        assert_eq!(
            parse_p_line("p cnf 23 42"),
            Ok((
                "",
                Preamble::Cnf {
                    n_vars: 23,
                    n_clauses: 42
                }
            ))
        );
        #[cfg(feature = "optimization")]
        assert_eq!(
            parse_p_line("p wcnf 23 42 52"),
            Ok((
                "",
                Preamble::WcnfPre22 {
                    n_vars: 23,
                    n_clauses: 42,
                    top: 52
                }
            ))
        );
    }

    #[test]
    fn parse_p_line_fail() {
        assert_eq!(
            parse_p_line("a cnf 23 42"),
            Err(nom::Err::Error(DimacsError::PLine(String::from(
                "a cnf 23 42"
            ))))
        );
        assert_eq!(
            parse_p_line("p abc 23 42 52"),
            Err(nom::Err::Error(DimacsError::PLine(String::from(
                "p abc 23 42 52"
            ))))
        );
        assert_eq!(
            parse_p_line("p cnf ab"),
            Err(nom::Err::Error(DimacsError::PLine(String::from(
                "p cnf ab"
            ))))
        );
        assert_eq!(
            parse_p_line("p wcnf ab"),
            Err(nom::Err::Error(DimacsError::PLine(String::from(
                "p wcnf ab"
            ))))
        );
    }

    #[test]
    fn parse_clause_ending_pass() {
        assert_eq!(parse_clause_ending("0"), Ok(("", "0")));
        assert_eq!(parse_clause_ending("0 test"), Ok(("test", "0 ")));
        assert_eq!(parse_clause_ending("0\n"), Ok(("", "0\n")));
        assert_eq!(parse_clause_ending("\n"), Ok(("", "\n")));
    }

    #[test]
    fn parse_clause_ending_fail() {
        assert_eq!(
            parse_clause_ending("test"),
            Err(nom::Err::Error(DimacsError::ClauseEnding(String::from(
                "test"
            ))))
        );
        assert_eq!(
            parse_clause_ending("0test"),
            Err(nom::Err::Error(DimacsError::ClauseEnding(String::from(
                "0test"
            ))))
        );
    }

    #[test]
    fn parse_cnf_line_pass() {
        assert_eq!(parse_cnf_line("c test"), Ok((" test", None)));
        assert_eq!(
            parse_cnf_line("42 34 -16 0"),
            Ok((
                "",
                Some(clause![ipasir_lit![42], ipasir_lit![34], ipasir_lit![-16]])
            ))
        );
        assert_eq!(
            parse_cnf_line("42 34 0 -16 0"),
            Ok(("-16 0", Some(clause![ipasir_lit![42], ipasir_lit![34]])))
        );
        assert_eq!(
            parse_cnf_line(" 42 34"),
            Ok(("", Some(clause![ipasir_lit![42], ipasir_lit![34]])))
        );
    }

    #[test]
    fn parse_cnf_line_fail() {
        assert_eq!(
            parse_cnf_line("42 34 a -16 0"),
            Err(nom::Err::Error(DimacsError::ClauseEnding(String::from(
                "a -16 0"
            ))))
        );
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_pre22_line_pass() {
        assert_eq!(parse_wcnf_pre22_line("c test"), Ok((" test", None)));
        assert_eq!(
            parse_wcnf_pre22_line("42 34 -16 0"),
            Ok(("", Some((42, clause![ipasir_lit![34], ipasir_lit![-16]]))))
        );
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_post22_line_pass() {
        assert_eq!(parse_mcnf_line("c test"), Ok((" test", None)));
        assert_eq!(
            parse_mcnf_line("42 34 -16 0"),
            Ok((
                "",
                Some((Some((1, 42)), clause![ipasir_lit![34], ipasir_lit![-16]]))
            ))
        );
        assert_eq!(
            parse_mcnf_line("h 42 34 -16 0"),
            Ok((
                "",
                Some((
                    None,
                    clause![ipasir_lit![42], ipasir_lit![34], ipasir_lit![-16]]
                ))
            ))
        );
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf_line_pass() {
        assert_eq!(parse_mcnf_line("c test"), Ok((" test", None)));
        assert_eq!(
            parse_mcnf_line("o42 34 -16 0"),
            Ok(("", Some((Some((42, 34)), clause![ipasir_lit![-16]]))))
        );
        assert_eq!(
            parse_mcnf_line("h 42 34 -16 0"),
            Ok((
                "",
                Some((
                    None,
                    clause![ipasir_lit![42], ipasir_lit![34], ipasir_lit![-16]]
                ))
            ))
        );
    }

    #[test]
    fn parse_cnf_preamble() {
        let data = "c test\np cnf 5 2\n1 2 0";
        let reader = Cursor::new(data);

        let (_, preamble) = parse_preamble(reader).unwrap();

        assert_eq!(
            preamble,
            Preamble::Cnf {
                n_vars: 5,
                n_clauses: 2,
            }
        );
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_pre22_preamble() {
        let data = "c test\np wcnf 5 2 10\n1 2 0";
        let reader = Cursor::new(data);

        let (_, preamble) = parse_preamble(reader).unwrap();

        assert_eq!(
            preamble,
            Preamble::WcnfPre22 {
                n_vars: 5,
                n_clauses: 2,
                top: 10,
            }
        );
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_post22_preamble() {
        let data = "c test\nh 5 2 0\n1 2 0";
        let reader = Cursor::new(data);

        let (_, preamble) = parse_preamble(reader).unwrap();

        assert_eq!(
            preamble,
            Preamble::NoPLine {
                first_line: String::from("h 5 2 0\n"),
            }
        );
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf_preamble() {
        let data = "c test\no1 2 0\nh 5 2 0";
        let reader = Cursor::new(data);

        let (_, preamble) = parse_preamble(reader).unwrap();

        assert_eq!(
            preamble,
            Preamble::NoPLine {
                first_line: String::from("o1 2 0\n")
            }
        );
    }

    #[test]
    fn parse_cnf_body_pass() {
        let data = "1 2 0\n-3 4 5 0\n";
        let reader = Cursor::new(data);

        let parsed_inst = parse_cnf_body(reader).unwrap();

        let mut true_inst = SatInstance::new();
        true_inst.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_inst.add_clause(clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        #[cfg(not(feature = "optimization"))]
        assert_eq!(parsed_inst, true_inst);
        #[cfg(feature = "optimization")]
        assert_eq!(parsed_inst, (true_inst, vec![]));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_pre22_body_pass() {
        let data = "42 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);

        let parsed_inst = parse_wcnf_pre22_body(reader, 42).unwrap();

        let mut true_constrs = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj]));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_post22_body_pass() {
        let data = "h 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);

        let parsed_inst = parse_no_pline_body(reader, "c test").unwrap();

        let mut true_constrs = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj]));
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf_body_pass() {
        let data = "h 1 2 0\no2 10 -3 4 5 0\n";
        let reader = Cursor::new(data);

        let parsed_inst = parse_no_pline_body(reader, "c test\n").unwrap();

        let mut true_constrs = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(
            parsed_inst,
            (true_constrs, vec![Objective::new(), true_obj])
        );
    }

    #[test]
    fn parse_cnf() {
        let data = "p cnf 5 2\n1 2 0\n-3 4 5 0\n";
        let reader = Cursor::new(data);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut true_inst = SatInstance::new();
        true_inst.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_inst.add_clause(clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        #[cfg(not(feature = "optimization"))]
        assert_eq!(parsed_inst, true_inst);
        #[cfg(feature = "optimization")]
        assert_eq!(parsed_inst, (true_inst, vec![]));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_pre22() {
        let data = "p wcnf 5 2 42\n42 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut true_constrs = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj]));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_post22() {
        let data = "h 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut true_constrs = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj]));
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf() {
        let data = "c test\nh 1 2 0\no2 10 -3 4 5 0\no1 3 -1 0\n";
        let reader = Cursor::new(data);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut true_constrs = SatInstance::new();
        let mut true_obj0 = Objective::new();
        let mut true_obj1 = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj0.add_soft_clause(3, clause![ipasir_lit![-1]]);
        true_obj1.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj0, true_obj1]));
    }

    #[test]
    fn write_parse_cnf() {
        let mut true_cnf = CNF::new();
        true_cnf.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_cnf.add_clause(clause![ipasir_lit![2], ipasir_lit![1]]);

        let mut cursor = Cursor::new(vec![]);

        write_cnf(&mut cursor, true_cnf.clone(), var![1]).unwrap();

        cursor.rewind().unwrap();

        let parsed_inst = super::parse_cnf(cursor).unwrap();
        let (parsed_cnf, _) = parsed_inst.as_cnf();

        assert_eq!(parsed_cnf, true_cnf);
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn write_parse_wcnf() {
        let mut true_constrs: SatInstance = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        let mut cursor = Cursor::new(vec![]);

        write_wcnf(
            &mut cursor,
            true_constrs.clone().as_cnf().0,
            true_obj.clone().as_soft_cls(),
            Some(var![1]),
        )
        .unwrap();

        cursor.rewind().unwrap();

        let parsed_inst = super::parse_wcnf_with_idx(cursor, 0).unwrap();

        assert_eq!(parsed_inst, OptInstance::compose(true_constrs, true_obj));
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn write_parse_mcnf() {
        let mut true_constrs = SatInstance::new();
        let mut true_obj0 = Objective::new();
        let mut true_obj1 = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj0.add_soft_clause(3, clause![ipasir_lit![-1]]);
        true_obj1.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        let mut cursor = Cursor::new(vec![]);

        write_mcnf(
            &mut cursor,
            true_constrs.clone().as_cnf().0,
            vec![
                true_obj0.clone().as_soft_cls(),
                true_obj1.clone().as_soft_cls(),
            ],
            Some(var![4]),
        )
        .unwrap();

        cursor.rewind().unwrap();

        let parsed_inst = super::parse_mcnf(cursor).unwrap();

        assert_eq!(
            parsed_inst,
            MultiOptInstance::compose(true_constrs, vec![true_obj0, true_obj1])
        );
    }
}
