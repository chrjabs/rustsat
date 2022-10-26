//! # Parsing DIMACS Files
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

use super::SatInstance;
use crate::types::{Clause, Lit};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{i32, line_ending, multispace0, multispace1, u64},
    combinator::{all_consuming, map_res, recognize, success},
    error::{Error, ErrorKind},
    multi::separated_list0,
    sequence::{pair, terminated, tuple},
    IResult,
};
use std::{
    convert::TryFrom,
    fmt,
    io::{BufRead, BufReader, Read},
};

#[cfg(feature = "optimization")]
use super::OptInstance;
#[cfg(feature = "multiopt")]
use super::{MultiOptInstance, Objective};
#[cfg(feature = "optimization")]
use nom::sequence::separated_pair;

/// Parses a CNF instance from a reader (typically a (compressed) file)
pub fn parse_cnf<R: Read>(reader: R) -> Result<SatInstance, DimacsError> {
    let reader = BufReader::new(reader);
    match parse_dimacs(reader)? {
        DimacsInstance::CNF(inst) => Ok(inst),
        _ => Err(DimacsError::InvalidInstanceType),
    }
}

#[cfg(feature = "optimization")]
/// Parses a WCNF instance (old or new format) from a reader (typically a (compressed) file)
pub fn parse_wcnf<R: Read>(reader: R) -> Result<OptInstance, DimacsError> {
    let reader = BufReader::new(reader);
    match parse_dimacs(reader)? {
        DimacsInstance::WCNF(inst) => Ok(inst),
        _ => Err(DimacsError::InvalidInstanceType),
    }
}

#[cfg(feature = "multiopt")]
/// Parses a MCNF instance (old or new format) from a reader (typically a (compressed) file)
pub fn parse_mcnf<R: Read>(reader: R) -> Result<MultiOptInstance, DimacsError> {
    let reader = BufReader::new(reader);
    match parse_dimacs(reader)? {
        DimacsInstance::MCNF(inst) => Ok(inst),
        _ => Err(DimacsError::InvalidInstanceType),
    }
}

/// Errors occuring within the DIMACS parsing module
#[derive(Debug)]
pub enum DimacsError {
    /// Encountered invalid preamble
    InvalidPreamble,
    /// Encountered invalid CNF
    InvalidCNF,
    #[cfg(feature = "optimization")]
    /// Encountered invalid WCNF
    InvalidWCNF,
    #[cfg(feature = "multiopt")]
    /// Encountered invalid MCNF
    InvalidMCNF,
    /// Expected different instance type
    InvalidInstanceType,
}

impl fmt::Display for DimacsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DimacsError::InvalidPreamble => write!(f, "Encountered invalid preamble"),
            DimacsError::InvalidCNF => write!(f, "Encountered invalid CNF"),
            #[cfg(feature = "optimization")]
            DimacsError::InvalidWCNF => write!(f, "Encountered invalid WCNF"),
            #[cfg(feature = "multiopt")]
            DimacsError::InvalidMCNF => write!(f, "Encountered invalid MCNF"),
            DimacsError::InvalidInstanceType => write!(f, "Expected different instance type"),
        }
    }
}

/// Internal type of Dimacs instances
#[derive(Debug, PartialEq)]
enum DimacsInstance {
    CNF(SatInstance),
    #[cfg(feature = "optimization")]
    WCNF(OptInstance),
    #[cfg(feature = "multiopt")]
    MCNF(MultiOptInstance),
}

/// Internal type of possible preambles
#[derive(PartialEq, Debug)]
enum Preamble {
    CNF {
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
    WcnfPost22 {
        first_line: String,
    },
    #[cfg(feature = "multiopt")]
    MCNF,
}

/// Top level parser
fn parse_dimacs<R>(reader: R) -> Result<DimacsInstance, DimacsError>
where
    R: BufRead,
{
    match parse_preamble(reader) {
        Err(_) => Err(DimacsError::InvalidPreamble),
        Ok((reader, preamble)) => match preamble {
            Preamble::CNF {
                n_vars: _,
                n_clauses: _,
            } => match parse_cnf_body(reader) {
                Err(_) => Err(DimacsError::InvalidCNF),
                Ok((_, inst)) => Ok(DimacsInstance::CNF(inst)), // n_vars and n_clauses from preamble are intentionally ignored
            },
            #[cfg(feature = "optimization")]
            Preamble::WcnfPre22 {
                n_vars: _,
                n_clauses: _,
                top,
            } => match parse_wcnf_pre22_body(reader, top) {
                Err(_) => Err(DimacsError::InvalidWCNF),
                Ok((_, inst)) => Ok(DimacsInstance::WCNF(inst)), // n_vars and n_clauses from preamble are intentionally ignored
            },
            #[cfg(feature = "optimization")]
            Preamble::WcnfPost22 { first_line } => {
                match parse_wcnf_post22_body(reader, &first_line) {
                    Err(_) => Err(DimacsError::InvalidWCNF),
                    Ok((_, inst)) => Ok(DimacsInstance::WCNF(inst)),
                }
            }
            #[cfg(feature = "multiopt")]
            Preamble::MCNF => match parse_mcnf_body(reader) {
                Err(_) => Err(DimacsError::InvalidMCNF),
                Ok((_, inst)) => Ok(DimacsInstance::MCNF(inst)),
            },
        },
    }
}

/// Casts a nom error with string input to a nom error with reader input
fn cast_str_error_reader<R: BufRead>(err: nom::Err<Error<&str>>, reader: R) -> nom::Err<Error<R>> {
    match err {
        nom::Err::Incomplete(_) => nom::Err::Failure(Error::new(reader, ErrorKind::Fail)),
        nom::Err::Error(e) => nom::Err::Error(Error::new(reader, e.code)),
        nom::Err::Failure(e) => nom::Err::Failure(Error::new(reader, e.code)),
    }
}

/// Parses preamble and determines type of instance/file format
fn parse_preamble<R: BufRead>(mut reader: R) -> IResult<R, Preamble> {
    loop {
        let mut buf = String::new();
        match reader.read_line(&mut buf) {
            Ok(len) => {
                if len == 0 {
                    return Err(nom::Err::Failure(Error::new(reader, ErrorKind::Fail)));
                }
            }
            Err(_) => return Err(nom::Err::Failure(Error::new(reader, ErrorKind::Fail))),
        };
        if buf.starts_with("c") {
            continue;
        }
        if buf.starts_with("p") {
            return match parse_p_line(&buf) {
                Ok((_, preamb)) => Ok((reader, preamb)),
                Err(err) => Err(cast_str_error_reader(err, reader)),
            };
        }
        #[cfg(feature = "optimization")]
        return Ok((reader, Preamble::WcnfPost22 { first_line: buf }));
        #[cfg(not(feature = "optimization"))]
        return Err(nom::Err::Failure(Error::new(reader, ErrorKind::Tag)));
    }
}

/// Main parser for CNF file
fn parse_cnf_body<R>(mut reader: R) -> IResult<R, SatInstance>
where
    R: BufRead,
{
    let mut inst = SatInstance::new();
    loop {
        let mut buf = String::new();
        match reader.read_line(&mut buf) {
            Ok(len) => {
                if len == 0 {
                    return Ok((reader, inst));
                }
            }
            Err(_) => return Err(nom::Err::Failure(Error::new(reader, ErrorKind::Fail))),
        };
        match parse_cnf_line(&buf) {
            Ok((_, opt_clause)) => match opt_clause {
                None => (),
                Some(clause) => inst.add_clause(clause),
            },
            Err(err) => return Err(cast_str_error_reader(err, reader)),
        };
    }
}

#[cfg(feature = "optimization")]
/// Main parser for WCNF pre 22 (with p line)
fn parse_wcnf_pre22_body<R>(mut reader: R, top: usize) -> IResult<R, OptInstance>
where
    R: BufRead,
{
    let mut inst = OptInstance::new();
    loop {
        let mut buf = String::new();
        match reader.read_line(&mut buf) {
            Ok(len) => {
                if len == 0 {
                    return Ok((reader, inst));
                }
            }
            Err(_) => return Err(nom::Err::Failure(Error::new(reader, ErrorKind::Fail))),
        };
        match parse_wcnf_pre22_line(&buf) {
            Ok((_, opt_wclause)) => match opt_wclause {
                None => (),
                Some((w, clause)) => {
                    if w >= top {
                        inst.get_constraints().add_clause(clause)
                    } else {
                        inst.get_objective().add_soft_clause(w, clause)
                    }
                }
            },
            Err(err) => return Err(cast_str_error_reader(err, reader)),
        };
    }
}

#[cfg(feature = "optimization")]
/// Main parser for WCNF post 22 (without p line)
fn parse_wcnf_post22_body<R>(mut reader: R, first_line: &str) -> IResult<R, OptInstance>
where
    R: BufRead,
{
    let mut inst = OptInstance::new();
    let mut buf = first_line.to_string();
    loop {
        match parse_wcnf_post22_line(&buf) {
            Ok((_, opt_wclause)) => match opt_wclause {
                None => (),
                Some((opt_weight, clause)) => match opt_weight {
                    None => inst.get_constraints().add_clause(clause),
                    Some(w) => inst.get_objective().add_soft_clause(w, clause),
                },
            },
            Err(err) => return Err(cast_str_error_reader(err, reader)),
        };
        buf.clear();
        match reader.read_line(&mut buf) {
            Ok(len) => {
                if len == 0 {
                    return Ok((reader, inst));
                }
            }
            Err(_) => return Err(nom::Err::Failure(Error::new(reader, ErrorKind::Fail))),
        };
    }
}

#[cfg(feature = "multiopt")]
/// Main parser for MCNF
fn parse_mcnf_body<R>(mut reader: R) -> IResult<R, MultiOptInstance>
where
    R: BufRead,
{
    let mut constr = SatInstance::new();
    let mut objs = vec![];
    loop {
        let mut buf = String::new();
        match reader.read_line(&mut buf) {
            Ok(len) => {
                if len == 0 {
                    return Ok((reader, MultiOptInstance::compose(constr, objs)));
                }
            }
            Err(_) => return Err(nom::Err::Failure(Error::new(reader, ErrorKind::Fail))),
        };
        match parse_mcnf_line(&buf) {
            Ok((_, opt_mwclause)) => match opt_mwclause {
                None => (),
                Some((opt_idx_weight, clause)) => match opt_idx_weight {
                    None => constr.add_clause(clause),
                    Some((idx, w)) => {
                        if objs.len() < idx {
                            objs.resize(idx, Objective::new());
                        }
                        objs[idx - 1].add_soft_clause(w, clause);
                    }
                },
            },
            Err(err) => return Err(cast_str_error_reader(err, reader)),
        };
    }
}

/// Parses p line and determine file format
fn parse_p_line(input: &str) -> IResult<&str, Preamble> {
    let (input, _) = terminated(tag("p"), multispace1)(input)?;
    let (input, id_token) = alt((
        terminated(tag("cnf"), multispace1),
        #[cfg(feature = "optimization")]
        terminated(tag("wcnf"), multispace1),
        #[cfg(feature = "multiopt")]
        terminated(tag("mcnf"), multispace0),
    ))(input)?;
    if id_token == "cnf" {
        // Is CNF file
        let (input, (n_vars, _, n_clauses)) = tuple((u64, multispace1, u64))(input)?;
        // Safe cast to usize
        let n_vars = match usize::try_from(n_vars) {
            Ok(v) => v,
            Err(_) => return Err(nom::Err::Error(Error::new(input, ErrorKind::TooLarge))),
        };
        let n_clauses = match usize::try_from(n_clauses) {
            Ok(v) => v,
            Err(_) => return Err(nom::Err::Error(Error::new(input, ErrorKind::TooLarge))),
        };
        return Ok((input, Preamble::CNF { n_vars, n_clauses }));
    }
    #[cfg(feature = "optimization")]
    if id_token == "wcnf" {
        // Is WCNF file
        let (input, (n_vars, _, n_clauses, _, top)) =
            tuple((u64, multispace1, u64, multispace1, u64))(input)?;
        // Safe cast to usize
        let n_vars = match usize::try_from(n_vars) {
            Ok(v) => v,
            Err(_) => return Err(nom::Err::Error(Error::new(input, ErrorKind::TooLarge))),
        };
        let n_clauses = match usize::try_from(n_clauses) {
            Ok(v) => v,
            Err(_) => return Err(nom::Err::Error(Error::new(input, ErrorKind::TooLarge))),
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
    #[cfg(feature = "multiopt")]
    if id_token == "mcnf" {
        // Is MCNF file
        return Ok((input, Preamble::MCNF));
    }
    Err(nom::Err::Error(Error::new(input, ErrorKind::Tag)))
}

/// Parses a CNF line, either a comment or a clause
fn parse_cnf_line(input: &str) -> IResult<&str, Option<Clause>> {
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
fn parse_wcnf_pre22_line(input: &str) -> IResult<&str, Option<(usize, Clause)>> {
    let (input, _) = multispace0(input)?;
    match tag::<&str, &str, Error<&str>>("c")(input) {
        Ok((input, _)) => Ok((input, None)),
        Err(_) => {
            // Line is not a comment
            let (input, (weight, opt_clause)) =
                separated_pair(parse_weight, multispace1, parse_cnf_line)(input)?;
            match opt_clause {
                Some(clause) => Ok((input, Some((weight, clause)))),
                None => Err(nom::Err::Error(Error::new(input, ErrorKind::Digit))),
            }
        }
    }
}

#[cfg(feature = "optimization")]
/// Parses a WCNF post 22 line, either a comment or a clause
fn parse_wcnf_post22_line(input: &str) -> IResult<&str, Option<(Option<usize>, Clause)>> {
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
                        None => Err(nom::Err::Error(Error::new(input, ErrorKind::Digit))),
                    }
                }
                Err(_) => {
                    // Soft clause
                    let (input, (weight, opt_clause)) =
                        separated_pair(parse_weight, multispace1, parse_cnf_line)(input)?;
                    match opt_clause {
                        Some(clause) => Ok((input, Some((Some(weight), clause)))),
                        None => Err(nom::Err::Error(Error::new(input, ErrorKind::Digit))),
                    }
                }
            }
        }
    }
}

#[cfg(feature = "multiopt")]
/// Parses a MCNF line, either a comment or a clause
fn parse_mcnf_line(input: &str) -> IResult<&str, Option<(Option<(usize, usize)>, Clause)>> {
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
                        None => Err(nom::Err::Error(Error::new(input, ErrorKind::Digit))),
                    }
                }
                Err(_) => {
                    // Soft clause
                    let (input, (idx, _, weight, _, opt_clause)) = tuple((
                        parse_idx,
                        multispace1,
                        parse_weight,
                        multispace1,
                        parse_cnf_line,
                    ))(input)?;
                    match opt_clause {
                        Some(clause) => Ok((input, Some((Some((idx, weight)), clause)))),
                        None => Err(nom::Err::Error(Error::new(input, ErrorKind::Digit))),
                    }
                }
            }
        }
    }
}

#[cfg(feature = "optimization")]
/// Nuclear parser for weight value
fn parse_weight(input: &str) -> IResult<&str, usize> {
    let (input, w) = map_res(u64, |w| w.try_into())(input)?;
    if w == 0 {
        Err(nom::Err::Error(Error::new(input, ErrorKind::Satisfy)))
    } else {
        Ok((input, w))
    }
}

#[cfg(feature = "multiopt")]
/// Nuclear parser for objective index
fn parse_idx(input: &str) -> IResult<&str, usize> {
    let (input, idx) = map_res(u64, |idx| idx.try_into())(input)?;
    if idx == 0 {
        Err(nom::Err::Error(Error::new(input, ErrorKind::Satisfy)))
    } else {
        Ok((input, idx))
    }
}

/// Nuclear parser for literal
fn parse_lit(input: &str) -> IResult<&str, Lit> {
    map_res(i32, Lit::from_ipasir)(input)
}

/// Parses the end of a clause
/// A '0' followed by a linebreak, as well as a '0' followed by
/// whitespace or only a linebreak are treated as valid clause endings.
/// This is more lean than the file format spec.
fn parse_clause_ending(input: &str) -> IResult<&str, &str> {
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
}

#[cfg(test)]
mod tests {
    use super::{
        parse_clause_ending, parse_cnf_line, parse_dimacs, parse_lit, parse_p_line, DimacsInstance,
        Preamble,
    };
    use crate::{
        clause,
        instances::{
            dimacs::{parse_cnf_body, parse_preamble},
            SatInstance,
        },
        ipasir_lit,
        types::{Clause, Lit},
    };
    use nom::error::{Error, ErrorKind};
    use std::io::{BufReader, Cursor};

    #[cfg(feature = "optimization")]
    use super::OptInstance;
    #[cfg(feature = "optimization")]
    use super::{
        parse_wcnf_post22_body, parse_wcnf_post22_line, parse_wcnf_pre22_body,
        parse_wcnf_pre22_line, parse_weight,
    };

    #[cfg(feature = "multiopt")]
    use super::MultiOptInstance;
    #[cfg(feature = "multiopt")]
    use super::{parse_idx, parse_mcnf_body, parse_mcnf_line};

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_idx_pass() {
        assert_eq!(parse_idx("15 "), Ok((" ", 15)));
        assert_eq!(parse_idx("42 63"), Ok((" 63", 42)));
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_idx_fail() {
        assert_eq!(
            parse_idx("0 "),
            Err(nom::Err::Error(Error::new(" ", ErrorKind::Satisfy)))
        );
        assert_eq!(
            parse_idx("-15 "),
            Err(nom::Err::Error(Error::new("-15 ", ErrorKind::Digit)))
        );
        assert_eq!(
            parse_idx("abc "),
            Err(nom::Err::Error(Error::new("abc ", ErrorKind::Digit)))
        );
        assert_eq!(
            parse_idx(" abc "),
            Err(nom::Err::Error(Error::new(" abc ", ErrorKind::Digit)))
        );
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_weight_pass() {
        assert_eq!(parse_weight("15 "), Ok((" ", 15)));
        assert_eq!(parse_weight("42 63"), Ok((" 63", 42)));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_weight_fail() {
        assert_eq!(
            parse_weight("0 "),
            Err(nom::Err::Error(Error::new(" ", ErrorKind::Satisfy)))
        );
        assert_eq!(
            parse_weight("-2 "),
            Err(nom::Err::Error(Error::new("-2 ", ErrorKind::Digit)))
        );
        assert_eq!(
            parse_weight("abc "),
            Err(nom::Err::Error(Error::new("abc ", ErrorKind::Digit)))
        );
        assert_eq!(
            parse_weight(" abc "),
            Err(nom::Err::Error(Error::new(" abc ", ErrorKind::Digit)))
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
            Err(nom::Err::Error(Error::new("abc ", ErrorKind::Digit)))
        );
        assert_eq!(
            parse_lit(" abc "),
            Err(nom::Err::Error(Error::new(" abc ", ErrorKind::Digit)))
        );
    }

    #[test]
    fn parse_p_line_pass() {
        assert_eq!(
            parse_p_line("p cnf 23 42"),
            Ok((
                "",
                Preamble::CNF {
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
        #[cfg(feature = "multiopt")]
        assert_eq!(parse_p_line("p mcnf"), Ok(("", Preamble::MCNF)));
    }

    #[test]
    fn parse_p_line_fail() {
        assert_eq!(
            parse_p_line("a cnf 23 42"),
            Err(nom::Err::Error(Error::new("a cnf 23 42", ErrorKind::Tag)))
        );
        assert_eq!(
            parse_p_line("p abc 23 42 52"),
            Err(nom::Err::Error(Error::new("abc 23 42 52", ErrorKind::Tag)))
        );
        assert_eq!(
            parse_p_line("p cnf ab"),
            Err(nom::Err::Error(Error::new("ab", ErrorKind::Digit)))
        );
        #[cfg(feature = "optimization")]
        assert_eq!(
            parse_p_line("p wcnf ab"),
            Err(nom::Err::Error(Error::new("ab", ErrorKind::Digit)))
        );
        #[cfg(not(feature = "optimization"))]
        assert_eq!(
            parse_p_line("p wcnf ab"),
            Err(nom::Err::Error(Error::new("wcnf ab", ErrorKind::Tag)))
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
            Err(nom::Err::Error(Error::new("test", ErrorKind::CrLf)))
        );
        assert_eq!(
            parse_clause_ending("0test"),
            Err(nom::Err::Error(Error::new("0test", ErrorKind::CrLf)))
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
            Err(nom::Err::Error(Error::new("a -16 0", ErrorKind::CrLf)))
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
        assert_eq!(parse_wcnf_post22_line("c test"), Ok((" test", None)));
        assert_eq!(
            parse_wcnf_post22_line("42 34 -16 0"),
            Ok((
                "",
                Some((Some(42), clause![ipasir_lit![34], ipasir_lit![-16]]))
            ))
        );
        assert_eq!(
            parse_wcnf_post22_line("h 42 34 -16 0"),
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
            parse_mcnf_line("42 34 -16 0"),
            Ok(("", Some((Some((42, 34)), clause![ipasir_lit![-16]]))))
        );
        assert_eq!(
            parse_wcnf_post22_line("h 42 34 -16 0"),
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
        let reader = BufReader::new(reader);

        let (_, preamble) = parse_preamble(reader).unwrap();

        assert_eq!(
            preamble,
            Preamble::CNF {
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
        let reader = BufReader::new(reader);

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
        let reader = BufReader::new(reader);

        let (_, preamble) = parse_preamble(reader).unwrap();

        assert_eq!(
            preamble,
            Preamble::WcnfPost22 {
                first_line: String::from("h 5 2 0\n"),
            }
        );
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf_preamble() {
        let data = "c test\np mcnf\nh 5 2 0\n1 2 0";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let (_, preamble) = parse_preamble(reader).unwrap();

        assert_eq!(preamble, Preamble::MCNF);
    }

    #[test]
    fn parse_cnf_body_pass() {
        let data = "1 2 0\n-3 4 5 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let (_, parsed_inst) = parse_cnf_body(reader).unwrap();

        let mut true_inst = SatInstance::new();
        true_inst.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_inst.add_clause(clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, true_inst);
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_pre22_body_pass() {
        let data = "42 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let (_, parsed_inst) = parse_wcnf_pre22_body(reader, 42).unwrap();

        let mut true_inst = OptInstance::new();
        true_inst
            .get_constraints()
            .add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_inst
            .get_objective()
            .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, true_inst);
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_post22_body_pass() {
        let data = "h 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let (_, parsed_inst) = parse_wcnf_post22_body(reader, "c test").unwrap();

        let mut true_inst = OptInstance::new();
        true_inst
            .get_constraints()
            .add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_inst
            .get_objective()
            .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, true_inst);
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf_body_pass() {
        let data = "c test\nh 1 2 0\n2 10 -3 4 5 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let (_, parsed_inst) = parse_mcnf_body(reader).unwrap();

        let mut true_inst = MultiOptInstance::new(2);
        true_inst
            .get_constraints()
            .add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_inst
            .get_objective(1)
            .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, true_inst);
    }

    #[test]
    fn parse_cnf() {
        let data = "p cnf 5 2\n1 2 0\n-3 4 5 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut inst = SatInstance::new();
        inst.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        inst.add_clause(clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        let true_inst = DimacsInstance::CNF(inst);

        assert_eq!(parsed_inst, true_inst);
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_pre22() {
        let data = "p wcnf 5 2 42\n42 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut inst = OptInstance::new();
        inst.get_constraints()
            .add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        inst.get_objective()
            .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        let true_inst = DimacsInstance::WCNF(inst);

        assert_eq!(parsed_inst, true_inst);
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_post22() {
        let data = "h 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut inst = OptInstance::new();
        inst.get_constraints()
            .add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        inst.get_objective()
            .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        let true_inst = DimacsInstance::WCNF(inst);

        assert_eq!(parsed_inst, true_inst);
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf() {
        let data = "c test\np mcnf\nh 1 2 0\n2 10 -3 4 5 0\n1 3 -1 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut inst = MultiOptInstance::new(2);
        inst.get_constraints()
            .add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        inst.get_objective(0)
            .add_soft_clause(3, clause![ipasir_lit![-1]]);
        inst.get_objective(1)
            .add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        let true_inst = DimacsInstance::MCNF(inst);

        assert_eq!(parsed_inst, true_inst);
    }
}
