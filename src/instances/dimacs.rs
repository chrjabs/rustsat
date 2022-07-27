//! # Parsing DIMACS CNF and WCNF Files
//!
//! Internal module containing functions for parsing DIMACS files.
//! The approach is to accept input instances, even if they are not technically
//! in spec, as long as the input is still reasonable.

use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{i32, line_ending, multispace0, multispace1, u64},
    combinator::{all_consuming, map_res, recognize, success},
    error::{Error, ErrorKind},
    multi::separated_list0,
    sequence::{pair, separated_pair, terminated, tuple},
    IResult,
};
use std::{
    convert::TryFrom,
    fmt,
    io::{BufRead, BufReader, Read},
};

use super::{OptInstance, SatInstance};
use crate::types::{Clause, Lit};

/// Parses a CNF instance from a reader (typically a (compressed) file)
pub fn parse_cnf<R: Read>(reader: R) -> Result<SatInstance, DimacsError> {
    let reader = BufReader::new(reader);
    match parse_dimacs(reader)? {
        DimacsInstance::CNF(inst) => Ok(inst),
        _ => Err(DimacsError::InvalidInstanceType),
    }
}

/// Parses a WCNF instance (old or new format) from a reader (typically a (compressed) file)
pub fn parse_wcnf<R: Read>(reader: R) -> Result<OptInstance, DimacsError> {
    let reader = BufReader::new(reader);
    match parse_dimacs(reader)? {
        DimacsInstance::WCNF(inst) => Ok(inst),
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
    /// Encountered invalid WCNF
    InvalidWCNF,
    /// Expected different instance type
    InvalidInstanceType,
}

impl fmt::Display for DimacsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DimacsError::InvalidPreamble => write!(f, "Encountered invalid preamble"),
            DimacsError::InvalidCNF => write!(f, "Encountered invalid CNF"),
            DimacsError::InvalidWCNF => write!(f, "Encountered invalid WCNF"),
            DimacsError::InvalidInstanceType => write!(f, "Expected different instance type"),
        }
    }
}

/// Internal type of Dimacs instances
#[derive(Debug, PartialEq)]
enum DimacsInstance {
    CNF(SatInstance),
    WCNF(OptInstance),
}

/// Internal type of possible preambles
#[derive(PartialEq, Debug)]
enum Preamble {
    CNF {
        n_vars: usize,
        n_clauses: usize,
    },
    WcnfPre22 {
        n_vars: usize,
        n_clauses: usize,
        top: u64,
    },
    WcnfPost22 {
        first_line: String,
    },
}

/// Top level parser
fn parse_dimacs<R: BufRead>(reader: R) -> Result<DimacsInstance, DimacsError> {
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
            Preamble::WcnfPre22 {
                n_vars: _,
                n_clauses: _,
                top,
            } => match parse_wcnf_pre22_body(reader, top) {
                Err(_) => Err(DimacsError::InvalidWCNF),
                Ok((_, inst)) => Ok(DimacsInstance::WCNF(inst)), // n_vars and n_clauses from preamble are intentionally ignored
            },
            Preamble::WcnfPost22 { first_line } => match parse_wcnf_post22_body(reader, &first_line)
            {
                Err(_) => Err(DimacsError::InvalidWCNF),
                Ok((_, inst)) => Ok(DimacsInstance::WCNF(inst)),
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
        return Ok((reader, Preamble::WcnfPost22 { first_line: buf }));
    }
}

/// Main parser for CNF file
fn parse_cnf_body<R: BufRead>(mut reader: R) -> IResult<R, SatInstance> {
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

/// Main parser for WCNF pre 22 (with p line)
fn parse_wcnf_pre22_body<R: BufRead>(mut reader: R, top: u64) -> IResult<R, OptInstance> {
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
                        inst.add_soft_clause(w, clause)
                    }
                }
            },
            Err(err) => return Err(cast_str_error_reader(err, reader)),
        };
    }
}

/// Main parser for WCNF post 22 (without p line)
fn parse_wcnf_post22_body<R: BufRead>(mut reader: R, first_line: &str) -> IResult<R, OptInstance> {
    let mut inst = OptInstance::new();
    let mut buf = first_line.to_string();
    loop {
        match parse_wcnf_post22_line(&buf) {
            Ok((_, opt_wclause)) => match opt_wclause {
                None => (),
                Some((opt_weight, clause)) => match opt_weight {
                    None => inst.get_constraints().add_clause(clause),
                    Some(w) => inst.add_soft_clause(w, clause),
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

/// Parses p line and determine file format
fn parse_p_line(input: &str) -> IResult<&str, Preamble> {
    let (input, _) = terminated(tag("p"), multispace1)(input)?;
    match terminated(tag::<&str, &str, Error<&str>>("cnf"), multispace1)(input) {
        Err(_) => {
            // Is WCNF file
            let (input, _) = terminated(tag("wcnf"), multispace1)(input)?;
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
            Ok((
                input,
                Preamble::WcnfPre22 {
                    n_vars,
                    n_clauses,
                    top,
                },
            ))
        }
        Ok((input, _)) => {
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
            Ok((input, Preamble::CNF { n_vars, n_clauses }))
        }
    }
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

/// Parses a WCNF pre 22 line, either a comment or a clause
fn parse_wcnf_pre22_line(input: &str) -> IResult<&str, Option<(u64, Clause)>> {
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

/// Parses a WCNF post 22 line, either a comment or a clause
fn parse_wcnf_post22_line(input: &str) -> IResult<&str, Option<(Option<u64>, Clause)>> {
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

/// Nuclear parser for weight value
fn parse_weight(input: &str) -> IResult<&str, u64> {
    u64(input)
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
        parse_clause_ending, parse_cnf_line, parse_dimacs, parse_lit, parse_p_line,
        parse_wcnf_post22_body, parse_wcnf_post22_line, parse_wcnf_pre22_body,
        parse_wcnf_pre22_line, parse_weight, DimacsInstance, Preamble,
    };
    use crate::{
        clause,
        instances::{
            dimacs::{parse_cnf_body, parse_preamble},
            OptInstance, SatInstance,
        },
        ipasir_lit,
        types::{Clause, Lit},
    };
    use nom::error::{Error, ErrorKind};
    use std::io::{BufReader, Cursor};

    #[test]
    fn parse_weight_pass() {
        assert_eq!(parse_weight("15 "), Ok((" ", 15)));
        assert_eq!(parse_weight("42 63"), Ok((" 63", 42)));
    }

    #[test]
    fn parse_weight_fail() {
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
        assert_eq!(
            parse_p_line("p wcnf ab"),
            Err(nom::Err::Error(Error::new("ab", ErrorKind::Digit)))
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

    #[test]
    fn parse_wcnf_pre22_line_pass() {
        assert_eq!(parse_cnf_line("c test"), Ok((" test", None)));
        assert_eq!(
            parse_wcnf_pre22_line("42 34 -16 0"),
            Ok(("", Some((42, clause![ipasir_lit![34], ipasir_lit![-16]]))))
        );
    }

    #[test]
    fn parse_wcnf_post22_line_pass() {
        assert_eq!(parse_cnf_line("c test"), Ok((" test", None)));
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
        true_inst.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, true_inst);
    }

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
        true_inst.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

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

    #[test]
    fn parse_wcnf_pre22() {
        let data = "p wcnf 5 2 42\n42 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut inst = OptInstance::new();
        inst
            .get_constraints()
            .add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        inst.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        let true_inst = DimacsInstance::WCNF(inst);

        assert_eq!(parsed_inst, true_inst);
    }

    #[test]
    fn parse_wcnf_post22() {
        let data = "h 1 2 0\n10 -3 4 5 0\n";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);

        let parsed_inst = parse_dimacs(reader).unwrap();

        let mut inst = OptInstance::new();
        inst
            .get_constraints()
            .add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        inst.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        let true_inst = DimacsInstance::WCNF(inst);

        assert_eq!(parsed_inst, true_inst);
    }
}
