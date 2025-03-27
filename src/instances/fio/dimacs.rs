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

use crate::{
    instances::{Cnf, ManageVars, SatInstance},
    types::{Cl, Clause, Lit, Var},
};
use anyhow::Context;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{i32, line_ending, multispace0, multispace1, u32, u64},
    combinator::{all_consuming, map, map_res, recognize, success},
    error::{context, Error as NomError},
    multi::separated_list0,
    sequence::{pair, terminated, tuple},
    IResult,
};
use std::{
    convert::TryFrom,
    io::{self, BufRead, Write},
};
use thiserror::Error;

#[cfg(feature = "multiopt")]
use crate::instances::MultiOptInstance;
#[cfg(feature = "optimization")]
use crate::instances::{Objective, OptInstance};
#[cfg(feature = "optimization")]
use crate::types::WClsIter;
#[cfg(feature = "optimization")]
use nom::sequence::separated_pair;

#[cfg(feature = "optimization")]
type BodyContent<VM> = (SatInstance<VM>, Vec<Objective>);
#[cfg(not(feature = "optimization"))]
type BodyContent<VM> = SatInstance<VM>;

/// An error for when an invalid p line is encountered
#[derive(Error, Debug, PartialEq, Eq, Clone)]
#[error("invalid p line '{0}'")]
pub struct InvalidPLine(String);

/// Parses a CNF instance from a reader (typically a (compressed) file)
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
pub fn parse_cnf<R, VM>(reader: &mut R) -> anyhow::Result<SatInstance<VM>>
where
    R: BufRead,
    VM: ManageVars + Default,
{
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
/// (compressed) file). The objective with the index `obj_idx` is used.
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
pub fn parse_wcnf_with_idx<R, VM>(reader: &mut R, obj_idx: usize) -> anyhow::Result<OptInstance<VM>>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    use super::ObjNoExist;

    let (constrs, mut objs) = parse_dimacs(reader)?;
    if objs.is_empty() {
        objs.push(Objective::default());
    }
    let objs_len = objs.len();
    if let Some(obj) = objs.into_iter().nth(obj_idx) {
        Ok(OptInstance::compose(constrs, obj))
    } else {
        anyhow::bail!(ObjNoExist(objs_len))
    }
}

#[cfg(feature = "multiopt")]
/// Parses a MCNF instance (old or new format) from a reader (typically a (compressed) file)
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
pub fn parse_mcnf<R, VM>(reader: &mut R) -> anyhow::Result<MultiOptInstance<VM>>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    let (constrs, objs) = parse_dimacs(reader)?;
    Ok(MultiOptInstance::compose(constrs, objs))
}

/// Internal type of possible preambles
#[derive(PartialEq, Debug)]
enum Preamble {
    Cnf {
        n_vars: u32,
        n_clauses: usize,
    },
    #[cfg(feature = "optimization")]
    WcnfPre22 {
        n_vars: u32,
        n_clauses: usize,
        top: usize,
    },
    #[cfg(feature = "optimization")]
    NoPLine {
        first_line: String,
    },
}

/// Top level parser
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
fn parse_dimacs<R, VM>(reader: &mut R) -> anyhow::Result<BodyContent<VM>>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    let preamble = parse_preamble(reader)?;
    let mut vm = VM::default();
    let content = match preamble {
        Preamble::Cnf {
            n_vars,
            n_clauses: _, // Intentionally ignored (lean acceptance)
        } => {
            vm.increase_next_free(Var::new(n_vars));
            parse_cnf_body(reader, vm)
        }
        #[cfg(feature = "optimization")]
        Preamble::WcnfPre22 {
            n_vars,
            n_clauses: _, // Intentionally ignored (lean acceptance)
            top,
        } => {
            vm.increase_next_free(Var::new(n_vars));
            parse_wcnf_pre22_body(reader, top, vm)
        }
        #[cfg(feature = "optimization")]
        Preamble::NoPLine { first_line } => parse_no_pline_body(reader, &first_line, vm),
    }?;
    Ok(content)
}

/// Parses preamble and determines type of instance/file format
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
fn parse_preamble<R: BufRead>(reader: &mut R) -> anyhow::Result<Preamble> {
    let mut buf = String::new();
    while reader.read_line(&mut buf)? > 0 {
        if buf.starts_with('c') || buf.trim().is_empty() {
            buf.clear();
            continue;
        }
        if buf.starts_with('p') {
            let Ok((_, preamble)) = parse_p_line(&buf) else {
                return Err(InvalidPLine(buf).into());
            };
            return Ok(preamble);
        }
        break;
    }
    #[cfg(feature = "optimization")]
    {
        Ok(Preamble::NoPLine { first_line: buf })
    }
    #[cfg(not(feature = "optimization"))]
    {
        Err(InvalidPLine(buf).into())
    }
}

/// Main parser for CNF file
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
fn parse_cnf_body<R, VM>(reader: &mut R, vm: VM) -> anyhow::Result<BodyContent<VM>>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    let mut inst = SatInstance::new_with_manager(vm);
    let mut buf = String::new();
    while reader.read_line(&mut buf)? > 0 {
        let (_, opt_clause) = parse_cnf_line(&buf)
            .map_err(nom::Err::<NomError<&str>>::to_owned)
            .with_context(|| format!("failed to parse cnf line '{buf}'"))?;
        if let Some(clause) = opt_clause {
            inst.add_clause(clause);
        }
        buf.clear();
    }
    #[cfg(feature = "optimization")]
    {
        Ok((inst, vec![]))
    }
    #[cfg(not(feature = "optimization"))]
    {
        Ok(inst)
    }
}

#[cfg(feature = "optimization")]
/// Main parser for WCNF pre-22 (with p line)
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
fn parse_wcnf_pre22_body<R, VM>(
    reader: &mut R,
    top: usize,
    vm: VM,
) -> anyhow::Result<BodyContent<VM>>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    let mut constrs = SatInstance::new_with_manager(vm);
    let mut obj = Objective::new();
    let mut buf = String::new();
    while reader.read_line(&mut buf)? > 0 {
        let (_, opt_wclause) = parse_wcnf_pre22_line(&buf)
            .map_err(nom::Err::<NomError<&str>>::to_owned)
            .with_context(|| format!("failed to parse old wcnf line '{buf}'"))?;
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
        buf.clear();
    }
    Ok((constrs, if obj.is_empty() { vec![] } else { vec![obj] }))
}

#[cfg(feature = "optimization")]
/// Main parser for WCNF post 22 (without p line) and MCNF
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
fn parse_no_pline_body<R, VM>(
    reader: &mut R,
    first_line: &str,
    vm: VM,
) -> anyhow::Result<BodyContent<VM>>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    let mut constrs = SatInstance::new_with_manager(vm);
    let mut objs = Vec::new();
    let mut buf = first_line.to_string();
    loop {
        let (_, opt_wclause) = parse_mcnf_line(&buf)
            .map_err(nom::Err::<NomError<&str>>::to_owned)
            .with_context(|| format!("failed to parse new wcnf/mcnf line '{buf}'"))?;
        if let Some((opt_iw, clause)) = opt_wclause {
            match opt_iw {
                Some((idx, w)) => {
                    if idx > objs.len() {
                        objs.resize(idx, Objective::new());
                    }
                    objs[idx - 1].add_soft_clause(w, clause);
                }
                None => constrs.add_clause(clause),
            }
        };
        buf.clear();
        let len = reader.read_line(&mut buf)?;
        if len == 0 {
            return Ok((constrs, objs));
        }
    }
}

/// Parses p line and determine file format
fn parse_p_line(input: &str) -> IResult<&str, Preamble> {
    let (input, _) = context(
        "p line does not start with 'p'",
        terminated::<_, _, _, NomError<_>, _, _>(tag("p"), multispace1),
    )(input)?;
    let (input, id_token) = context(
        "invalid id token in p line",
        alt((
            terminated::<_, _, _, NomError<_>, _, _>(tag("cnf"), multispace1),
            #[cfg(feature = "optimization")]
            terminated(tag("wcnf"), multispace1),
        )),
    )(input)?;
    //.with_context(|| format!("invalid id token in '{}'", input))?;
    if id_token == "cnf" {
        // Is CNF file
        let (input, (n_vars, _, n_clauses)) = context(
            "failed to parse number of variables and clauses",
            tuple::<_, _, NomError<_>, _>((
                context("number of vars does not fit usize", u32),
                multispace1,
                context(
                    "number of clauses does not fit usize",
                    map_res(u64, usize::try_from),
                ),
            )),
        )(input)?;
        return Ok((input, Preamble::Cnf { n_vars, n_clauses }));
    }
    #[cfg(feature = "optimization")]
    if id_token == "wcnf" {
        // Is WCNF file
        let (input, (n_vars, _, n_clauses, _, top)) = context(
            "failed to parse number of variables, clauses, and top",
            tuple::<_, _, NomError<_>, _>((
                context("number of vars does not fit usize", u32),
                multispace1,
                context(
                    "number of clauses does not fit usize",
                    map_res(u64, usize::try_from),
                ),
                multispace1,
                context("top does not fit usize", map_res(u64, usize::try_from)),
            )),
        )(input)?;
        return Ok((
            input,
            Preamble::WcnfPre22 {
                n_vars,
                n_clauses,
                top,
            },
        ));
    }
    panic!("this should be impossible to reach")
}

/// Parses a CNF line, either a comment or a clause
fn parse_cnf_line(input: &str) -> IResult<&str, Option<Clause>> {
    let (input, _) = multispace0::<_, NomError<_>>(input)?;
    if input.trim().is_empty() {
        // Tolerate empty lines
        return Ok((input, None));
    }
    if let Ok((input, _)) = tag::<&str, &str, NomError<&str>>("c")(input) {
        Ok((input, None))
    } else {
        // Line is not a comment
        let (input, clause) = parse_clause(input)?;
        Ok((input, Some(clause)))
    }
}

#[cfg(feature = "optimization")]
/// Parses a WCNF pre-22 line, either a comment or a clause
fn parse_wcnf_pre22_line(input: &str) -> IResult<&str, Option<(usize, Clause)>> {
    let (input, _) = multispace0::<_, NomError<_>>(input)?;
    if input.trim().is_empty() {
        // Tolerate empty lines
        return Ok((input, None));
    }
    if let Ok((input, _)) = tag::<&str, &str, NomError<&str>>("c")(input) {
        Ok((input, None))
    } else {
        // Line is not a comment
        let (input, (weight, clause)) =
            separated_pair(parse_weight, multispace1, parse_clause)(input)?;
        Ok((input, Some((weight, clause))))
    }
}

#[cfg(feature = "optimization")]
type McnfDataLine = Option<(Option<(usize, usize)>, Clause)>;

#[cfg(feature = "optimization")]
/// Parses a MCNF or WCNF post 22 line, either a comment or a clause with
/// objective index. If a line does not explicitly specify an objective index,
/// it is assumed to be 1. This enables for also parsing MCNF lines.
fn parse_mcnf_line(input: &str) -> IResult<&str, McnfDataLine> {
    let (input, _) = multispace0::<_, NomError<_>>(input)?;
    if input.trim().is_empty() {
        // Tolerate empty lines
        return Ok((input, None));
    }
    match tag::<&str, &str, NomError<&str>>("c")(input) {
        Ok((input, _)) => Ok((input, None)),
        Err(_) =>
        // Line is not a comment
        {
            match terminated(tag::<_, _, NomError<_>>("h"), multispace1)(input) {
                Ok((input, _)) => {
                    // Hard clause
                    let (input, clause) = parse_clause(input)?;
                    Ok((input, Some((None, clause))))
                }
                Err(_) => {
                    // Soft clause
                    if let Ok((input, _)) = tag::<_, _, NomError<_>>("o")(input) {
                        // MCNF soft (explicit obj index)
                        let (input, (idx, _, weight, _, clause)) =
                            tuple((
                                parse_idx,
                                multispace1,
                                parse_weight,
                                multispace1,
                                parse_clause,
                            ))(input)?;
                        Ok((input, Some((Some((idx, weight)), clause))))
                    } else {
                        // WCNF soft (implicit obj index of 1)
                        let (input, (weight, clause)) =
                            separated_pair(parse_weight, multispace1, parse_clause)(input)?;
                        Ok((input, Some((Some((1, weight)), clause))))
                    }
                }
            }
        }
    }
}

/// Nom-like parser for a clause
fn parse_clause(input: &str) -> IResult<&str, Clause> {
    context(
        "failed to parse clause",
        map(
            terminated(separated_list0(multispace1, parse_lit), parse_clause_ending),
            Clause::from_iter,
        ),
    )(input)
}

#[cfg(feature = "optimization")]
/// Nom-like parser for weight value
fn parse_weight(input: &str) -> IResult<&str, usize> {
    context(
        "weight does not fit usize",
        map_res(
            context("expected number for weight", u64),
            TryInto::try_into,
        ),
    )(input)
}

#[cfg(feature = "optimization")]
/// Nom-like parser for objective index
fn parse_idx(input: &str) -> IResult<&str, usize> {
    context(
        "invalid objective index (either 0 or does not fit usize)",
        map_res(context("expected number for objective index", u64), |w| {
            if w == 0 {
                return Err(());
            }
            w.try_into().map_err(|_| ())
        }),
    )(input)
}

/// Nom-like parser for literal
///
/// # Errors
///
/// If parsing fails
#[cfg_attr(feature = "internals", visibility::make(pub))]
fn parse_lit(input: &str) -> IResult<&str, Lit> {
    context("invalid ipasir literal", map_res(i32, Lit::from_ipasir))(input)
}

/// Parses the end of a clause
/// A '0' followed by a line-break, as well as a '0' followed by
/// white-space or only a line-break are treated as valid clause endings.
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

/// Writes a CNF to a DIMACS CNF file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
pub fn write_cnf_annotated<W: Write>(
    writer: &mut W,
    cnf: &Cnf,
    n_vars: u32,
) -> Result<(), io::Error> {
    writeln!(writer, "c CNF file written by RustSAT")?;
    writeln!(writer, "p cnf {n_vars} {}", cnf.len())?;
    cnf.iter().try_for_each(|cl| write_clause(writer, cl))?;
    writer.flush()
}

/// Input data for writing a CNF instance
pub enum CnfLine {
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
            CnfLine::Comment(_) => None,
            CnfLine::Clause(cl) => Some(cl),
        }
    }
}

/// Writes a CNF to a DIMACS CNF file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
pub fn write_cnf<W: Write, Iter: Iterator<Item = CnfLine>>(
    writer: &mut W,
    mut data: Iter,
) -> Result<(), io::Error> {
    data.try_for_each(|dat| match dat {
        CnfLine::Comment(c) => write!(writer, "c {c}"),
        CnfLine::Clause(cl) => write_clause(writer, &cl),
    })
}

#[cfg(feature = "optimization")]
/// Writes a CNF and soft clauses to a (post 22, no p line) DIMACS WCNF file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
pub fn write_wcnf_annotated<W: Write, CI: WClsIter>(
    writer: &mut W,
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
        write_clause(writer, cl)
    })?;
    soft_cls.into_iter().try_for_each(|(cl, w)| {
        write!(writer, "{w} ")?;
        write_clause(writer, &cl)
    })?;
    writer.flush()
}

#[cfg(feature = "optimization")]
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
    writer: &mut W,
    mut data: Iter,
) -> Result<(), io::Error> {
    data.try_for_each(|dat| match dat {
        WcnfLine::Comment(c) => write!(writer, "c {c}"),
        WcnfLine::Hard(cl) => {
            write!(writer, "h ")?;
            write_clause(writer, &cl)
        }
        WcnfLine::Soft(cl, w) => {
            write!(writer, "{w} ")?;
            write_clause(writer, &cl)
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
    writer: &mut W,
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
        write_clause(writer, cl)
    })?;
    soft_cls
        .into_iter()
        .enumerate()
        .try_for_each(|(idx, sft_cls)| {
            sft_cls.into_iter().try_for_each(|(cl, w)| {
                write!(writer, "o{} {} ", idx + 1, w)?;
                write_clause(writer, &cl)
            })
        })?;
    writer.flush()
}

#[cfg(feature = "multiopt")]
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
    writer: &mut W,
    mut data: Iter,
) -> Result<(), io::Error> {
    data.try_for_each(|dat| match dat {
        McnfLine::Comment(c) => writeln!(writer, "c {c}"),
        McnfLine::Hard(cl) => {
            write!(writer, "h ")?;
            write_clause(writer, &cl)
        }
        McnfLine::Soft(cl, w, oidx) => {
            write!(writer, "o{} {} ", oidx + 1, w)?;
            write_clause(writer, &cl)
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
    use super::{
        parse_clause_ending, parse_cnf_body, parse_cnf_line, parse_dimacs, parse_lit, parse_p_line,
        parse_preamble, write_cnf_annotated, Preamble,
    };
    use crate::{
        clause,
        instances::{BasicVarManager, Cnf, SatInstance},
        ipasir_lit,
    };
    use nom::error::Error as NomError;
    use std::io::{Cursor, Seek};

    #[cfg(feature = "optimization")]
    use super::{
        parse_idx, parse_mcnf_line, parse_no_pline_body, parse_wcnf_pre22_body,
        parse_wcnf_pre22_line, parse_weight, write_wcnf_annotated, Objective, OptInstance,
    };

    #[cfg(feature = "multiopt")]
    use super::{write_mcnf_annotated, MultiOptInstance};

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_idx_pass() {
        assert_eq!(parse_idx("15 "), Ok((" ", 15)));
        assert_eq!(parse_idx("42 63"), Ok((" 63", 42)));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_idx_fail() {
        assert!(parse_idx("0 ")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "0 ", .. }))));
        assert!(parse_idx("-15 ")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "-15 ", .. }))));
        assert!(parse_idx("abc ")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "abc ", .. }))));
        assert!(parse_idx(" abc ")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: " abc ", .. }))));
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
        assert!(parse_weight("-2 ")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "-2 ", .. }))));
        assert!(parse_weight("abc ")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "abc ", .. }))));
        assert!(parse_weight(" abc ")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: " abc ", .. }))));
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
        assert!(parse_lit("abc ")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "abc ", .. }))));
        assert!(parse_lit(" abc ")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: " abc ", .. }))));
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
        assert!(parse_p_line("a cnf 23 42").is_err_and(|e| matches!(
            e,
            nom::Err::Error(NomError {
                input: "a cnf 23 42",
                ..
            })
        )));
        assert!(parse_p_line("p abc 23 42 52").is_err_and(|e| matches!(
            e,
            nom::Err::Error(NomError {
                input: "abc 23 42 52",
                ..
            })
        )));
        assert!(parse_p_line("p cnf ab")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "ab", .. }))));
        assert!(parse_p_line("p wcnf ab")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "ab", .. }))));
        #[cfg(not(feature = "optimization"))]
        assert!(parse_p_line("p wcnf 23 42 52").is_err_and(|e| matches!(
            e,
            nom::Err::Error(NomError {
                input: "wcnf 23 42 52",
                ..
            })
        )));
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
        assert!(parse_clause_ending("test")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "test", .. }))));
        assert!(parse_clause_ending("0test")
            .is_err_and(|e| matches!(e, nom::Err::Error(NomError { input: "0test", .. }))));
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
        assert!(parse_cnf_line("42 34 a -16 0").is_err_and(|e| matches!(
            e,
            nom::Err::Error(NomError {
                input: "a -16 0",
                ..
            })
        )));
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

        assert_eq!(
            parse_preamble(&mut Cursor::new(data)).unwrap(),
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

        assert_eq!(
            parse_preamble(&mut Cursor::new(data)).unwrap(),
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

        assert_eq!(
            parse_preamble(&mut Cursor::new(data)).unwrap(),
            Preamble::NoPLine {
                first_line: String::from("h 5 2 0\n"),
            }
        );
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf_preamble() {
        let data = "c test\no1 2 0\nh 5 2 0";

        assert_eq!(
            parse_preamble(&mut Cursor::new(data)).unwrap(),
            Preamble::NoPLine {
                first_line: String::from("o1 2 0\n")
            }
        );
    }

    #[test]
    fn parse_cnf_body_pass() {
        let data = "1 2 0\n-3 4 5 0\n";

        let parsed_inst =
            parse_cnf_body(&mut Cursor::new(data), BasicVarManager::default()).unwrap();

        let mut true_inst: SatInstance = SatInstance::new();
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

        let parsed_inst =
            parse_wcnf_pre22_body(&mut Cursor::new(data), 42, BasicVarManager::default()).unwrap();

        let mut true_constrs: SatInstance = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj]));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_post22_body_pass() {
        let data = "h 1 2 0\n10 -3 4 5 0\n";

        let parsed_inst =
            parse_no_pline_body(&mut Cursor::new(data), "c test", BasicVarManager::default())
                .unwrap();

        let mut true_constrs: SatInstance = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj]));
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf_body_pass() {
        let data = "h 1 2 0\no2 10 -3 4 5 0\n";

        let parsed_inst = parse_no_pline_body(
            &mut Cursor::new(data),
            "c test\n",
            BasicVarManager::default(),
        )
        .unwrap();

        let mut true_constrs: SatInstance = SatInstance::new();
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

        let parsed_inst = parse_dimacs(&mut Cursor::new(data)).unwrap();

        let mut true_inst: SatInstance = SatInstance::new();
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
        use crate::{instances::ManageVars, types::Var};

        let data = "p wcnf 5 2 42\n42 1 2 0\n10 -3 4 5 0\n";

        let parsed_inst = parse_dimacs(&mut Cursor::new(data)).unwrap();

        let mut true_constrs: SatInstance = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_constrs
            .var_manager_mut()
            .increase_next_free(Var::new(5));
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj]));
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_wcnf_post22() {
        let data = "h 1 2 0\n10 -3 4 5 0\n";

        let parsed_inst = parse_dimacs(&mut Cursor::new(data)).unwrap();

        let mut true_constrs: SatInstance = SatInstance::new();
        let mut true_obj = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj]));
    }

    #[cfg(feature = "multiopt")]
    #[test]
    fn parse_mcnf() {
        let data = "c test\nh 1 2 0\no2 10 -3 4 5 0\no1 3 -1 0\n";

        let parsed_inst = parse_dimacs(&mut Cursor::new(data)).unwrap();

        let mut true_constrs: SatInstance = SatInstance::new();
        let mut true_obj0 = Objective::new();
        let mut true_obj1 = Objective::new();
        true_constrs.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_obj0.add_soft_clause(3, clause![ipasir_lit![-1]]);
        true_obj1.add_soft_clause(10, clause![ipasir_lit![-3], ipasir_lit![4], ipasir_lit![5]]);

        assert_eq!(parsed_inst, (true_constrs, vec![true_obj0, true_obj1]));
    }

    #[test]
    fn write_parse_cnf() {
        let mut true_cnf = Cnf::new();
        true_cnf.add_clause(clause![ipasir_lit![1], ipasir_lit![2]]);
        true_cnf.add_clause(clause![ipasir_lit![2], ipasir_lit![1]]);

        let mut cursor = Cursor::new(vec![]);

        write_cnf_annotated(&mut cursor, &true_cnf, 2).unwrap();

        cursor.rewind().unwrap();

        let parsed_inst: SatInstance = super::parse_cnf(&mut cursor).unwrap();
        let (parsed_cnf, _) = parsed_inst.into_cnf();

        assert_eq!(parsed_cnf, true_cnf);
    }

    #[cfg(feature = "optimization")]
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

        let parsed_inst = super::parse_wcnf_with_idx(&mut cursor, 0).unwrap();

        assert_eq!(parsed_inst, OptInstance::compose(true_constrs, true_obj));
    }

    #[cfg(feature = "multiopt")]
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

        let parsed_inst = super::parse_mcnf(&mut cursor).unwrap();

        assert_eq!(
            parsed_inst,
            MultiOptInstance::compose(true_constrs, vec![true_obj0, true_obj1])
        );
    }
}
