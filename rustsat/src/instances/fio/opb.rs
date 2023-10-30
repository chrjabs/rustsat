//! # Parsing OPB Files
//!
//! Internal module containing functions for parsing linear OPB files.
//! The approach is to accept input instances, even if they are not technically
//! in spec, as long as the input is still reasonable.
//!
//! ## References
//!
//! - [OPB](https://www.cril.univ-artois.fr/PB12/format.pdf)

use crate::{
    instances::{ManageVars, SatInstance},
    types::{
        constraints::{CardConstraint, PBConstraint},
        Clause, Lit, Var,
    },
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{anychar, i64, line_ending, space0, space1, u64},
    combinator::{eof, map_res, recognize},
    error::Error as NomError,
    multi::{many0, many_till},
    sequence::{pair, tuple},
    IResult,
};
use std::{
    io::{self, BufRead, BufReader, Read, Write},
    num::TryFromIntError,
};
use thiserror::Error;

#[cfg(feature = "multiopt")]
use crate::instances::MultiOptInstance;
#[cfg(feature = "optimization")]
use crate::instances::{Objective, OptInstance};
#[cfg(feature = "optimization")]
use crate::types::WLitIter;

/// Errors occuring within the OPB parsing module
#[derive(Error, Debug, PartialEq, Eq)]
pub enum Error {
    /// The requested objective does not exist
    #[error("no matching objective found in file")]
    ObjectiveNotFound,
    /// Encountered an unexpected line in the OPB file
    #[error("invalid OPB line: {0}")]
    InvalidLine(String),
    /// Error while reading input data
    #[error("IO error")]
    IOError,
}

/// Options for reading and writing OPB files
/// Possible relational operators
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Options {
    /// The variable with this index (`x<idx>`) in the OPB file will correspond to
    /// `var![0]`
    pub first_var_idx: u32,
    /// Whether to avoid negated literals (e.g., `4 ~x1`) by transforming the
    /// constraint
    pub no_negated_lits: bool,
}

impl Default for Options {
    /// Default options following the OPB specification
    fn default() -> Self {
        Self {
            first_var_idx: 0,
            no_negated_lits: true,
        }
    }
}

/// Possible relational operators
#[derive(Debug, PartialEq, Eq)]
enum OpbOperator {
    /// <=
    LE,
    /// >=
    GE,
    /// <
    LT,
    /// >
    GT,
    /// =
    EQ,
}

/// Possible parsing results for comment or constraint or objective
#[derive(Debug, PartialEq)]
enum OpbData {
    /// A comment
    Cmt(String),
    /// A constraint
    Constr(PBConstraint),
    /// An objective
    Obj(
        #[cfg(feature = "optimization")] Objective,
        #[cfg(not(feature = "optimization"))] String,
    ),
}

/// Parses the constraints from an OPB file as a [`SatInstance`]
pub fn parse_sat<R, VM>(reader: R, opts: Options) -> Result<SatInstance<VM>, Error>
where
    R: Read,
    VM: ManageVars + Default,
{
    let data = parse_opb_data(reader, opts)?;
    let mut inst = SatInstance::<VM>::new();
    data.into_iter().for_each(|d| {
        if let OpbData::Constr(constr) = d {
            inst.add_pb_constr(constr);
        }
    });
    Ok(inst)
}

#[cfg(feature = "optimization")]
/// Parses an OPB file as an [`OptInstance`] using the objective with the given
/// index (starting from 0).
pub fn parse_opt_with_idx<R, VM>(
    reader: R,
    obj_idx: usize,
    opts: Options,
) -> Result<OptInstance<VM>, Error>
where
    R: Read,
    VM: ManageVars + Default,
{
    let data = parse_opb_data(reader, opts)?;
    let mut sat_inst = SatInstance::<VM>::new();
    let mut obj_cnt = 0;
    let obj = data.into_iter().fold(Objective::new(), |o, d| match d {
        OpbData::Cmt(_) => o,
        OpbData::Constr(constr) => {
            sat_inst.add_pb_constr(constr);
            o
        }
        OpbData::Obj(obj) => {
            obj_cnt += 1;
            if obj_cnt - 1 == obj_idx {
                obj
            } else {
                o
            }
        }
    });
    if obj_cnt <= obj_idx {
        Err(Error::ObjectiveNotFound)
    } else {
        Ok(OptInstance::compose(sat_inst, obj))
    }
}

#[cfg(feature = "multiopt")]
/// Parses an OPB file as an [`MultiOptInstance`] using the objective with the given
/// index (starting from 0).
pub fn parse_multi_opt<R, VM>(reader: R, opts: Options) -> Result<MultiOptInstance<VM>, Error>
where
    R: Read,
    VM: ManageVars + Default,
{
    let data = parse_opb_data(reader, opts)?;
    let mut sat_inst = SatInstance::<VM>::new();
    let mut objs = vec![];
    data.into_iter().for_each(|d| match d {
        OpbData::Cmt(_) => (),
        OpbData::Constr(constr) => sat_inst.add_pb_constr(constr),
        OpbData::Obj(obj) => objs.push(obj),
    });
    Ok(MultiOptInstance::compose(sat_inst, objs))
}

/// Parses all OPB data of a reader
fn parse_opb_data<R: Read>(reader: R, opts: Options) -> Result<Vec<OpbData>, Error> {
    let mut reader = BufReader::new(reader);
    let mut buf = String::new();
    let mut data = vec![];
    while let Ok(len) = reader.read_line(&mut buf) {
        if len == 0 {
            return Ok(data);
        }
        match many0(|i| opb_data(i, opts))(&buf) {
            Ok((rem, new_data)) => {
                if !rem.is_empty() {
                    return Err(Error::InvalidLine(buf.clone()));
                } else {
                    data.extend(new_data)
                }
            }
            Err(_) => return Err(Error::InvalidLine(buf.clone())),
        }
        buf.clear();
    }
    Err(Error::IOError)
}

/// Matches an OPB comment
fn comment(input: &str) -> IResult<&str, &str> {
    recognize(pair(
        tag("*"),
        alt((
            recognize(many_till(anychar, line_ending)),
            recognize(many0(anychar)),
        )),
    ))(input)
}

/// Parses an OPB variable
fn variable(input: &str, opts: Options) -> IResult<&str, Var> {
    let (input, _) = tag("x")(input)?;
    map_res(u64, |idx| {
        let idx = (TryInto::<u32>::try_into(idx)?) - opts.first_var_idx;
        Ok::<Var, TryFromIntError>(Var::new(idx))
    })(input)
}

/// Parses a literal. The spec for linear OPB instances only allows for
/// variables but we allow negated literals with '~' as in non-linear OPB
/// instances.
fn literal(input: &str, opts: Options) -> IResult<&str, Lit> {
    match tag::<_, _, NomError<_>>("~")(input) {
        Ok((input, _)) => map_res(|i| variable(i, opts), |v| Ok::<_, ()>(v.neg_lit()))(input),
        Err(_) => map_res(|i| variable(i, opts), |v| Ok::<_, ()>(v.pos_lit()))(input),
    }
}

/// Parses an OPB relational operator. We admit more operators than the spec.
fn operator(input: &str) -> IResult<&str, OpbOperator> {
    let (input, op_str) = alt((tag("<="), tag(">="), tag("<"), tag(">"), tag("=")))(input)?;
    Ok((
        input,
        if op_str == "<=" {
            OpbOperator::LE
        } else if op_str == ">=" {
            OpbOperator::GE
        } else if op_str == "<" {
            OpbOperator::LT
        } else if op_str == ">" {
            OpbOperator::GT
        } else {
            OpbOperator::EQ
        },
    ))
}

/// Parses an OPB weight
fn weight(input: &str) -> IResult<&str, isize> {
    map_res(i64, |i| i.try_into())(input)
}

/// Parses an OPB weighted term
fn weighted_literal(input: &str, opts: Options) -> IResult<&str, (Lit, isize)> {
    map_res(
        tuple((weight, space1, |i| literal(i, opts), space0)),
        |(w, _, l, _)| Ok::<_, ()>((l, w)),
    )(input)
}

/// Parses an OPB sum
fn weighted_lit_sum(input: &str, opts: Options) -> IResult<&str, Vec<(Lit, isize)>> {
    many0(|i| weighted_literal(i, opts))(input)
}

/// Leniently parses OPB constraint or objective ending as ';' or a line ending
fn opb_ending(input: &str) -> IResult<&str, &str> {
    recognize(pair(
        space0,
        alt((
            recognize(pair(
                alt((
                    recognize(tuple((tag(";"), space0, line_ending))),
                    line_ending,
                    tag(";"),
                )),
                space0,
            )),
            eof,
        )),
    ))(input)
}

/// Parses an OPB constraint
fn constraint(input: &str, opts: Options) -> IResult<&str, PBConstraint> {
    map_res(
        tuple((
            |i| weighted_lit_sum(i, opts),
            operator,
            space0,
            weight,
            opb_ending,
        )),
        |(wls, op, _, b, _)| {
            let lits = wls.into_iter();
            Ok::<_, ()>(match op {
                OpbOperator::LE => PBConstraint::new_ub(lits, b),
                OpbOperator::GE => PBConstraint::new_lb(lits, b),
                OpbOperator::LT => PBConstraint::new_ub(lits, b + 1),
                OpbOperator::GT => PBConstraint::new_lb(lits, b + 1),
                OpbOperator::EQ => PBConstraint::new_eq(lits, b),
            })
        },
    )(input)
}

#[cfg(feature = "optimization")]
/// Parses an OPB objective
fn objective(input: &str, opts: Options) -> IResult<&str, Objective> {
    map_res(
        tuple((
            tag("min:"),
            space0,
            |i| weighted_lit_sum(i, opts),
            opb_ending,
        )),
        |(_, _, wsl, _)| {
            let mut obj = Objective::new();
            wsl.into_iter()
                .for_each(|(l, w)| obj.increase_soft_lit_int(w, l));
            Ok::<_, ()>(obj)
        },
    )(input)
}

#[cfg(not(feature = "optimization"))]
/// Matches an OPB objective
fn objective(input: &str, opts: Options) -> IResult<&str, &str> {
    recognize(tuple((
        tag("min:"),
        space0,
        |i| weighted_lit_sum(i, opts),
        opb_ending,
    )))(input)
}

/// Top level string parser applied to lines
fn opb_data(input: &str, opts: Options) -> IResult<&str, OpbData> {
    // remove leading spaces
    let (input, _) = space0(input)?;
    alt((
        map_res(comment, |cmt| Ok::<_, ()>(OpbData::Cmt(String::from(cmt)))),
        map_res(
            |i| constraint(i, opts),
            |constr| Ok::<_, ()>(OpbData::Constr(constr)),
        ),
        #[cfg(feature = "optimization")]
        map_res(|i| objective(i, opts), |obj| Ok::<_, ()>(OpbData::Obj(obj))),
        #[cfg(not(feature = "optimization"))]
        map_res(
            |i| objective(i, opts),
            |obj| Ok::<_, ()>(OpbData::Obj(String::from(obj))),
        ),
    ))(input)
}

/// Writes a [`SatInstance`] to an OPB file
pub fn write_sat<W, VM>(
    writer: &mut W,
    inst: SatInstance<VM>,
    opts: Options,
) -> Result<(), io::Error>
where
    W: Write,
    VM: ManageVars,
{
    writeln!(writer, "* OPB file written by RustSAT")?;
    if let Some(max_var) = inst.var_manager.max_var() {
        writeln!(writer, "* maximum variable: {}", max_var)?;
    }
    writeln!(writer, "* {} clauses", inst.n_clauses())?;
    writeln!(writer, "* {} cardinality constraints", inst.cards.len())?;
    writeln!(writer, "* {} pseudo-boolean constraints", inst.pbs.len())?;
    inst.cnf
        .into_iter()
        .try_for_each(|cl| write_clause(writer, cl, opts))?;
    inst.cards
        .into_iter()
        .try_for_each(|card| write_card(writer, card, opts))?;
    inst.pbs
        .into_iter()
        .try_for_each(|pb| write_pb(writer, pb, opts))?;
    writer.flush()
}

#[cfg(feature = "optimization")]
/// Writes an [`OptInstance`] to an OPB file
pub fn write_opt<W, VM>(
    writer: &mut W,
    inst: OptInstance<VM>,
    opts: Options,
) -> Result<(), io::Error>
where
    W: Write,
    VM: ManageVars,
{
    let (constrs, obj) = inst.decompose();
    let cnf = constrs.cnf;
    let cards = constrs.cards;
    let pbs = constrs.pbs;
    let mut vm = constrs.var_manager;
    let (hardened, softs) = obj.as_soft_lits(&mut vm);
    writeln!(writer, "* OPB file written by RustSAT")?;
    if let Some(max_var) = vm.max_var() {
        writeln!(writer, "* maximum variable: {}", max_var)?;
    }
    writeln!(writer, "* {} original hard clauses", cnf.len())?;
    writeln!(writer, "* {} cardinality constraints", cards.len())?;
    writeln!(writer, "* {} pseudo-boolean constraints", pbs.len())?;
    writeln!(
        writer,
        "* {} relaxed and hardened soft clauses",
        hardened.len()
    )?;
    write_objective(writer, softs, opts)?;
    hardened
        .into_iter()
        .try_for_each(|cl| write_clause(writer, cl, opts))?;
    cnf.into_iter()
        .try_for_each(|cl| write_clause(writer, cl, opts))?;
    cards
        .into_iter()
        .try_for_each(|card| write_card(writer, card, opts))?;
    pbs.into_iter()
        .try_for_each(|pb| write_pb(writer, pb, opts))?;
    writer.flush()
}

#[cfg(feature = "multiopt")]
/// Writes a [`MultiOptInstance`] to an OPB file
pub fn write_multi_opt<W, VM>(
    writer: &mut W,
    inst: MultiOptInstance<VM>,
    opts: Options,
) -> Result<(), io::Error>
where
    W: Write,
    VM: ManageVars,
{
    let (constrs, objs) = inst.decompose();
    let cnf = constrs.cnf;
    let cards = constrs.cards;
    let pbs = constrs.pbs;
    let mut vm = constrs.var_manager;
    let (hardened, objs) = objs
        .into_iter()
        .map(|o| o.as_soft_lits(&mut vm))
        .unzip::<_, _, Vec<_>, Vec<_>>();
    writeln!(writer, "* OPB file written by RustSAT")?;
    if let Some(max_var) = vm.max_var() {
        writeln!(writer, "* maximum variable: {}", max_var)?;
    }
    writeln!(writer, "* {} original hard clauses", cnf.len())?;
    writeln!(writer, "* {} cardinality constraints", cards.len())?;
    writeln!(writer, "* {} pseudo-boolean constraints", pbs.len())?;
    write!(writer, "* ( ")?;
    hardened
        .iter()
        .try_for_each(|h| write!(writer, "{} ", h.len()))?;
    writeln!(writer, ") relaxed and hardened soft clauses",)?;
    objs.into_iter()
        .try_for_each(|softs| write_objective(writer, softs, opts))?;
    hardened.into_iter().try_for_each(|h| {
        h.into_iter()
            .try_for_each(|cl| write_clause(writer, cl, opts))
    })?;
    cnf.into_iter()
        .try_for_each(|cl| write_clause(writer, cl, opts))?;
    cards
        .into_iter()
        .try_for_each(|card| write_card(writer, card, opts))?;
    pbs.into_iter()
        .try_for_each(|pb| write_pb(writer, pb, opts))?;
    writer.flush()
}

/// Writes a clause to an OPB file
fn write_clause<W: Write>(writer: &mut W, clause: Clause, opts: Options) -> Result<(), io::Error> {
    if opts.no_negated_lits {
        let mut rhs: isize = 1;
        clause.into_iter().try_for_each(|l| {
            if l.is_pos() {
                write!(writer, "1 x{} ", l.vidx32() + opts.first_var_idx)
            } else {
                rhs -= 1;
                write!(writer, "-1 x{} ", l.vidx32() + opts.first_var_idx)
            }
        })?;
        writeln!(writer, ">= {};", rhs)
    } else {
        clause.into_iter().try_for_each(|l| {
            if l.is_pos() {
                write!(writer, "1 x{} ", l.vidx32() + opts.first_var_idx)
            } else {
                write!(writer, "1 ~x{} ", l.vidx32() + opts.first_var_idx)
            }
        })?;
        writeln!(writer, ">= 1;")
    }
}

/// Writes a cardinality constraint to an OPB file
fn write_card<W: Write>(
    writer: &mut W,
    card: CardConstraint,
    opts: Options,
) -> Result<(), io::Error> {
    if opts.no_negated_lits {
        let (lits, bound, op) = match card {
            CardConstraint::UB(constr) => {
                let (lits, bound) = constr.decompose();
                let bound = lits.len() as isize - bound as isize;
                // Flip operator by negating literals
                let lits: Vec<Lit> = lits.into_iter().map(|l| !l).collect();
                (lits, bound, ">=")
            }
            CardConstraint::LB(constr) => {
                let (lits, bound) = constr.decompose();
                (lits, bound as isize, ">=")
            }
            CardConstraint::EQ(constr) => {
                let (lits, bound) = constr.decompose();
                (lits, bound as isize, "=")
            }
        };
        let mut offset = 0;
        lits.into_iter().try_for_each(|l| {
            if l.is_pos() {
                write!(writer, "1 x{} ", l.vidx32() + opts.first_var_idx)
            } else {
                offset += 1;
                write!(writer, "-1 x{} ", l.vidx32() + opts.first_var_idx)
            }
        })?;
        writeln!(writer, "{} {};", op, bound - offset)
    } else {
        let (lits, bound, op) = match card {
            CardConstraint::UB(constr) => {
                let (lits, bound) = constr.decompose();
                let bound = lits.len() as isize - bound as isize;
                // Flip operator by negating literals
                let lits: Vec<Lit> = lits.into_iter().map(|l| !l).collect();
                (lits, bound, ">=")
            }
            CardConstraint::LB(constr) => {
                let (lits, bound) = constr.decompose();
                (lits, bound as isize, ">=")
            }
            CardConstraint::EQ(constr) => {
                let (lits, bound) = constr.decompose();
                (lits, bound as isize, "=")
            }
        };
        lits.into_iter().try_for_each(|l| {
            if l.is_pos() {
                write!(writer, "1 x{} ", l.vidx32() + opts.first_var_idx)
            } else {
                write!(writer, "1 ~x{} ", l.vidx32() + opts.first_var_idx)
            }
        })?;
        writeln!(writer, "{} {};", op, bound)
    }
}

/// Writes a pseudo-boolean constraint to an OPB file
fn write_pb<W: Write>(writer: &mut W, pb: PBConstraint, opts: Options) -> Result<(), io::Error> {
    if opts.no_negated_lits {
        let (lits, bound, op) = match pb {
            PBConstraint::UB(constr) => {
                let (lits, bound) = constr.decompose();
                let weight_sum = lits.iter().fold(0, |sum, (_, w)| sum + w);
                // Flip operator by negating literals
                let lits = lits.into_iter().map(|(l, w)| (!l, w)).collect();
                (lits, weight_sum as isize - bound, ">=")
            }
            PBConstraint::LB(constr) => {
                let (lits, bound) = constr.decompose();
                (lits, bound, ">=")
            }
            PBConstraint::EQ(constr) => {
                let (lits, bound) = constr.decompose();
                (lits, bound, "=")
            }
        };
        let mut offset: isize = 0;
        lits.into_iter().try_for_each(|(l, w)| {
            if l.is_pos() {
                write!(writer, "{} x{} ", w, l.vidx32() + opts.first_var_idx)
            } else {
                // TODO: consider returning error for usize -> isize cast
                let w = w as isize;
                offset += w;
                write!(writer, "{} x{} ", -w, l.vidx32() + opts.first_var_idx)
            }
        })?;
        writeln!(writer, "{} {};", op, bound - offset)
    } else {
        let (lits, bound, op) = match pb {
            PBConstraint::UB(constr) => {
                let (lits, bound) = constr.decompose();
                let weight_sum = lits.iter().fold(0, |sum, (_, w)| sum + w);
                // Flip operator by negating literals
                let lits = lits.into_iter().map(|(l, w)| (!l, w)).collect();
                (lits, weight_sum as isize - bound, ">=")
            }
            PBConstraint::LB(constr) => {
                let (lits, bound) = constr.decompose();
                (lits, bound, ">=")
            }
            PBConstraint::EQ(constr) => {
                let (lits, bound) = constr.decompose();
                (lits, bound, "=")
            }
        };
        lits.into_iter().try_for_each(|(l, w)| {
            if l.is_pos() {
                write!(writer, "{} x{} ", w, l.vidx32() + opts.first_var_idx)
            } else {
                write!(writer, "{} ~x{} ", w, l.vidx32() + opts.first_var_idx)
            }
        })?;
        writeln!(writer, "{} {};", op, bound)
    }
}

#[cfg(feature = "optimization")]
fn write_objective<W: Write, LI: WLitIter>(
    writer: &mut W,
    softs: (LI, isize),
    opts: Options,
) -> Result<(), io::Error> {
    let (soft_lits, mut offset) = softs;
    write!(writer, "min:")?;
    if opts.no_negated_lits {
        soft_lits
            .into_iter()
            .map(|(l, w)| {
                if l.is_neg() {
                    offset += w as isize;
                    (l.var(), -(w as isize))
                } else {
                    (l.var(), w as isize)
                }
            })
            .try_for_each(|(v, w)| write!(writer, " {} x{}", w, v.idx32() + opts.first_var_idx))?;
    } else {
        soft_lits.into_iter().try_for_each(|(l, w)| {
            if l.is_pos() {
                write!(writer, " {} x{}", w, l.vidx32() + opts.first_var_idx)
            } else {
                write!(writer, " {} ~x{}", w, l.vidx32() + opts.first_var_idx)
            }
        })?;
    }
    writeln!(writer, ";")?;
    if offset != 0 {
        // OPB does not support offsets in objectives, so we have to add it as a comment
        writeln!(
            writer,
            "* objective offset for previous objective: {}",
            offset
        )?;
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use std::io::{Cursor, Seek};

    use super::{
        comment, constraint, literal, objective, opb_ending, operator, variable, weight,
        weighted_lit_sum, weighted_literal, write_clause, write_sat, OpbOperator, Options,
    };
    use crate::{
        clause,
        instances::{BasicVarManager, SatInstance},
        lit,
        types::constraints::{CardConstraint, PBConstraint},
        var,
    };
    use nom::error::{Error as NomError, ErrorKind};

    #[cfg(feature = "optimization")]
    use super::{opb_data, parse_opb_data, Error, OpbData};
    #[cfg(feature = "optimization")]
    use crate::instances::Objective;
    #[cfg(feature = "optimization")]
    use std::io::BufReader;

    #[test]
    fn match_comment() {
        assert_eq!(comment("* test\n"), Ok(("", "* test\n")));
        assert_eq!(comment("* test"), Ok(("", "* test")));
        assert_eq!(comment("*\n"), Ok(("", "*\n")));
        assert_eq!(
            comment(" test\n"),
            Err(nom::Err::Error(NomError::new(" test\n", ErrorKind::Tag)))
        );
    }

    #[test]
    fn parse_variable() {
        assert_eq!(
            variable("x5 test", Options::default()),
            Ok((" test", var![5]))
        );
        assert_eq!(
            variable(
                "x5 test",
                Options {
                    first_var_idx: 1,
                    no_negated_lits: true
                }
            ),
            Ok((" test", var![4]))
        );
        assert_eq!(
            variable("x2 test", Options::default()),
            Ok((" test", var![2]))
        );
        assert_eq!(
            variable(" test\n", Options::default()),
            Err(nom::Err::Error(NomError::new(" test\n", ErrorKind::Tag)))
        );
    }

    #[test]
    fn parse_literal() {
        assert_eq!(
            literal("x5 test", Options::default()),
            Ok((" test", lit![5]))
        );
        assert_eq!(
            literal("x2 test", Options::default()),
            Ok((" test", lit![2]))
        );
        assert_eq!(
            literal("~x5 test", Options::default()),
            Ok((" test", !lit![5]))
        );
        assert_eq!(
            literal("~x2 test", Options::default()),
            Ok((" test", !lit![2]))
        );
    }

    #[test]
    fn parse_operator() {
        assert_eq!(operator("<= test"), Ok((" test", OpbOperator::LE)));
        assert_eq!(operator(">= test"), Ok((" test", OpbOperator::GE)));
        assert_eq!(operator("< test"), Ok((" test", OpbOperator::LT)));
        assert_eq!(operator("> test"), Ok((" test", OpbOperator::GT)));
        assert_eq!(operator("= test"), Ok((" test", OpbOperator::EQ)));
    }

    #[test]
    fn parse_weight() {
        assert_eq!(weight("5 test"), Ok((" test", 5)));
        assert_eq!(weight("+5 test"), Ok((" test", 5)));
        assert_eq!(weight("-5 test"), Ok((" test", -5)));
    }

    #[test]
    fn parse_weighted_literal() {
        assert_eq!(
            weighted_literal("5 x1 test", Options::default()),
            Ok(("test", (lit![1], 5)))
        );
        assert_eq!(
            weighted_literal("-5  x1 test", Options::default()),
            Ok(("test", (lit![1], -5)))
        );
        assert_eq!(
            weighted_literal("5 ~x1  test", Options::default()),
            Ok(("test", (!lit![1], 5)))
        );
        assert_eq!(
            weighted_literal("-5 ~x1 test", Options::default()),
            Ok(("test", (!lit![1], -5)))
        );
    }

    #[test]
    fn parse_weighted_lit_sum() {
        assert_eq!(
            weighted_lit_sum("5  x1    -3 ~x2  test", Options::default()),
            Ok(("test", vec![(lit![1], 5), (!lit![2], -3)]))
        );
    }

    #[test]
    fn parse_opb_ending() {
        assert_eq!(opb_ending("   ; test"), Ok(("test", "   ; ")));
        assert_eq!(opb_ending("   \n test"), Ok(("test", "   \n ")));
        assert_eq!(opb_ending("  ; \n test"), Ok(("test", "  ; \n ")));
        assert_eq!(opb_ending("  "), Ok(("", "  ")));
    }

    #[test]
    fn parse_constraint() {
        match constraint("3 x1 -2 ~x2 <= 4;", Options::default()) {
            Ok((rest, constr)) => match constr {
                PBConstraint::UB(constr) => {
                    assert_eq!(rest, "");
                    let (lits, b) = constr.decompose();
                    let should_be_lits = vec![(lit![1], 3), (lit![2], 2)];
                    assert_eq!(lits, should_be_lits);
                    assert_eq!(b, 6);
                }
                PBConstraint::LB(_) => panic!(),
                PBConstraint::EQ(_) => panic!(),
            },
            Err(_) => panic!(),
        }
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_objective() {
        match objective("min: 3 x1 -2 ~x2;", Options::default()) {
            Ok((rest, obj)) => {
                assert_eq!(rest, "");
                let mut should_be_obj = Objective::new();
                should_be_obj.increase_soft_lit_int(3, lit![1]);
                should_be_obj.increase_soft_lit_int(-2, !lit![2]);
                assert_eq!(obj, should_be_obj);
            }
            Err(_) => panic!(),
        }
        match objective("min: x0;", Options::default()) {
            Ok(_) => panic!(),
            Err(err) => assert_eq!(err, nom::Err::Error(NomError::new("x0;", ErrorKind::Eof))),
        }
        match objective("min:;", Options::default()) {
            Ok((rest, obj)) => {
                assert_eq!(rest, "");
                let should_be_obj = Objective::new();
                assert_eq!(obj, should_be_obj);
            }
            Err(_) => panic!(),
        }
    }

    #[cfg(not(feature = "optimization"))]
    #[test]
    fn parse_objective() {
        assert_eq!(
            objective("min: 3 x1 -2 ~x2;"),
            Ok(("", "min: 3 x1 -2 ~x2;"))
        );
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn single_opb_data() {
        assert_eq!(
            opb_data("* test\n", Options::default()),
            Ok(("", OpbData::Cmt(String::from("* test\n"))))
        );
        let lits = vec![(lit![1], 3), (!lit![2], -2)];
        let should_be_constr = PBConstraint::new_ub(lits, 4);
        assert_eq!(
            opb_data("3 x1 -2 ~x2 <= 4;\n", Options::default()),
            Ok(("", OpbData::Constr(should_be_constr)))
        );
        #[cfg(feature = "optimization")]
        {
            let mut obj = Objective::new();
            obj.increase_soft_lit_int(-3, lit![0]);
            obj.increase_soft_lit_int(4, lit![1]);
            assert_eq!(
                opb_data("min: -3 x0 4 x1;", Options::default()),
                Ok(("", OpbData::Obj(obj)))
            );
            assert_eq!(
                opb_data("min: x0;", Options::default()),
                Err(nom::Err::Error(NomError::new("x0;", ErrorKind::Eof)))
            );
        }
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn multi_opb_data() {
        let data = "* test\n5 x0 -3 x1 >= 4;\nmin: 1 x0;";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);
        match parse_opb_data(reader, Options::default()) {
            Ok(data) => {
                assert_eq!(data.len(), 3);
                assert_eq!(data[0], OpbData::Cmt(String::from("* test\n")));
                if let OpbData::Constr(_) = data[1] {
                    ()
                } else {
                    panic!()
                }
                if let OpbData::Obj(_) = data[2] {
                    ()
                } else {
                    panic!()
                }
            }
            Err(_) => panic!(),
        }
        let data = "* test\n5 x0 -3 x1 >= 4;\nmin: x0;";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);
        assert_eq!(
            parse_opb_data(reader, Options::default()),
            Err(Error::InvalidLine(String::from("min: x0;")))
        );
    }

    #[test]
    fn write_parse_clause() {
        let cl = clause![!lit![0], lit![1], !lit![2]];

        let mut cursor = Cursor::new(vec![]);

        write_clause(&mut cursor, cl.clone(), Options::default()).unwrap();

        cursor.rewind().unwrap();

        let (cnf, _) = super::parse_sat::<_, BasicVarManager>(cursor, Options::default())
            .unwrap()
            .as_cnf();

        assert_eq!(cnf.len(), 1);
        assert_eq!(cnf.into_iter().next().unwrap().normalize(), cl.normalize());
    }

    fn write_parse_inst_test(in_inst: SatInstance, true_inst: SatInstance, opts: Options) {
        let mut cursor = Cursor::new(vec![]);

        write_sat(&mut cursor, in_inst, opts).unwrap();

        cursor.rewind().unwrap();

        let parsed_inst: SatInstance = super::parse_sat(cursor, opts).unwrap();

        let (parsed_cnf, parsed_vm) = parsed_inst.as_cnf();
        let (true_cnf, true_vm) = true_inst.as_cnf();

        assert_eq!(parsed_vm, true_vm);
        assert_eq!(parsed_cnf.normalize(), true_cnf.normalize());
    }

    #[test]
    fn write_parse_card() {
        // Note: this test is known to fail _sometimes_ without feature "fxhash".
        // This is due to the non-deterministic default hash function.

        // Since the hash map of going through a pb constraint at parsing
        // reorders the literals, the true instance has to go through a pb
        // constraint as well.
        let lits = vec![(!lit![3], 1), (lit![4], 1), (!lit![5], 1)];

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_ub(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(in_inst, true_inst, Options::default());

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_eq(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(in_inst, true_inst, Options::default());

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_lb(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(in_inst, true_inst, Options::default());
    }

    #[test]
    fn write_parse_card_neg_lits() {
        // Note: this test is known to fail _sometimes_ without feature "fxhash".
        // This is due to the non-deterministic default hash function.

        // Since the hash map of going through a pb constraint at parsing
        // reorders the literals, the true instance has to go through a pb
        // constraint as well.
        let lits = vec![(!lit![3], 1), (lit![4], 1), (!lit![5], 1)];

        let mut alt_opb_opts = Options::default();
        alt_opb_opts.no_negated_lits = false;

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_ub(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(in_inst, true_inst, alt_opb_opts);

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_eq(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(in_inst, true_inst, alt_opb_opts);

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_lb(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(in_inst, true_inst, alt_opb_opts);
    }

    #[test]
    fn write_parse_pb() {
        let lits = vec![(!lit![6], 3), (!lit![7], -5), (lit![8], 2), (lit![9], -4)];

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(true_inst.clone(), true_inst, Options::default());

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(true_inst.clone(), true_inst, Options::default());

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(true_inst.clone(), true_inst, Options::default());
    }

    #[test]
    fn write_parse_pb_neg_lits() {
        let lits = vec![(!lit![6], 3), (!lit![7], -5), (lit![8], 2), (lit![9], -4)];

        let mut alt_opb_opts = Options::default();
        alt_opb_opts.no_negated_lits = false;

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(true_inst.clone(), true_inst, alt_opb_opts);

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(true_inst.clone(), true_inst, alt_opb_opts);

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(true_inst.clone(), true_inst, alt_opb_opts);
    }
}
