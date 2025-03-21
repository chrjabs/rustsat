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
        constraints::{CardConstraint, PbConstraint},
        Cl, Clause, Lit, Var,
    },
};
use anyhow::Context;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{anychar, i64, line_ending, space0, space1, u64},
    combinator::{cut, eof, map, map_res, recognize},
    error::Error as NomError,
    multi::{many0, many1, many_till},
    sequence::{pair, tuple},
    IResult,
};
use std::{
    io::{self, BufRead, Write},
    num::TryFromIntError,
};

#[cfg(feature = "multiopt")]
use crate::instances::MultiOptInstance;
#[cfg(feature = "optimization")]
use crate::instances::{Objective, OptInstance};

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
            first_var_idx: 1,
            no_negated_lits: true,
        }
    }
}

/// Possible relational operators
#[derive(Debug, PartialEq, Eq)]
enum OpbOperator {
    /// `<=`
    LE,
    /// `>=`
    GE,
    /// `<`
    LT,
    /// `>`
    GT,
    /// `=`
    EQ,
}

/// Possible parsing results for comment or constraint or objective
#[derive(Debug, PartialEq)]
enum OpbData {
    /// A comment
    Cmt(String),
    /// A constraint
    Constr(PbConstraint),
    /// An objective
    Obj(
        #[cfg(feature = "optimization")] Objective,
        #[cfg(not(feature = "optimization"))] String,
    ),
}

/// Parses the constraints from an OPB file as a [`SatInstance`]
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
pub fn parse_sat<R, VM>(reader: &mut R, opts: Options) -> anyhow::Result<SatInstance<VM>>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    let data = parse_opb_data(reader, opts)?;
    let mut inst = SatInstance::<VM>::new();
    for d in data {
        if let OpbData::Constr(constr) = d {
            inst.add_pb_constr(constr);
        }
    }
    Ok(inst)
}

#[cfg(feature = "optimization")]
/// Parses an OPB file as an [`OptInstance`] using the objective with the given
/// index (starting from 0).
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
pub fn parse_opt_with_idx<R, VM>(
    reader: &mut R,
    obj_idx: usize,
    opts: Options,
) -> anyhow::Result<OptInstance<VM>>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    use super::ObjNoExist;

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
        Err(ObjNoExist(obj_cnt).into())
    } else {
        Ok(OptInstance::compose(sat_inst, obj))
    }
}

#[cfg(feature = "multiopt")]
/// Parses an OPB file as an [`MultiOptInstance`] using the objective with the given
/// index (starting from 0).
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
pub fn parse_multi_opt<R, VM>(reader: &mut R, opts: Options) -> anyhow::Result<MultiOptInstance<VM>>
where
    R: BufRead,
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
fn parse_opb_data<R: BufRead>(reader: &mut R, opts: Options) -> anyhow::Result<Vec<OpbData>> {
    let mut buf = String::new();
    let mut data = vec![];
    // TODO: consider not necessarily reading a full line
    while reader.read_line(&mut buf)? > 0 {
        let (rem, new_data) = many0(|i| opb_data(i, opts))(&buf)
            .map_err(nom::Err::<NomError<&str>>::to_owned)
            .with_context(|| format!("failed to parse opb line '{buf}'"))?;
        data.extend(new_data);
        if rem.is_empty() {
            buf.clear();
        } else {
            // continue with remainder, this allows for line breaks within constraints etc
            // TODO: to work, this requires the opb_ending function to be adapted
            buf = String::from(rem);
        }
    }
    Ok(data)
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
/// variables but we allow negated literals with `~` as in non-linear OPB
/// instances.
///
/// # Errors
///
/// If parsing fails
#[cfg_attr(feature = "internals", visibility::make(pub))]
pub(crate) fn literal(input: &str, opts: Options) -> IResult<&str, Lit> {
    match alt::<_, _, NomError<_>, _>((tag("~"), tag("-")))(input) {
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
    map_res(i64, TryInto::try_into)(input)
}

/// Parses an OPB weighted term
fn weighted_literal(input: &str, opts: Options) -> IResult<&str, (Lit, isize)> {
    map(
        tuple((weight, cut(space1), cut(|i| literal(i, opts)), space0)),
        |(w, _, l, _)| (l, w),
    )(input)
}

/// Parses an OPB sum
fn weighted_lit_sum(input: &str, opts: Options) -> IResult<&str, Vec<(Lit, isize)>> {
    many1(|i| weighted_literal(i, opts))(input)
}

#[cfg(feature = "optimization")]
/// Parses a (potentially empty) OPB sum
fn weighted_lit_sum0(input: &str, opts: Options) -> IResult<&str, Vec<(Lit, isize)>> {
    many0(|i| weighted_literal(i, opts))(input)
}

/// Leniently parses OPB constraint or objective ending as ';' or a line ending
fn opb_ending(input: &str) -> IResult<&str, &str> {
    // TODO: potentially simplify with `cut`?
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
fn constraint(input: &str, opts: Options) -> IResult<&str, PbConstraint> {
    map_res(
        tuple((
            |i| weighted_lit_sum(i, opts),
            cut(operator),
            space0,
            cut(weight),
            cut(opb_ending),
        )),
        |(wls, op, _, b, _)| {
            let lits = wls.into_iter();
            Ok::<_, ()>(match op {
                OpbOperator::LE => PbConstraint::new_ub(lits, b),
                OpbOperator::GE => PbConstraint::new_lb(lits, b),
                OpbOperator::LT => PbConstraint::new_ub(lits, b + 1),
                OpbOperator::GT => PbConstraint::new_lb(lits, b + 1),
                OpbOperator::EQ => PbConstraint::new_eq(lits, b),
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
            |i| weighted_lit_sum0(i, opts),
            cut(opb_ending),
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
        map(comment, |cmt| OpbData::Cmt(String::from(cmt))),
        map(|i| constraint(i, opts), OpbData::Constr),
        #[cfg(feature = "optimization")]
        map(|i| objective(i, opts), OpbData::Obj),
        #[cfg(not(feature = "optimization"))]
        map(
            |i| objective(i, opts),
            |obj| OpbData::Obj(String::from(obj)),
        ),
    ))(input)
}

/// Possible lines that can be written to OPB
#[cfg(not(feature = "optimization"))]
pub enum FileLine {
    /// A comment line
    Comment(String),
    /// A clausal constraint line
    Clause(Clause),
    /// A cardinality constraint line
    Card(CardConstraint),
    /// A PB constraint line
    Pb(PbConstraint),
}

/// Possible lines that can be written to OPB
#[cfg(feature = "optimization")]
pub enum FileLine<LI: crate::types::WLitIter> {
    /// A comment line
    Comment(String),
    /// A clausal constraint line
    Clause(Clause),
    /// A cardinality constraint line
    Card(CardConstraint),
    /// A PB constraint line
    Pb(PbConstraint),
    /// An objective line
    Objective(LI),
}

/// Writes an OPB file from an iterator over [`FileLine`]s
///
/// # Errors
///
/// If writing fails, returns [`io::Error`]
#[cfg(not(feature = "optimization"))]
pub fn write_opb_lines<W, Iter>(writer: &mut W, data: Iter, opts: Options) -> io::Result<()>
where
    W: Write,
    Iter: Iterator<Item = FileLine>,
{
    for dat in data {
        match dat {
            FileLine::Comment(c) => writeln!(writer, "* {c}")?,
            FileLine::Clause(cl) => write_clause(writer, &cl, opts)?,
            FileLine::Card(card) => write_card(writer, &card, opts)?,
            FileLine::Pb(pb) => write_pb(writer, &pb, opts)?,
        }
    }
    Ok(())
}

/// Writes an OPB file from an iterator over [`FileLine`]s
///
/// # Errors
///
/// If writing fails, returns [`io::Error`]
#[cfg(feature = "optimization")]
pub fn write_opb_lines<W, LI, Iter>(writer: &mut W, data: Iter, opts: Options) -> io::Result<()>
where
    W: Write,
    LI: crate::types::WLitIter,
    Iter: Iterator<Item = FileLine<LI>>,
{
    for dat in data {
        match dat {
            FileLine::Comment(c) => writeln!(writer, "* {c}")?,
            FileLine::Clause(cl) => write_clause(writer, &cl, opts)?,
            FileLine::Card(card) => write_card(writer, &card, opts)?,
            FileLine::Pb(pb) => write_pb(writer, &pb, opts)?,
            FileLine::Objective(obj) => write_objective(writer, (obj, 0), opts)?,
        }
    }
    Ok(())
}

/// Writes a [`SatInstance`] to an OPB file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
///
/// # Panics
///
/// - On weights larger than [`isize::MAX`]
/// - On upper bound constraint with weight sum larger than [`isize::MAX`]
/// - On bounds lager than [`isize::MAX`]
pub fn write_sat<W, VM>(
    writer: &mut W,
    inst: &SatInstance<VM>,
    opts: Options,
) -> Result<(), io::Error>
where
    W: Write,
    VM: ManageVars,
{
    writeln!(
        writer,
        "* #variable = {} #constraint= {}",
        inst.var_manager.n_used(),
        inst.n_clauses() + inst.cards.len() + inst.pbs.len()
    )?;
    writeln!(writer, "* OPB file written by RustSAT")?;
    if let Some(max_var) = inst.var_manager.max_var() {
        writeln!(writer, "* maximum variable: {max_var}")?;
    }
    writeln!(writer, "* {} clauses", inst.n_clauses())?;
    writeln!(writer, "* {} cardinality constraints", inst.cards.len())?;
    writeln!(writer, "* {} pseudo-boolean constraints", inst.pbs.len())?;
    inst.cnf
        .iter()
        .try_for_each(|cl| write_clause(writer, cl, opts))?;
    inst.cards
        .iter()
        .try_for_each(|card| write_card(writer, card, opts))?;
    inst.pbs
        .iter()
        .try_for_each(|pb| write_pb(writer, pb, opts))?;
    writer.flush()
}

#[cfg(feature = "optimization")]
/// Writes an optimization instance to an OPB file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
///
/// # Panics
///
/// - On weights larger than [`isize::MAX`]
/// - On upper bound constraint with weight sum larger than [`isize::MAX`]
/// - On bounds lager than [`isize::MAX`]
pub fn write_opt<W, VM, LI>(
    writer: &mut W,
    constrs: &SatInstance<VM>,
    obj: (LI, isize),
    opts: Options,
) -> Result<(), io::Error>
where
    W: Write,
    LI: crate::types::WLitIter,
    VM: ManageVars,
{
    let cnf = &constrs.cnf;
    let cards = &constrs.cards;
    let pbs = &constrs.pbs;
    writeln!(
        writer,
        "* #variable = {} #constraint= {}",
        constrs.n_vars(),
        cnf.len() + cards.len() + pbs.len()
    )?;
    writeln!(writer, "* OPB file written by RustSAT")?;
    if let Some(max_var) = constrs.max_var() {
        writeln!(writer, "* maximum variable: {max_var}")?;
    }
    writeln!(writer, "* {} original hard clauses", cnf.len())?;
    writeln!(writer, "* {} cardinality constraints", cards.len())?;
    writeln!(writer, "* {} pseudo-boolean constraints", pbs.len())?;
    write_objective(writer, obj, opts)?;
    cnf.iter()
        .try_for_each(|cl| write_clause(writer, cl, opts))?;
    cards
        .iter()
        .try_for_each(|card| write_card(writer, card, opts))?;
    pbs.iter().try_for_each(|pb| write_pb(writer, pb, opts))?;
    writer.flush()
}

#[cfg(feature = "multiopt")]
/// Writes a [`MultiOptInstance`] to an OPB file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
///
/// # Panics
///
/// - On weights larger than [`isize::MAX`]
/// - On upper bound constraint with weight sum larger than [`isize::MAX`]
/// - On bounds lager than [`isize::MAX`]
pub fn write_multi_opt<W, VM, Iter, LI>(
    writer: &mut W,
    constrs: &SatInstance<VM>,
    mut objs: Iter,
    opts: Options,
) -> Result<(), io::Error>
where
    W: Write,
    VM: ManageVars,
    Iter: Iterator<Item = (LI, isize)>,
    LI: crate::types::WLitIter,
{
    let cnf = &constrs.cnf;
    let cards = &constrs.cards;
    let pbs = &constrs.pbs;
    writeln!(
        writer,
        "* #variable = {} #constraint= {}",
        constrs.n_vars(),
        cnf.len() + cards.len() + pbs.len()
    )?;
    writeln!(writer, "* OPB file written by RustSAT")?;
    if let Some(max_var) = constrs.max_var() {
        writeln!(writer, "* maximum variable: {max_var}")?;
    }
    writeln!(writer, "* {} original hard clauses", cnf.len())?;
    writeln!(writer, "* {} cardinality constraints", cards.len())?;
    writeln!(writer, "* {} pseudo-boolean constraints", pbs.len())?;
    write!(writer, "* ( ")?;
    writeln!(writer, ") relaxed and hardened soft clauses",)?;
    objs.try_for_each(|softs| write_objective(writer, softs, opts))?;
    cnf.iter()
        .try_for_each(|cl| write_clause(writer, cl, opts))?;
    cards
        .iter()
        .try_for_each(|card| write_card(writer, card, opts))?;
    pbs.iter().try_for_each(|pb| write_pb(writer, pb, opts))?;
    writer.flush()
}

/// Writes a clause to an OPB file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
fn write_clause<W, C>(writer: &mut W, clause: &C, opts: Options) -> Result<(), io::Error>
where
    W: Write,
    C: AsRef<Cl> + ?Sized,
{
    if opts.no_negated_lits {
        let mut rhs: isize = 1;
        clause.as_ref().iter().try_for_each(|l| {
            if l.is_pos() {
                write!(writer, "1 x{} ", l.vidx32() + opts.first_var_idx)
            } else {
                rhs -= 1;
                write!(writer, "-1 x{} ", l.vidx32() + opts.first_var_idx)
            }
        })?;
        writeln!(writer, ">= {rhs};")
    } else {
        clause.as_ref().iter().try_for_each(|l| {
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
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
///
/// # Panics
///
/// - On upper bounding constraint with more than [`isize::MAX`] literals
/// - On bounds lager than [`isize::MAX`]
fn write_card<W: Write>(
    writer: &mut W,
    card: &CardConstraint,
    opts: Options,
) -> Result<(), io::Error> {
    let mut iter_a;
    let mut iter_b;
    let neg_lit = |l: &Lit| !*l;
    if opts.no_negated_lits {
        let (lits, bound, op): (&mut dyn Iterator<Item = Lit>, _, _) = match card {
            CardConstraint::Ub(constr) => {
                let (lits, bound) = constr.decompose_ref();
                let bound = isize::try_from(lits.len())
                    .expect("cannot handle more than `isize::MAX` literals")
                    - isize::try_from(*bound)
                        .expect("cannot handle bound higher than `isize::MAX`");
                // Flip operator by negating literals
                iter_a = lits.iter().map(neg_lit);
                (&mut iter_a, bound, ">=")
            }
            CardConstraint::Lb(constr) => {
                let (lits, bound) = constr.decompose_ref();
                iter_b = lits.iter().copied();
                (
                    &mut iter_b,
                    isize::try_from(*bound).expect("cannot handle bound higher than `isize::MAX`"),
                    ">=",
                )
            }
            CardConstraint::Eq(constr) => {
                let (lits, bound) = constr.decompose_ref();
                iter_b = lits.iter().copied();
                (
                    &mut iter_b,
                    isize::try_from(*bound).expect("cannot handle bound higher than `isize::MAX`"),
                    "=",
                )
            }
        };
        let mut offset = 0;
        for l in lits {
            if l.is_pos() {
                write!(writer, "1 x{} ", l.vidx32() + opts.first_var_idx)?;
            } else {
                offset += 1;
                write!(writer, "-1 x{} ", l.vidx32() + opts.first_var_idx)?;
            }
        }
        writeln!(writer, "{} {};", op, bound - offset)
    } else {
        let (lits, bound, op): (&mut dyn Iterator<Item = Lit>, _, _) = match card {
            CardConstraint::Ub(constr) => {
                let (lits, bound) = constr.decompose_ref();
                let bound = isize::try_from(lits.len())
                    .expect("cannot handle more than `isize::MAX` literals")
                    - isize::try_from(*bound)
                        .expect("cannot handle bound higher than `isize::MAX`");
                // Flip operator by negating literals
                iter_a = lits.iter().map(neg_lit);
                (&mut iter_a, bound, ">=")
            }
            CardConstraint::Lb(constr) => {
                let (lits, bound) = constr.decompose_ref();
                iter_b = lits.iter().copied();
                (
                    &mut iter_b,
                    isize::try_from(*bound).expect("cannot handle bound higher than `isize::MAX`"),
                    ">=",
                )
            }
            CardConstraint::Eq(constr) => {
                let (lits, bound) = constr.decompose_ref();
                iter_b = lits.iter().copied();
                (
                    &mut iter_b,
                    isize::try_from(*bound).expect("cannot handle bound higher than `isize::MAX`"),
                    "=",
                )
            }
        };
        for l in lits {
            if l.is_pos() {
                write!(writer, "1 x{} ", l.vidx32() + opts.first_var_idx)?;
            } else {
                write!(writer, "1 ~x{} ", l.vidx32() + opts.first_var_idx)?;
            }
        }
        writeln!(writer, "{op} {bound};")
    }
}

/// Writes a pseudo-boolean constraint to an OPB file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
///
/// # Panics
///
/// - On weights larger than [`isize::MAX`]
/// - On upper bound constraint with weight sum larger than [`isize::MAX`]
fn write_pb<W: Write>(writer: &mut W, pb: &PbConstraint, opts: Options) -> Result<(), io::Error> {
    let mut iter_a;
    let mut iter_b;
    let neg_lit = |(l, w): &(Lit, usize)| (!*l, *w);
    if opts.no_negated_lits {
        let (lits, bound, op): (&mut dyn Iterator<Item = (Lit, usize)>, _, _) = match pb {
            PbConstraint::Ub(constr) => {
                let (lits, bound) = constr.decompose_ref();
                let weight_sum = lits.iter().fold(0, |sum, (_, w)| sum + w);
                // Flip operator by negating literals
                iter_a = lits.iter().map(neg_lit);
                (
                    &mut iter_a,
                    isize::try_from(weight_sum)
                        .expect("cannot handle weight sum larger than `isize::MAX`")
                        - bound,
                    ">=",
                )
            }
            PbConstraint::Lb(constr) => {
                let (lits, bound) = constr.decompose_ref();
                iter_b = lits.iter().copied();
                (&mut iter_b, *bound, ">=")
            }
            PbConstraint::Eq(constr) => {
                let (lits, bound) = constr.decompose_ref();
                iter_b = lits.iter().copied();
                (&mut iter_b, *bound, "=")
            }
        };
        let mut offset: isize = 0;
        for (l, w) in lits {
            if l.is_pos() {
                write!(writer, "{} x{} ", w, l.vidx32() + opts.first_var_idx)?;
            } else {
                // TODO: consider returning error for usize -> isize cast
                let w = isize::try_from(w).expect("cannot handle weights larger than `isize::MAX`");
                offset += w;
                write!(writer, "{} x{} ", -w, l.vidx32() + opts.first_var_idx)?;
            }
        }
        writeln!(writer, "{} {};", op, bound - offset)
    } else {
        let (lits, bound, op): (&mut dyn Iterator<Item = (Lit, usize)>, _, _) = match pb {
            PbConstraint::Ub(constr) => {
                let (lits, bound) = constr.decompose_ref();
                let weight_sum = lits.iter().fold(0, |sum, (_, w)| sum + w);
                // Flip operator by negating literals
                iter_a = lits.iter().map(neg_lit);
                (
                    &mut iter_a,
                    isize::try_from(weight_sum)
                        .expect("cannot handle weight sum larger than `isize::MAX`")
                        - bound,
                    ">=",
                )
            }
            PbConstraint::Lb(constr) => {
                let (lits, bound) = constr.decompose_ref();
                iter_b = lits.iter().copied();
                (&mut iter_b, *bound, ">=")
            }
            PbConstraint::Eq(constr) => {
                let (lits, bound) = constr.decompose_ref();
                iter_b = lits.iter().copied();
                (&mut iter_b, *bound, "=")
            }
        };
        for (l, w) in lits {
            if l.is_pos() {
                write!(writer, "{} x{} ", w, l.vidx32() + opts.first_var_idx)?;
            } else {
                write!(writer, "{} ~x{} ", w, l.vidx32() + opts.first_var_idx)?;
            }
        }
        writeln!(writer, "{op} {bound};")
    }
}

#[cfg(feature = "optimization")]
/// Writes an objective to an OPB file
///
/// # Errors
///
/// If writing fails, returns [`io::Error`].
fn write_objective<W: Write, LI: crate::types::WLitIter>(
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
                let w = isize::try_from(w).expect("cannot handle weights larger than `isize::MAX`");
                if l.is_neg() {
                    offset += w;
                    (l.var(), -w)
                } else {
                    (l.var(), w)
                }
            })
            .try_for_each(|(v, w)| write!(writer, " {w} x{}", v.idx32() + opts.first_var_idx))?;
    } else {
        soft_lits.into_iter().try_for_each(|(l, w)| {
            if l.is_pos() {
                write!(writer, " {w} x{}", l.vidx32() + opts.first_var_idx)
            } else {
                write!(writer, " {w} ~x{}", l.vidx32() + opts.first_var_idx)
            }
        })?;
    }
    writeln!(writer, ";")?;
    if offset != 0 {
        // OPB does not support offsets in objectives, so we have to add it as a comment
        writeln!(
            writer,
            "* objective offset for previous objective: {offset}",
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
        types::constraints::{CardConstraint, PbConstraint},
        var,
    };
    use nom::error::{Error as NomError, ErrorKind};

    #[cfg(feature = "optimization")]
    use super::{opb_data, parse_opb_data, OpbData};
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
            Ok((" test", var![4]))
        );
        assert_eq!(
            variable(
                "x5 test",
                Options {
                    first_var_idx: 0,
                    no_negated_lits: true
                }
            ),
            Ok((" test", var![5]))
        );
        assert_eq!(
            variable("x2 test", Options::default()),
            Ok((" test", var![1]))
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
            Ok((" test", lit![4]))
        );
        assert_eq!(
            literal("x2 test", Options::default()),
            Ok((" test", lit![1]))
        );
        assert_eq!(
            literal("~x5 test", Options::default()),
            Ok((" test", !lit![4]))
        );
        assert_eq!(
            literal("~x2 test", Options::default()),
            Ok((" test", !lit![1]))
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
            Ok(("test", (lit![0], 5)))
        );
        assert_eq!(
            weighted_literal("-5  x1 test", Options::default()),
            Ok(("test", (lit![0], -5)))
        );
        assert_eq!(
            weighted_literal("5 ~x1  test", Options::default()),
            Ok(("test", (!lit![0], 5)))
        );
        assert_eq!(
            weighted_literal("-5 ~x1 test", Options::default()),
            Ok(("test", (!lit![0], -5)))
        );
    }

    #[test]
    fn parse_weighted_lit_sum() {
        assert_eq!(
            weighted_lit_sum("5  x1    -3 ~x2  test", Options::default()),
            Ok(("test", vec![(lit![0], 5), (!lit![1], -3)]))
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
        if let Ok((rest, PbConstraint::Ub(constr))) =
            constraint("3 x1 -2 ~x2 <= 4;", Options::default())
        {
            assert_eq!(rest, "");
            let (lits, b) = constr.decompose();
            let should_be_lits = vec![(lit![0], 3), (lit![1], 2)];
            assert_eq!(lits, should_be_lits);
            assert_eq!(b, 6);
        } else {
            panic!()
        }
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_objective() {
        if let Ok((rest, obj)) = objective("min: 3 x1 -2 ~x2;", Options::default()) {
            assert_eq!(rest, "");
            let mut should_be_obj = Objective::new();
            should_be_obj.increase_soft_lit_int(3, lit![0]);
            should_be_obj.increase_soft_lit_int(-2, !lit![1]);
            assert_eq!(obj, should_be_obj);
        } else {
            panic!()
        }
        assert!(objective("min: x0;", Options::default())
            .is_err_and(|err| err == nom::Err::Failure(NomError::new("x0;", ErrorKind::Eof))));
        if let Ok((rest, obj)) = objective("min:;", Options::default()) {
            assert_eq!(rest, "");
            let should_be_obj = Objective::new();
            assert_eq!(obj, should_be_obj);
        } else {
            panic!()
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
        let lits = vec![(lit![0], 3), (!lit![1], -2)];
        let should_be_constr = PbConstraint::new_ub(lits, 4);
        assert_eq!(
            opb_data("3 x1 -2 ~x2 <= 4;\n", Options::default()),
            Ok(("", OpbData::Constr(should_be_constr)))
        );
        assert!(opb_data("", Options::default()).is_err_and(|e| matches!(e, nom::Err::Error(_))));
        #[cfg(feature = "optimization")]
        {
            let mut obj = Objective::new();
            obj.increase_soft_lit_int(-3, lit![0]);
            obj.increase_soft_lit_int(4, lit![1]);
            assert_eq!(
                opb_data("min: -3 x1 4 x2;", Options::default()),
                Ok(("", OpbData::Obj(obj)))
            );
            assert_eq!(
                opb_data("min: x1;", Options::default()),
                Err(nom::Err::Failure(NomError::new("x1;", ErrorKind::Eof)))
            );
        }
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn multi_opb_data() {
        let data = "* test\n5 x1 -3 x2 >= 4;\nmin: 1 x1;";
        let reader = Cursor::new(data);
        if let Ok(data) = parse_opb_data(&mut BufReader::new(reader), Options::default()) {
            assert_eq!(data.len(), 3);
            assert_eq!(data[0], OpbData::Cmt(String::from("* test\n")));
            assert!(matches!(data[1], OpbData::Constr(_)));
            assert!(matches!(data[2], OpbData::Obj(_)));
        } else {
            panic!()
        }
        let data = "* test\n5 x1 -3 x2 >= 4;\nmin: x1;";
        let reader = Cursor::new(data);
        assert!(parse_opb_data(&mut BufReader::new(reader), Options::default()).is_err());
    }

    #[test]
    fn write_parse_clause() {
        let cl = clause![!lit![0], lit![1], !lit![2]];

        let mut cursor = Cursor::new(vec![]);

        write_clause(&mut cursor, &cl, Options::default()).unwrap();

        cursor.rewind().unwrap();

        let (cnf, _) = super::parse_sat::<_, BasicVarManager>(&mut cursor, Options::default())
            .unwrap()
            .into_cnf();

        assert_eq!(cnf.len(), 1);
        assert_eq!(cnf.into_iter().next().unwrap().normalize(), cl.normalize());
    }

    fn write_parse_inst_test(in_inst: &SatInstance, true_inst: SatInstance, opts: Options) {
        let mut cursor = Cursor::new(vec![]);

        write_sat(&mut cursor, in_inst, opts).unwrap();

        cursor.rewind().unwrap();

        let parsed_inst: SatInstance = super::parse_sat(&mut cursor, opts).unwrap();

        let (parsed_cnf, parsed_vm) = parsed_inst.into_cnf();
        let (true_cnf, true_vm) = true_inst.into_cnf();

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
        true_inst.add_pb_constr(PbConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, Options::default());

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_eq(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, Options::default());

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_lb(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, Options::default());
    }

    #[test]
    fn write_parse_card_neg_lits() {
        // Note: this test is known to fail _sometimes_ without feature "fxhash".
        // This is due to the non-deterministic default hash function.

        // Since the hash map of going through a pb constraint at parsing
        // reorders the literals, the true instance has to go through a pb
        // constraint as well.
        let lits = vec![(!lit![3], 1), (lit![4], 1), (!lit![5], 1)];

        let alt_opb_opts = Options {
            no_negated_lits: false,
            ..Default::default()
        };

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_ub(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, alt_opb_opts);

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_eq(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, alt_opb_opts);

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_lb(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, alt_opb_opts);
    }

    #[test]
    fn write_parse_pb() {
        let lits = vec![(!lit![6], 3), (!lit![7], -5), (lit![8], 2), (lit![9], -4)];

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(&true_inst, true_inst.clone(), Options::default());

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(&true_inst, true_inst.clone(), Options::default());

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(&true_inst, true_inst.clone(), Options::default());
    }

    #[test]
    fn write_parse_pb_neg_lits() {
        let lits = vec![(!lit![6], 3), (!lit![7], -5), (lit![8], 2), (lit![9], -4)];

        let alt_opb_opts = Options {
            no_negated_lits: false,
            ..Default::default()
        };

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(&true_inst, true_inst.clone(), alt_opb_opts);

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(&true_inst, true_inst.clone(), alt_opb_opts);

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(&true_inst, true_inst.clone(), alt_opb_opts);
    }
}
