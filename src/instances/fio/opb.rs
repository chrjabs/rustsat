//! # Parsing OPB Files
//!
//! Internal module containing functions for parsing linear OPB files.
//! The approach is to accept input instances, even if they are not technically
//! in spec, as long as the input is still reasonable.
//!
//! ## References
//!
//! - [OPB](https://www.cril.univ-artois.fr/PB12/format.pdf)

use std::io::{self, BufRead, Write};

use winnow::{
    ascii::{dec_int, digit0, line_ending, space0, space1, till_line_ending},
    combinator::{alt, cut_err, dispatch, empty, eof, opt, preceded, repeat, seq},
    error::{ContextError, ErrMode, StrContext},
    token::one_of,
    ModalResult, Parser as WParser,
};

use crate::{
    instances::{ManageVars, SatInstance},
    types::{
        constraints::{CardConstraint, PbConstraint},
        Cl, Clause, Lit, Var,
    },
    utils,
};

#[cfg(feature = "multiopt")]
use crate::instances::MultiOptInstance;
#[cfg(feature = "optimization")]
use crate::instances::{Objective, OptInstance};

use super::ParsingError;

/// An OPB parser as an iterator over [`OpbData`] in a given file
pub struct Parser<R> {
    reader: io::BufReader<R>,
    buffer: String,
    opts: Options,
}

impl<R: io::Read> Parser<R> {
    /// Create a parser from a reader
    pub fn new(reader: R, opts: Options) -> Self {
        Parser {
            reader: io::BufReader::new(reader),
            buffer: String::new(),
            opts,
        }
    }

    /// Create a parser from an existing [`io::BufReader`]
    pub fn new_pre_buffered(reader: io::BufReader<R>, opts: Options) -> Self {
        Parser {
            reader,
            buffer: String::new(),
            opts,
        }
    }

    /// Unwraps this parser, returning the underlying reader
    pub fn into_inner(self) -> R {
        self.reader.into_inner()
    }

    /// Unwraps this parser, returning the underlying buffered reader
    pub fn into_buffered_inner(self) -> io::BufReader<R> {
        self.reader
    }
}

impl<R: io::Read> Iterator for Parser<R> {
    type Item = Result<Data, super::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.is_empty() {
            match self.reader.read_line(&mut self.buffer) {
                Err(e) => return Some(Err(super::Error::Io(e))),
                Ok(0) => return None,
                Ok(_) => {}
            }
        }
        let mut stream = self.buffer.as_str();
        let data = match opb_data(self.opts).parse_next(&mut stream) {
            Ok(data) => data,
            Err(e) => {
                return Some(Err(super::Error::Parsing(ParsingError::from_err_mode(
                    e,
                    &self.buffer,
                    utils::substr_offset(&self.buffer, stream).unwrap(),
                ))))
            }
        };
        self.buffer
            .drain(..utils::substr_offset(&self.buffer, stream).unwrap());
        Some(Ok(data))
    }
}

/// Trait for parsers used in this module
pub(crate) trait OpbParser<'i, O>:
    WParser<&'i str, O, ErrMode<ContextError<StrContext>>>
{
}

impl<'i, P, O> OpbParser<'i, O> for P where P: WParser<&'i str, O, ErrMode<ContextError<StrContext>>>
{}

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
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
pub enum Data {
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

impl Data {
    /// Unwraps the PB constraint, if it is one
    #[must_use]
    pub fn constraint(self) -> Option<PbConstraint> {
        match self {
            Data::Constr(constr) => Some(constr),
            _ => None,
        }
    }
}

/// Parsing errors that can occurr
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    /// A variable index appearing in the parsed data is lower than the specified lowest index
    #[error("found variable with index {0}, which is lower than lowest index {1}")]
    VarIdxTooLow(u32, u32),
}

/// Parses the constraints from an OPB file as a [`SatInstance`]
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
pub fn parse_sat<R, VM>(reader: &mut R, opts: Options) -> Result<SatInstance<VM>, super::Error>
where
    R: io::Read,
    VM: ManageVars + Default,
{
    Parser::new(reader, opts).collect()
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
) -> Result<OptInstance<VM>, super::Error>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    let parser = Parser::new(reader, opts);
    let mut sat_inst = SatInstance::<VM>::new();
    let mut obj_cnt = 0;
    let mut obj = None;
    for data in parser {
        match data? {
            Data::Cmt(_) => {}
            Data::Constr(constr) => sat_inst.add_pb_constr(constr),
            Data::Obj(objective) => {
                if obj_cnt == obj_idx {
                    obj = Some(objective);
                }
                obj_cnt += 1;
            }
        }
    }
    let Some(obj) = obj else {
        return Err(super::Error::ObjNoExist(obj_cnt));
    };
    Ok(OptInstance::compose(sat_inst, obj))
}

#[cfg(feature = "multiopt")]
/// Parses an OPB file as an [`MultiOptInstance`] using the objective with the given
/// index (starting from 0).
///
/// # Errors
///
/// Parsing errors or [`io::Error`].
pub fn parse_multi_opt<R, VM>(
    reader: &mut R,
    opts: Options,
) -> Result<MultiOptInstance<VM>, super::Error>
where
    R: BufRead,
    VM: ManageVars + Default,
{
    Parser::new(reader, opts).collect()
}

/// Matches an OPB comment
fn comment<'i>(input: &mut &'i str) -> ModalResult<&'i str> {
    seq! { '*', till_line_ending, opt(line_ending) }
        .take()
        .parse_next(input)
}

/// Parser for variables with a given minimum variable index
struct VarParser(u32);

impl VarParser {
    fn new(opts: Options) -> Self {
        VarParser(opts.first_var_idx)
    }
}

impl<'i, E> WParser<&'i str, Var, E> for VarParser
where
    E: winnow::error::ParserError<&'i str>
        + winnow::error::AddContext<&'i str, winnow::error::StrContext>
        + winnow::error::FromExternalError<&'i str, Error>
        + winnow::error::FromExternalError<&'i str, <u32 as std::str::FromStr>::Err>,
{
    fn parse_next(&mut self, input: &mut &'i str) -> winnow::Result<Var, E> {
        // NOTE: manual implementation for the index following `dec_uint` in order to not allow
        // signs
        preceded(
            'x'.context(StrContext::Label("variable prefix")),
            alt(((one_of('1'..='9'), digit0).void(), '0'.void())),
        )
        .take()
        .try_map(str::parse)
        .context(StrContext::Label("variable index"))
        .try_map(|idx| {
            if idx < self.0 {
                return Err(Error::VarIdxTooLow(idx, self.0));
            }
            Ok(Var::new(idx - self.0))
        })
        .context(StrContext::Label("variable"))
        .parse_next(input)
    }
}

/// Generates a parser for literals with a given minimum variable index. The spec for linear OPB
/// instances only allows for variables but we allow negated literals with `~` as in non-linear OPB
/// instances.
pub(crate) fn literal<'i>(opts: Options) -> impl OpbParser<'i, Lit> {
    let neg = opt(alt(('~', '-'))).map(|opt| opt.is_some());
    (neg, VarParser::new(opts)).map(|(neg, var)| var.lit(neg))
}

/// Parses an OPB relational operator. We admit more operators than the spec.
fn operator(input: &mut &str) -> ModalResult<OpbOperator> {
    dispatch! {alt(("<=", ">=", "<", ">", "="));
        "<=" => empty.value(OpbOperator::LE),
        ">=" => empty.value(OpbOperator::GE),
        "<" => empty.value(OpbOperator::LT),
        ">" => empty.value(OpbOperator::GT),
        _ => empty.value(OpbOperator::EQ),
    }
    .parse_next(input)
}

/// Parses an OPB weight
fn coeff(input: &mut &str) -> ModalResult<isize> {
    dec_int
        .context(StrContext::Label("coefficient"))
        .parse_next(input)
}

/// Parses an OPB weighted term
fn term<'i>(opts: Options) -> impl OpbParser<'i, (Lit, isize)> {
    seq! { coeff, _: space1, literal(opts), _: space0 }.map(|(c, l)| (l, c))
}

/// Parses an OPB sum
fn term_sum<'i, Accumulator>(opts: Options) -> impl OpbParser<'i, Accumulator>
where
    Accumulator: winnow::stream::Accumulate<(Lit, isize)>,
{
    repeat(1.., term(opts))
}

/// Parses a (potentially empty) OPB sum
fn term_sum0<'i, Accumulator>(opts: Options) -> impl OpbParser<'i, Accumulator>
where
    Accumulator: winnow::stream::Accumulate<(Lit, isize)>,
{
    repeat(0.., term(opts))
}

/// Leniently parses OPB constraint or objective ending as ';' or a line ending
fn ending<'i>(input: &mut &'i str) -> ModalResult<&'i str> {
    (
        space0,
        opt(';'),
        space0,
        opt(alt((eof, (line_ending, space0).take()))),
    )
        .verify(|p| p.1.is_some() || p.3.is_some())
        .take()
        .parse_next(input)
}

/// Parses an OPB constraint
fn constraint<'i>(opts: Options) -> impl OpbParser<'i, PbConstraint> {
    seq! { term_sum::<Vec<(Lit, isize)>>(opts), cut_err(operator), _: space0, cut_err(coeff), _: ending }.map(
        |(sum, opt, b)| match opt {
            OpbOperator::LE => PbConstraint::new_ub(sum, b),
            OpbOperator::GE => PbConstraint::new_lb(sum, b),
            OpbOperator::LT => PbConstraint::new_ub(sum, b + 1),
            OpbOperator::GT => PbConstraint::new_lb(sum, b + 1),
            OpbOperator::EQ => PbConstraint::new_eq(sum, b),
        },
    )
}

#[cfg(feature = "optimization")]
/// Parses an OPB objective
fn objective<'i>(opts: Options) -> impl OpbParser<'i, Objective> {
    seq! { _: "min:", _: space0, cut_err(term_sum0::<Objective>(opts)), _: cut_err(ending) }
        .map(|(o,)| o)
        .context(StrContext::Label("objective"))
}

#[cfg(not(feature = "optimization"))]
/// Matches an OPB objective
fn objective<'i>(opts: Options) -> impl OpbParser<'i, &'i str> {
    (
        "min:",
        space0,
        cut_err(term_sum0::<()>(opts)),
        cut_err(ending),
    )
        .take()
        .context(StrContext::Label("objective"))
}

/// Top level string parser applied to lines
fn opb_data<'i>(opts: Options) -> impl OpbParser<'i, Data> {
    #[cfg(feature = "optimization")]
    let parser = seq! {
    _: space0,
    alt((
        comment.map(|c| Data::Cmt(c.to_owned())),
        constraint(opts).map(Data::Constr),
        objective(opts).map(Data::Obj)
    )).context(StrContext::Label("comment/constraint/objective")) };
    #[cfg(not(feature = "optimization"))]
    let parser = seq! {
    _: space0,
    alt((
        comment.map(|c| Data::Cmt(c.to_owned())),
        constraint(opts).map(Data::Constr),
        objective(opts).map(|o| Data::Obj(o.to_owned()))
    )).context(StrContext::Label("comment/constraint/objective")) };
    parser.map(|(d,)| d)
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

    use winnow::{error::ContextError, Parser as WParser};

    use crate::{
        clause,
        instances::{BasicVarManager, SatInstance},
        lit,
        types::{
            constraints::{CardConstraint, PbConstraint},
            Var,
        },
        var,
    };

    use super::{
        coeff, comment, constraint, ending, literal, objective, operator, term, term_sum,
        write_clause, write_sat, OpbOperator, Options, Parser, VarParser,
    };

    #[cfg(feature = "optimization")]
    use super::{opb_data, Data};
    #[cfg(feature = "optimization")]
    use crate::instances::Objective;

    #[test]
    fn match_comment() {
        assert_eq!(comment.parse_peek("* test\n"), Ok(("", "* test\n")));
        assert_eq!(comment.parse_peek("* test"), Ok(("", "* test")));
        assert_eq!(comment.parse_peek("*\n"), Ok(("", "*\n")));

        assert!(comment.parse_peek(" test\n").is_err());
    }

    #[test]
    fn parse_variable() {
        assert_eq!(
            VarParser(Options::default().first_var_idx).parse_peek("x5 test"),
            Ok::<(&str, Var), ContextError<_>>((" test", var![4]))
        );
        assert_eq!(
            VarParser(0).parse_peek("x5 test"),
            Ok::<(&str, Var), ContextError<_>>((" test", var![5]))
        );
        assert_eq!(
            VarParser(Options::default().first_var_idx).parse_peek("x2 test"),
            Ok::<(&str, Var), ContextError<_>>((" test", var![1]))
        );

        let mut parser = VarParser(Options::default().first_var_idx);
        assert!(
            <VarParser as WParser<&str, Var, ContextError<_>>>::parse_peek(&mut parser, " test")
                .is_err()
        );
        assert!(
            <VarParser as WParser<&str, Var, ContextError<_>>>::parse_peek(&mut parser, "x+1 test")
                .is_err()
        );
    }

    #[test]
    fn parse_literal() {
        assert_eq!(
            literal(Options::default()).parse_peek("x5 test"),
            Ok((" test", lit![4]))
        );
        assert_eq!(
            literal(Options::default()).parse_peek("x2 test"),
            Ok((" test", lit![1]))
        );
        assert_eq!(
            literal(Options::default()).parse_peek("~x5 test"),
            Ok((" test", !lit![4]))
        );
        assert_eq!(
            literal(Options::default()).parse_peek("~x2 test"),
            Ok((" test", !lit![1]))
        );
    }

    #[test]
    fn parse_operator() {
        assert_eq!(
            operator.parse_peek("<= test"),
            Ok((" test", OpbOperator::LE))
        );
        assert_eq!(
            operator.parse_peek(">= test"),
            Ok((" test", OpbOperator::GE))
        );
        assert_eq!(
            operator.parse_peek("< test"),
            Ok((" test", OpbOperator::LT))
        );
        assert_eq!(
            operator.parse_peek("> test"),
            Ok((" test", OpbOperator::GT))
        );
        assert_eq!(
            operator.parse_peek("= test"),
            Ok((" test", OpbOperator::EQ))
        );
    }

    #[test]
    fn parse_weight() {
        assert_eq!(coeff.parse_peek("5 test"), Ok((" test", 5)));
        assert_eq!(coeff.parse_peek("+5 test"), Ok((" test", 5)));
        assert_eq!(coeff.parse_peek("-5 test"), Ok((" test", -5)));
    }

    #[test]
    fn parse_weighted_literal() {
        assert_eq!(
            term(Options::default()).parse_peek("5 x1 test"),
            Ok(("test", (lit![0], 5)))
        );
        assert_eq!(
            term(Options::default()).parse_peek("-5  x1 test"),
            Ok(("test", (lit![0], -5)))
        );
        assert_eq!(
            term(Options::default()).parse_peek("5 ~x1  test"),
            Ok(("test", (!lit![0], 5)))
        );
        assert_eq!(
            term(Options::default()).parse_peek("-5 ~x1 test"),
            Ok(("test", (!lit![0], -5)))
        );
    }

    #[test]
    fn parse_weighted_lit_sum() {
        assert_eq!(
            term_sum(Options::default()).parse_peek("5  x1    -3 ~x2  test"),
            Ok(("test", vec![(lit![0], 5), (!lit![1], -3)]))
        );
    }

    #[test]
    fn parse_opb_ending() {
        assert_eq!(ending.parse_peek("   ; test"), Ok(("test", "   ; ")));
        assert_eq!(ending.parse_peek("   \n test"), Ok(("test", "   \n ")));
        assert_eq!(ending.parse_peek("  ; \n test"), Ok(("test", "  ; \n ")));
        assert_eq!(ending.parse_peek("  "), Ok(("", "  ")));
    }

    #[test]
    fn parse_constraint() {
        if let Ok((rest, PbConstraint::Ub(constr))) =
            constraint(Options::default()).parse_peek("3 x1 -2 ~x2 <= 4;")
        {
            assert_eq!(rest, "");
            let (lits, b) = constr.decompose();
            let should_be_lits = vec![(lit![0], 3), (lit![1], 2)];
            assert_eq!(lits, should_be_lits);
            assert_eq!(b, 6);
        } else {
            panic!();
        }
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn parse_objective() {
        let (rest, obj) = objective(Options::default())
            .parse_peek("min: 3 x1 -2 ~x2;")
            .unwrap();
        assert_eq!(rest, "");
        let mut should_be_obj = Objective::new();
        should_be_obj.increase_soft_lit_int(3, lit![0]);
        should_be_obj.increase_soft_lit_int(-2, !lit![1]);
        assert_eq!(obj, should_be_obj);

        assert!(objective(Options::default())
            .parse_peek("min: x0;")
            .is_err());

        let (rest, obj) = objective(Options::default()).parse_peek("min:;").unwrap();
        assert_eq!(rest, "");
        let should_be_obj = Objective::new();
        assert_eq!(obj, should_be_obj);
    }

    #[cfg(not(feature = "optimization"))]
    #[test]
    fn parse_objective() {
        assert_eq!(
            objective(Options::default()).parse_peek("min: 3 x1 -2 ~x2;"),
            Ok(("", "min: 3 x1 -2 ~x2;"))
        );
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn single_opb_data() {
        assert_eq!(
            opb_data(Options::default()).parse_peek("* test\n"),
            Ok(("", Data::Cmt(String::from("* test\n"))))
        );
        let lits = vec![(lit![0], 3), (!lit![1], -2)];
        let should_be_constr = PbConstraint::new_ub(lits, 4);
        assert_eq!(
            opb_data(Options::default()).parse_peek("3 x1 -2 ~x2 <= 4;\n"),
            Ok(("", Data::Constr(should_be_constr)))
        );
        assert!(opb_data(Options::default()).parse_peek("").is_err());
        #[cfg(feature = "optimization")]
        {
            let mut obj = Objective::new();
            obj.increase_soft_lit_int(-3, lit![0]);
            obj.increase_soft_lit_int(4, lit![1]);
            assert_eq!(
                opb_data(Options::default()).parse_peek("min: -3 x1 4 x2;"),
                Ok(("", Data::Obj(obj)))
            );
            assert!(opb_data(Options::default()).parse_peek("min: x1;").is_err());
        }
    }

    #[cfg(feature = "optimization")]
    #[test]
    fn multi_opb_data() {
        let data = "* test\n5 x1 -3 x2 >= 4;\nmin: 1 x1;";

        let parser = Parser::new(Cursor::new(data), Options::default());
        let data = parser.collect::<Result<Vec<_>, _>>().unwrap();
        assert_eq!(data.len(), 3);
        assert_eq!(data[0], Data::Cmt(String::from("* test\n")));
        assert!(matches!(data[1], Data::Constr(_)));
        assert!(matches!(data[2], Data::Obj(_)));

        let data = "* test\n5 x1 -3 x2 >= 4;\nmin: x1;";
        let parser = Parser::new(Cursor::new(data), Options::default());
        assert!(parser.collect::<Result<Vec<_>, _>>().is_err());
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
        in_inst.add_card_constr(CardConstraint::new_ub([!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, Options::default());

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_eq([!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, Options::default());

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_lb([!lit![3], lit![4], !lit![5]], 2));
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
        in_inst.add_card_constr(CardConstraint::new_ub([!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, alt_opb_opts);

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_eq([!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PbConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(&in_inst, true_inst, alt_opb_opts);

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_lb([!lit![3], lit![4], !lit![5]], 2));
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
