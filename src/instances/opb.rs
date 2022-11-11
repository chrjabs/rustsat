//! # Parsing OPB Files
//!
//! Internal module containing functions for parsing linear OPB files.
//! The approach is to accept input instances, even if they are not technically
//! in spec, as long as the input is still reasonable.
//!
//! ## References
//!
//! - [OPB](https://www.cril.univ-artois.fr/PB12/format.pdf)

use super::{ManageVars, SatInstance};
use crate::types::{
    constraints::{CardConstraint, PBConstraint},
    Clause, Lit, RsHashMap, Var,
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{anychar, i64, line_ending, space0, space1, u64},
    combinator::{map_res, opt, recognize},
    error::Error,
    multi::{many0, many1, many_till},
    sequence::{pair, tuple},
    IResult,
};
use std::{
    fmt,
    io::{self, BufRead, BufReader, Read, Write},
    num::TryFromIntError,
};

#[cfg(feature = "multiopt")]
use super::MultiOptInstance;
#[cfg(feature = "optimization")]
use super::{Objective, OptInstance, SoftLitsOffset};

/// Errors occuring within the OPB parsing module
#[derive(Debug, PartialEq, Eq)]
pub enum OpbError {
    /// The requested objective does not exist
    ObjectiveNotFound,
    /// Encountered an unexpected line in the OPB file
    InvalidLine(String),
    /// Error while reading input data
    IOError,
}

impl fmt::Display for OpbError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OpbError::ObjectiveNotFound => write!(f, "No matching objective found in file"),
            OpbError::InvalidLine(line) => write!(f, "Invalid OPB line: {}", line),
            OpbError::IOError => write!(f, "Encountered error reading file"),
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
pub fn parse_sat<R: Read>(reader: R) -> Result<SatInstance, OpbError> {
    let data = parse_opb_data(reader)?;
    let mut inst = SatInstance::new();
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
pub fn parse_opt_with_idx<R: Read>(reader: R, obj_idx: usize) -> Result<OptInstance, OpbError> {
    let data = parse_opb_data(reader)?;
    let mut sat_inst = SatInstance::new();
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
        Err(OpbError::ObjectiveNotFound)
    } else {
        Ok(OptInstance::compose(sat_inst, obj))
    }
}

#[cfg(feature = "multiopt")]
/// Parses an OPB file as an [`OptInstance`] using the objective with the given
/// index (starting from 0).
pub fn parse_multi_opt<R: Read>(reader: R) -> Result<MultiOptInstance, OpbError> {
    let data = parse_opb_data(reader)?;
    let mut sat_inst = SatInstance::new();
    let mut objs = vec![];
    data.into_iter().for_each(|d| match d {
        OpbData::Cmt(_) => (),
        OpbData::Constr(constr) => sat_inst.add_pb_constr(constr),
        OpbData::Obj(obj) => objs.push(obj),
    });
    Ok(MultiOptInstance::compose(sat_inst, objs))
}

/// Parses all OPB data of a reader
fn parse_opb_data<R: Read>(reader: R) -> Result<Vec<OpbData>, OpbError> {
    let mut reader = BufReader::new(reader);
    let mut buf = String::new();
    let mut data = vec![];
    while let Ok(len) = reader.read_line(&mut buf) {
        if len == 0 {
            return Ok(data);
        }
        match many0(opb_data)(&buf) {
            Ok((rem, new_data)) => {
                if !rem.is_empty() {
                    return Err(OpbError::InvalidLine(buf.clone()));
                } else {
                    data.extend(new_data)
                }
            }
            Err(_) => return Err(OpbError::InvalidLine(buf.clone())),
        }
        buf.clear();
    }
    Err(OpbError::IOError)
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
fn variable(input: &str) -> IResult<&str, Var> {
    let (input, _) = tag("x")(input)?;
    map_res(u64, |idx| {
        let idx = idx.try_into()?;
        Ok::<Var, TryFromIntError>(Var::new(idx))
    })(input)
}

/// Parses a literal. The spec for linear OPB instances only allows for
/// variables but we allow negated literals with '~' as in non-linear OPB
/// instances.
fn literal(input: &str) -> IResult<&str, Lit> {
    match tag::<_, _, Error<_>>("~")(input) {
        Ok((input, _)) => map_res(variable, |v| Ok::<_, ()>(v.neg_lit()))(input),
        Err(_) => map_res(variable, |v| Ok::<_, ()>(v.pos_lit()))(input),
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
fn weighted_literal(input: &str) -> IResult<&str, (Lit, isize)> {
    map_res(tuple((weight, space1, literal, space0)), |(w, _, l, _)| {
        Ok::<_, ()>((l, w))
    })(input)
}

/// Parses an OPB sum
fn weighted_lit_sum(input: &str) -> IResult<&str, Vec<(Lit, isize)>> {
    many1(weighted_literal)(input)
}

/// Leniently parses OPB constraint or objective ending as ';' or a line ending
fn opb_ending(input: &str) -> IResult<&str, &str> {
    recognize(pair(
        space0,
        opt(pair(
            alt((
                recognize(tuple((tag(";"), space0, line_ending))),
                line_ending,
                tag(";"),
            )),
            space0,
        )),
    ))(input)
}

/// Parses an OPB constraint
fn constraint(input: &str) -> IResult<&str, PBConstraint> {
    map_res(
        tuple((weighted_lit_sum, operator, space0, weight, opb_ending)),
        |(wls, op, _, b, _)| {
            let lits = RsHashMap::from_iter(wls.into_iter());
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
fn objective(input: &str) -> IResult<&str, Objective> {
    map_res(
        tuple((tag("min:"), space0, weighted_lit_sum, opb_ending)),
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
fn objective(input: &str) -> IResult<&str, &str> {
    recognize(tuple((tag("min:"), space0, weighted_lit_sum, opb_ending)))(input)
}

/// Top level string parser applied to lines
fn opb_data(input: &str) -> IResult<&str, OpbData> {
    alt((
        map_res(comment, |cmt| Ok::<_, ()>(OpbData::Cmt(String::from(cmt)))),
        map_res(constraint, |constr| Ok::<_, ()>(OpbData::Constr(constr))),
        #[cfg(feature = "optimization")]
        map_res(objective, |obj| Ok::<_, ()>(OpbData::Obj(obj))),
        #[cfg(not(feature = "optimization"))]
        map_res(objective, |obj| {
            Ok::<_, ()>(OpbData::Obj(String::from(obj)))
        }),
    ))(input)
}

/// Writes a [`SatInstance`] to an OPB file
pub fn write_sat<W: Write, VM: ManageVars>(
    writer: &mut W,
    mut inst: SatInstance<VM>,
) -> Result<(), io::Error> {
    writeln!(writer, "* OPB file written by RustSAT")?;
    writeln!(
        writer,
        "* maximum variable: {}",
        inst.var_manager.next_free() - 1
    )?;
    writeln!(writer, "* {} clauses", inst.n_clauses())?;
    writeln!(writer, "* {} cardinality constraints", inst.cards.len())?;
    writeln!(writer, "* {} pseudo-boolean constraints", inst.pbs.len())?;
    inst.cnf
        .into_iter()
        .try_for_each(|cl| write_clause(writer, cl))?;
    inst.cards
        .into_iter()
        .try_for_each(|card| write_card(writer, card))?;
    inst.pbs
        .into_iter()
        .try_for_each(|pb| write_pb(writer, pb))?;
    writer.flush()
}

#[cfg(feature = "optimization")]
/// Writes an [`OptInstance`] to an OPB file
pub fn write_opt<W: Write, VM: ManageVars>(
    writer: &mut W,
    inst: OptInstance<VM>,
) -> Result<(), io::Error> {
    let (constrs, obj) = inst.decompose();
    let cnf = constrs.cnf;
    let cards = constrs.cards;
    let pbs = constrs.pbs;
    let mut vm = constrs.var_manager;
    let (hardened, softs) = obj.as_soft_lits(&mut vm);
    writeln!(writer, "* OPB file written by RustSAT")?;
    writeln!(writer, "* maximum variable: {}", vm.next_free() - 1)?;
    writeln!(writer, "* {} original hard clauses", cnf.n_clauses())?;
    writeln!(writer, "* {} cardinality constraints", cards.len())?;
    writeln!(writer, "* {} pseudo-boolean constraints", pbs.len())?;
    writeln!(
        writer,
        "* {} relaxed and hardened soft clauses",
        hardened.n_clauses()
    )?;
    write_objective(writer, softs)?;
    hardened
        .into_iter()
        .try_for_each(|cl| write_clause(writer, cl))?;
    cnf.into_iter()
        .try_for_each(|cl| write_clause(writer, cl))?;
    cards
        .into_iter()
        .try_for_each(|card| write_card(writer, card))?;
    pbs.into_iter().try_for_each(|pb| write_pb(writer, pb))?;
    writer.flush()
}

#[cfg(feature = "multiopt")]
/// Writes a [`MultiOptInstance`] to an OPB file
pub fn write_multi_opt<W: Write, VM: ManageVars>(
    writer: &mut W,
    inst: MultiOptInstance<VM>,
) -> Result<(), io::Error> {
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
    writeln!(writer, "* maximum variable: {}", vm.next_free() - 1)?;
    writeln!(writer, "* {} original hard clauses", cnf.n_clauses())?;
    writeln!(writer, "* {} cardinality constraints", cards.len())?;
    writeln!(writer, "* {} pseudo-boolean constraints", pbs.len())?;
    write!(writer, "* ( ")?;
    hardened
        .iter()
        .try_for_each(|h| write!(writer, "{} ", h.n_clauses()))?;
    writeln!(writer, ") relaxed and hardened soft clauses",)?;
    objs.into_iter()
        .try_for_each(|softs| write_objective(writer, softs))?;
    hardened
        .into_iter()
        .try_for_each(|h| h.into_iter().try_for_each(|cl| write_clause(writer, cl)))?;
    cnf.into_iter()
        .try_for_each(|cl| write_clause(writer, cl))?;
    cards
        .into_iter()
        .try_for_each(|card| write_card(writer, card))?;
    pbs.into_iter().try_for_each(|pb| write_pb(writer, pb))?;
    writer.flush()
}

/// Writes a clause to an OPB file
fn write_clause<W: Write>(writer: &mut W, clause: Clause) -> Result<(), io::Error> {
    let mut rhs: isize = 1;
    clause.into_iter().try_for_each(|l| {
        if l.is_pos() {
            write!(writer, "1 x{} ", l.vidx())
        } else {
            rhs -= 1;
            write!(writer, "-1 x{} ", l.vidx())
        }
    })?;
    writeln!(writer, ">= {};", rhs)
}

/// Writes a cardinality constraint to an OPB file
fn write_card<W: Write>(writer: &mut W, card: CardConstraint) -> Result<(), io::Error> {
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
            write!(writer, "1 x{} ", l.vidx())
        } else {
            offset += 1;
            write!(writer, "-1 x{} ", l.vidx())
        }
    })?;
    writeln!(writer, "{} {};", op, bound as isize - offset)
}

/// Writes a pseudo-boolean constraint to an OPB file
fn write_pb<W: Write>(writer: &mut W, pb: PBConstraint) -> Result<(), io::Error> {
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
            write!(writer, "{} x{} ", w, l.vidx())
        } else {
            // TODO: consider returning error for usize -> isize cast
            let w = w as isize;
            offset += w;
            write!(writer, "{} x{} ", -w, l.vidx())
        }
    })?;
    writeln!(writer, "{} {};", op, bound - offset)
}

#[cfg(feature = "optimization")]
fn write_objective<W: Write>(writer: &mut W, softs: SoftLitsOffset) -> Result<(), io::Error> {
    let (soft_lits, mut offset) = softs;
    write!(writer, "min:")?;
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
        .try_for_each(|(v, w)| write!(writer, " {} {}", v.idx(), w))?;
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
    use std::io::{BufReader, Cursor, Seek};

    use super::{
        comment, constraint, literal, objective, opb_data, opb_ending, operator, parse_opb_data,
        variable, weight, weighted_lit_sum, weighted_literal, write_clause, OpbData, OpbError,
        OpbOperator,
    };
    use crate::{
        clause,
        instances::{opb::write_sat, Objective, SatInstance},
        lit,
        types::{
            constraints::{CardConstraint, PBConstraint},
            Clause, Lit, RsHashMap, Var,
        },
        var,
    };
    use nom::error::{Error, ErrorKind};

    #[test]
    fn match_comment() {
        assert_eq!(comment("* test\n"), Ok(("", "* test\n")));
        assert_eq!(comment("* test"), Ok(("", "* test")));
        assert_eq!(comment("*\n"), Ok(("", "*\n")));
        assert_eq!(
            comment(" test\n"),
            Err(nom::Err::Error(Error::new(" test\n", ErrorKind::Tag)))
        );
    }

    #[test]
    fn parse_variable() {
        assert_eq!(variable("x5 test"), Ok((" test", var![5])));
        assert_eq!(variable("x2 test"), Ok((" test", var![2])));
        assert_eq!(
            variable(" test\n"),
            Err(nom::Err::Error(Error::new(" test\n", ErrorKind::Tag)))
        );
    }

    #[test]
    fn parse_literal() {
        assert_eq!(literal("x5 test"), Ok((" test", lit![5])));
        assert_eq!(literal("x2 test"), Ok((" test", lit![2])));
        assert_eq!(literal("~x5 test"), Ok((" test", !lit![5])));
        assert_eq!(literal("~x2 test"), Ok((" test", !lit![2])));
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
        assert_eq!(weighted_literal("5 x1 test"), Ok(("test", (lit![1], 5))));
        assert_eq!(weighted_literal("-5  x1 test"), Ok(("test", (lit![1], -5))));
        assert_eq!(weighted_literal("5 ~x1  test"), Ok(("test", (!lit![1], 5))));
        assert_eq!(
            weighted_literal("-5 ~x1 test"),
            Ok(("test", (!lit![1], -5)))
        );
    }

    #[test]
    fn parse_weighted_lit_sum() {
        assert_eq!(
            weighted_lit_sum("5  x1    -3 ~x2  test"),
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
        match constraint("3 x1 -2 ~x2 <= 4;") {
            Ok((rest, constr)) => match constr {
                PBConstraint::UB(constr) => {
                    assert_eq!(rest, "");
                    let (lits, b) = constr.decompose();
                    let mut should_be_lits = RsHashMap::default();
                    should_be_lits.insert(lit![1], 3);
                    should_be_lits.insert(lit![2], 2);
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
        match objective("min: 3 x1 -2 ~x2;") {
            Ok((rest, obj)) => {
                assert_eq!(rest, "");
                let mut should_be_obj = Objective::new();
                should_be_obj.increase_soft_lit_int(3, lit![1]);
                should_be_obj.increase_soft_lit_int(-2, !lit![2]);
                assert_eq!(obj, should_be_obj);
            }
            Err(_) => panic!(),
        }
        match objective("min: x0;") {
            Ok(_) => panic!(),
            Err(err) => assert_eq!(err, nom::Err::Error(Error::new("x0;", ErrorKind::Digit))),
        }
    }

    #[cfg(not(feature = "optimization"))]
    #[test]
    fn parse_objective() {
        assert_eq!(objective("min: 3 x1 -2 ~x2;"), Ok(("", "min: 3 x1 -2 ~x2")));
    }

    #[test]
    fn single_opb_data() {
        assert_eq!(
            opb_data("* test\n"),
            Ok(("", OpbData::Cmt(String::from("* test\n"))))
        );
        let mut lits = RsHashMap::default();
        lits.insert(lit![1], 3);
        lits.insert(!lit![2], -2);
        let should_be_constr = PBConstraint::new_ub(lits, 4);
        assert_eq!(
            opb_data("3 x1 -2 ~x2 <= 4;\n"),
            Ok(("", OpbData::Constr(should_be_constr)))
        );
        let mut obj = Objective::new();
        obj.increase_soft_lit_int(-3, lit![0]);
        obj.increase_soft_lit_int(4, lit![1]);
        assert_eq!(opb_data("min: -3 x0 4 x1;"), Ok(("", OpbData::Obj(obj))));
        assert_eq!(
            opb_data("min: x0;"),
            Err(nom::Err::Error(Error::new("x0;", ErrorKind::Digit)))
        );
    }

    #[test]
    fn multi_opb_data() {
        let data = "* test\n5 x0 -3 x1 >= 4;\nmin: 1 x0;";
        let reader = Cursor::new(data);
        let reader = BufReader::new(reader);
        match parse_opb_data(reader) {
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
            parse_opb_data(reader),
            Err(OpbError::InvalidLine(String::from("min: x0;")))
        );
    }

    #[test]
    fn write_parse_clause() {
        let cl = clause![!lit![0], lit![1], !lit![2]];

        let mut cursor = Cursor::new(vec![]);

        write_clause(&mut cursor, cl.clone()).unwrap();

        cursor.rewind().unwrap();

        let (cnf, _) = super::parse_sat(cursor).unwrap().as_cnf();

        assert_eq!(cnf.n_clauses(), 1);
        assert_eq!(cnf.into_iter().next().unwrap().normalize(), cl.normalize());
    }

    fn write_parse_inst_test(in_inst: SatInstance, true_inst: SatInstance) {
        let mut cursor = Cursor::new(vec![]);

        write_sat(&mut cursor, in_inst).unwrap();

        cursor.rewind().unwrap();

        let parsed_inst = super::parse_sat(cursor).unwrap();

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
        let mut lits = RsHashMap::default();
        lits.insert(!lit![3], 1);
        lits.insert(lit![4], 1);
        lits.insert(!lit![5], 1);

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_ub(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(in_inst, true_inst);

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_eq(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(in_inst, true_inst);

        let mut in_inst: SatInstance = SatInstance::new();
        in_inst.add_card_constr(CardConstraint::new_lb(vec![!lit![3], lit![4], !lit![5]], 2));
        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(in_inst, true_inst);
    }

    #[test]
    fn write_parse_pb() {
        let mut lits = RsHashMap::default();
        lits.insert(!lit![6], 3);
        lits.insert(!lit![7], -5);
        lits.insert(lit![8], 2);
        lits.insert(lit![9], -4);

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_ub(lits.clone(), 2));
        write_parse_inst_test(true_inst.clone(), true_inst);

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_eq(lits.clone(), 2));
        write_parse_inst_test(true_inst.clone(), true_inst);

        let mut true_inst: SatInstance = SatInstance::new();
        true_inst.add_pb_constr(PBConstraint::new_lb(lits.clone(), 2));
        write_parse_inst_test(true_inst.clone(), true_inst);
    }
}
