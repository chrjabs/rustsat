//! # Shared Parsing Functionality

use anyhow::Context;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{line_ending, multispace1, not_line_ending, space0},
    combinator::{map, recognize},
    error::{context, Error as NomErr},
    sequence::{pair, tuple},
};

pub fn single_value<'input, T, P>(
    parser: P,
    comment_tag: &'static str,
) -> impl FnMut(&'input str) -> nom::IResult<&'input str, T>
where
    P: Fn(&'input str) -> nom::IResult<&'input str, T>,
{
    context(
        "expected a single u32 number",
        map(
            tuple((space0, parser, space0, comment_or_end(comment_tag))),
            |tup| tup.1,
        ),
    )
}

pub fn comment_or_end<'input>(
    comment_tag: &'static str,
) -> impl FnMut(&'input str) -> nom::IResult<&'input str, &'input str> {
    recognize(pair(
        alt((
            recognize(tuple((tag(comment_tag), not_line_ending))),
            not_line_ending,
        )),
        line_ending,
    ))
}

pub fn callback_list<'input, T, P>(
    input: &'input str,
    mut parse: P,
    mut callback: impl FnMut(T) -> anyhow::Result<()>,
) -> anyhow::Result<&'input str>
where
    P: FnMut(&'input str) -> nom::IResult<&'input str, T>,
{
    let (mut buf, _) = tuple::<_, _, NomErr<_>, _>((tag("["), space0))(input)
        .map_err(|e| e.to_owned())
        .with_context(|| format!("failed to parse list start '{input}'"))?;
    loop {
        let (remain, val) = parse(buf)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse value in list '{input}'"))?;
        callback(val)?;
        anyhow::ensure!(
            !remain.trim().is_empty(),
            "line ended before list was closed"
        );
        buf = match tuple::<_, _, NomErr<_>, _>((space0, tag(","), space0))(remain) {
            Ok((remain, _)) => remain,
            Err(_) => {
                let (remain, _) = tuple::<_, _, NomErr<_>, _>((space0, tag("]")))(remain)
                    .map_err(|e| e.to_owned())
                    .with_context(|| format!("failed to parse list end/separator '{input}'"))?;
                return Ok(remain);
            }
        };
    }
}

pub fn callback_separated<'input, T, P>(
    input: &'input str,
    mut parse: P,
    mut callback: impl FnMut(T) -> anyhow::Result<()>,
) -> anyhow::Result<&'input str>
where
    P: FnMut(&'input str) -> nom::IResult<&'input str, T>,
{
    let mut buf = input.trim_start();
    loop {
        let (remain, val) = parse(buf)
            .map_err(|e| e.to_owned())
            .with_context(|| format!("failed to parse value in list '{input}'"))?;
        callback(val)?;
        buf = match multispace1::<_, NomErr<_>>(remain) {
            Ok((remain, _)) => {
                if remain.is_empty() {
                    return Ok("");
                }
                remain
            }
            Err(_) => return Ok(remain),
        };
    }
}
