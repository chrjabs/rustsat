//! # Shared Parsing Functionality

use anyhow::Context;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{line_ending, multispace1, not_line_ending, space0},
    combinator::{map, recognize},
    error::{context, Error as NomErr},
    Parser,
};

pub fn single_value<'input, T, P>(
    parser: P,
    comment_tag: &'static str,
) -> impl Parser<&'input str, Output = T, Error = NomErr<&'input str>>
where
    P: nom::Parser<&'input str, Output = T, Error = NomErr<&'input str>>,
{
    context(
        "expected a single u32 number",
        map(
            (space0, parser, space0, comment_or_end(comment_tag)),
            |tup| tup.1,
        ),
    )
}

pub fn comment_or_end<'input>(
    comment_tag: &'static str,
) -> impl nom::Parser<&'input str, Output = &'input str, Error = NomErr<&'input str>> {
    recognize((
        alt((
            recognize((tag::<_, _, NomErr<_>>(comment_tag), not_line_ending)),
            not_line_ending,
        )),
        line_ending,
    ))
}

pub fn callback_list<'input, T, P>(
    input: &'input str,
    mut parse: P,
    mut callback: impl FnMut(T) -> anyhow::Result<()>,
) -> anyhow::Result<&str>
where
    P: FnMut(&'input str) -> nom::IResult<&'input str, T>,
{
    let (mut buf, _) = (tag::<_, _, NomErr<_>>("["), space0)
        .parse(input)
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
        buf = match (space0::<_, NomErr<_>>, tag(","), space0).parse(remain) {
            Ok((remain, _)) => remain,
            Err(_) => {
                let (remain, _) = (space0::<_, NomErr<_>>, tag("]"))
                    .parse(remain)
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
) -> anyhow::Result<&str>
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
