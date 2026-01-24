//! # Shared Parsing Functionality

use winnow::{
    ascii::{line_ending, space0, space1, till_line_ending},
    combinator::opt,
    error::{ContextError, ParserError, StrContext, StrContextValue},
    seq, Parser,
};

pub fn single_value<'i, P, O, E>(
    mut parser: P,
    comment_tag: &'static str,
) -> impl Parser<&'i str, O, E>
where
    P: Parser<&'i str, O, E>,
    E: ParserError<&'i str>,
{
    seq! {
        _: space0,
        parser,
        _: space0,
        _: comment_or_end(comment_tag)
    }
    .map(|tup| tup.0)
}

pub fn comment_or_end<'i, E>(comment_tag: &'static str) -> impl Parser<&'i str, &'i str, E>
where
    E: ParserError<&'i str>,
{
    seq! {
        space0,
        opt((comment_tag, till_line_ending)),
        line_ending,
    }
    .take()
}

pub struct ListCallbackParser<Cb, P, O> {
    parser: P,
    callback: Cb,
    _output: std::marker::PhantomData<O>,
}

impl<Cb, P, O> ListCallbackParser<Cb, P, O> {
    pub fn new(callback: Cb, parser: P) -> Self {
        Self {
            parser,
            callback,
            _output: std::marker::PhantomData,
        }
    }
}

impl<'i, Cb, P, O> Parser<&'i str, (), ContextError> for ListCallbackParser<Cb, P, O>
where
    P: Parser<&'i str, O, ContextError> + Copy,
    Cb: FnMut(O) -> Result<(), ContextError>,
{
    fn parse_next(&mut self, input: &mut &'i str) -> winnow::Result<(), ContextError> {
        ('[', space0::<_, ContextError>)
            .context(StrContext::Expected(StrContextValue::Description(
                "start of list",
            )))
            .parse_next(input)?;
        loop {
            let val = self
                .parser
                .context(StrContext::Expected(StrContextValue::Description(
                    "list value",
                )))
                .parse_next(input)?;
            (self.callback)(val)?;
            if input.trim().is_empty() {
                let mut err = ContextError::new();
                err.push(StrContext::Expected(StrContextValue::Description(
                    "line should continue",
                )));
                return Err(err);
            }
            match (space0::<_, ContextError>, ',', space0).parse_next(input) {
                Ok(_) => (),
                Err(_) => {
                    (space0::<_, ContextError>, ']')
                        .context(StrContext::Expected(StrContextValue::Description(
                            "end of list or list separator token",
                        )))
                        .parse_next(input)?;
                    return Ok(());
                }
            };
        }
    }
}

pub struct SeparatedCallbackParser<Cb, P, O> {
    parser: P,
    callback: Cb,
    _output: std::marker::PhantomData<O>,
}

impl<Cb, P, O> SeparatedCallbackParser<Cb, P, O> {
    pub fn new(callback: Cb, parser: P) -> Self {
        Self {
            parser,
            callback,
            _output: std::marker::PhantomData,
        }
    }
}

impl<'i, Cb, P, O> Parser<&'i str, (), ContextError> for SeparatedCallbackParser<Cb, P, O>
where
    P: Parser<&'i str, O, ContextError> + Copy,
    Cb: FnMut(O) -> Result<(), ContextError>,
{
    fn parse_next(&mut self, input: &mut &'i str) -> winnow::Result<(), ContextError> {
        space0.parse_next(input)?;
        loop {
            let val = self
                .parser
                .context(StrContext::Expected(StrContextValue::Description(
                    "separated value",
                )))
                .parse_next(input)?;
            (self.callback)(val)?;
            match space1::<_, ContextError>.parse_next(input) {
                Ok(_) => {
                    if input.is_empty() {
                        return Ok(());
                    }
                }
                Err(_) => {
                    return Ok(());
                }
            };
        }
    }
}
