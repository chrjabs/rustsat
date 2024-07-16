extern crate proc_macro;

use proc_macro::TokenStream;
use quote::ToTokens;
use syn::{parse::Parse, parse_macro_input, punctuated::Punctuated, Expr, LitBool, Token, Type};

mod integration;
mod unit;

enum InitBy {
    Default(Type),
    Expr(Expr),
}

impl Parse for InitBy {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(if let syn::Result::<Type>::Ok(typ) = input.parse() {
            Self::Default(typ)
        } else {
            Self::Expr(input.parse()?)
        })
    }
}

impl ToTokens for InitBy {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            InitBy::Default(typ) => typ.to_tokens(tokens),
            InitBy::Expr(expr) => expr.to_tokens(tokens),
        }
    }
}

struct IntegrationInput {
    slv: InitBy,
    bools: Vec<bool>,
}

impl Parse for IntegrationInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let slv: InitBy = input.parse()?;
        if input.is_empty() {
            return Ok(Self { slv, bools: vec![] });
        }
        let _: Token![,] = input.parse()?;
        let bools = Punctuated::<LitBool, Token![,]>::parse_terminated(input)?;
        let bools: Vec<_> = bools.into_iter().map(|lit| lit.value).collect();
        Ok(Self { slv, bools })
    }
}

struct BasicUnitInput {
    slv: Type,
    mt: Option<bool>,
}

impl Parse for BasicUnitInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let slv: Type = input.parse()?;
        if input.is_empty() {
            return Ok(Self { slv, mt: None });
        }
        let _: Token![,] = input.parse()?;
        let mt: LitBool = input.parse()?;
        Ok(Self {
            slv,
            mt: Some(mt.value),
        })
    }
}

#[proc_macro]
pub fn basic_unittests(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as BasicUnitInput);
    let mt = input.mt.unwrap_or(true);
    unit::basic(input.slv, mt).into()
}

#[proc_macro]
pub fn termination_unittests(tokens: TokenStream) -> TokenStream {
    let slv = parse_macro_input!(tokens as Type);
    unit::termination(slv).into()
}

#[proc_macro]
pub fn learner_unittests(tokens: TokenStream) -> TokenStream {
    let slv = parse_macro_input!(tokens as Type);
    unit::learn(slv).into()
}

#[proc_macro]
pub fn freezing_unittests(tokens: TokenStream) -> TokenStream {
    let slv = parse_macro_input!(tokens as Type);
    unit::freezing(slv).into()
}

#[proc_macro]
pub fn propagating_unittests(tokens: TokenStream) -> TokenStream {
    let slv = parse_macro_input!(tokens as Type);
    unit::propagate(slv).into()
}

#[proc_macro]
pub fn base_tests(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as IntegrationInput);
    integration::base(input).into()
}

#[proc_macro]
pub fn incremental_tests(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as IntegrationInput);
    integration::incremental(input).into()
}

#[proc_macro]
pub fn phasing_tests(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as IntegrationInput);
    integration::phasing(input).into()
}

#[proc_macro]
pub fn flipping_tests(tokens: TokenStream) -> TokenStream {
    let input = parse_macro_input!(tokens as IntegrationInput);
    integration::flipping(input).into()
}
