extern crate proc_macro;

mod integration;
mod unit;

enum InitBy {
    Default(syn::Type),
    Expr(syn::Expr),
}

impl syn::parse::Parse for InitBy {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        Ok(
            if let syn::Result::<syn::Type>::Ok(r#type) = input.parse() {
                Self::Default(r#type)
            } else {
                Self::Expr(input.parse()?)
            },
        )
    }
}

impl quote::ToTokens for InitBy {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            InitBy::Default(r#type) => r#type.to_tokens(tokens),
            InitBy::Expr(expr) => expr.to_tokens(tokens),
        }
    }
}

struct IntegrationInput {
    slv: InitBy,
    bools: Vec<bool>,
}

impl syn::parse::Parse for IntegrationInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let slv: InitBy = input.parse()?;
        if input.is_empty() {
            return Ok(Self { slv, bools: vec![] });
        }
        let _: syn::Token![,] = input.parse()?;
        let bools =
            syn::punctuated::Punctuated::<syn::LitBool, syn::Token![,]>::parse_terminated(input)?;
        let bools: Vec<_> = bools.into_iter().map(|lit| lit.value).collect();
        Ok(Self { slv, bools })
    }
}

struct BasicUnitInput {
    slv: syn::Type,
    signature: syn::LitStr,
    mt: Option<bool>,
}

impl syn::parse::Parse for BasicUnitInput {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let slv: syn::Type = input.parse()?;
        let _: syn::Token![,] = input.parse()?;
        let signature: syn::LitStr = input.parse()?;
        if input.is_empty() {
            return Ok(Self {
                slv,
                signature,
                mt: None,
            });
        }
        let _: syn::Token![,] = input.parse()?;
        let mt: syn::LitBool = input.parse()?;
        Ok(Self {
            slv,
            signature,
            mt: Some(mt.value),
        })
    }
}

#[proc_macro]
pub fn basic_unittests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(tokens as BasicUnitInput);
    let mt = input.mt.unwrap_or(true);
    unit::basic(input.slv, input.signature, mt).into()
}

#[proc_macro]
pub fn termination_unittests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let slv = syn::parse_macro_input!(tokens as syn::Type);
    unit::termination(slv).into()
}

#[proc_macro]
pub fn learner_unittests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let slv = syn::parse_macro_input!(tokens as syn::Type);
    unit::learn(slv).into()
}

#[proc_macro]
pub fn freezing_unittests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let slv = syn::parse_macro_input!(tokens as syn::Type);
    unit::freezing(slv).into()
}

#[proc_macro]
pub fn propagating_unittests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let slv = syn::parse_macro_input!(tokens as syn::Type);
    unit::propagate(slv).into()
}

#[proc_macro]
pub fn base_tests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(tokens as IntegrationInput);
    integration::base(input).into()
}

#[proc_macro]
pub fn incremental_tests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(tokens as IntegrationInput);
    integration::incremental(input).into()
}

#[proc_macro]
pub fn learning_tests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(tokens as IntegrationInput);
    integration::learning(input).into()
}

#[proc_macro]
pub fn phasing_tests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(tokens as IntegrationInput);
    integration::phasing(input).into()
}

#[proc_macro]
pub fn flipping_tests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(tokens as IntegrationInput);
    integration::flipping(input).into()
}

#[proc_macro]
pub fn internal_stats_tests(tokens: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(tokens as IntegrationInput);
    integration::internal_stats(input).into()
}
