//! # "Atomic"/"Trivial" Encodings

use std::ops::Not;

use crate::{
    clause,
    types::{Clause, Lit},
};

/// Implication of form `a -> b`
#[must_use]
pub fn lit_impl_lit(a: Lit, b: Lit) -> Clause {
    clause![!a, b]
}

/// Implication of form `a -> (b1 | b2 | ... | bm)`
#[must_use]
pub fn lit_impl_clause(a: Lit, b: &[Lit]) -> Clause {
    let mut cl = Clause::from(b);
    cl.add(!a);
    cl
}

/// Implication of form `(a1 & a2 & ... & an) -> b`
#[must_use]
pub fn cube_impl_lit(a: &[Lit], b: Lit) -> Clause {
    let mut cl: Clause = a.iter().copied().map(Not::not).collect();
    cl.add(b);
    cl
}

/// Implication of form `(a1 & a2 & ... & an) -> (b1 | b2 | ... | bm)`
#[must_use]
pub fn cube_impl_clause(a: &[Lit], b: &[Lit]) -> Clause {
    let mut cl = Clause::from(b);
    cl.extend(a.iter().copied().map(Not::not));
    cl
}

/// Implication of form `a -> (b1 & b2 & ... & bm)`
pub fn lit_impl_cube(a: Lit, b: &[Lit]) -> impl Iterator<Item = Clause> + '_ {
    b.iter().map(move |bi| clause![!a, *bi])
}

/// Implication of form `(a1 | a2 | ... | an) -> b`
pub fn clause_impl_lit(a: &[Lit], b: Lit) -> impl Iterator<Item = Clause> + '_ {
    a.iter().map(move |ai| clause![!*ai, b])
}

/// Implication of form `(a1 | a2 | ... | an) -> (b1 | b2 | ... | bm)`
pub fn clause_impl_clause<'all>(
    a: &'all [Lit],
    b: &'all [Lit],
) -> impl Iterator<Item = Clause> + 'all {
    a.iter().map(move |ai| {
        let mut cl = Clause::from(b);
        cl.add(!*ai);
        cl
    })
}

/// Implication of form `(a1 | a2 | ... | an) -> (b1 & b2 & ... | bm)`
pub fn clause_impl_cube<'all>(
    a: &'all [Lit],
    b: &'all [Lit],
) -> impl Iterator<Item = Clause> + 'all {
    a.iter()
        .flat_map(move |ai| b.iter().map(|bi| clause![!*ai, *bi]))
}

/// Implication of form `(a1 & a2 & ... & an) -> (b1 & b2 & ... & bm)`
pub fn cube_impl_cube<'all>(a: &'all [Lit], b: &'all [Lit]) -> impl Iterator<Item = Clause> + 'all {
    b.iter().map(move |bi| {
        let mut cl: Clause = a.iter().copied().map(Not::not).collect();
        cl.add(*bi);
        cl
    })
}
