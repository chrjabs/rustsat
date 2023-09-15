//! # "Atomic"/"Trivial" Encodings

use crate::{
    clause,
    types::{Clause, Lit},
};

/// Implication of form `a -> b`
pub fn lit_impl_lit(a: Lit, b: Lit) -> Clause {
    clause![!a, b]
}

/// Implication of form `a -> (b1 | b2 | ... | bm)`
pub fn lit_impl_clause(a: Lit, b: &[Lit]) -> Clause {
    let mut cl: Clause = b.iter().copied().collect();
    cl.add(!a);
    cl
}

/// Implication of form `(a1 & a2 & ... & an) -> b`
pub fn cube_impl_lit(a: &[Lit], b: Lit) -> Clause {
    let mut cl: Clause = a.iter().map(|ai| !*ai).collect();
    cl.add(b);
    cl
}

/// Implication of form `(a1 & a2 & ... & an) -> (b1 | b2 | ... | bm)`
pub fn cube_impl_clause(a: &[Lit], b: &[Lit]) -> Clause {
    let mut cl: Clause = a.iter().map(|ai| !*ai).collect();
    cl.extend(b.iter().copied());
    cl
}
