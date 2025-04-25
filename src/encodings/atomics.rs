//! # "Atomic"/"Trivial" Encodings

use std::ops::Not;

use crate::{
    clause,
    types::{
        constraints::{CardConstraint, PbConstraint},
        Clause, Lit,
    },
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

/// Reification of a literal implying a cardinality constraint
///
/// `lit -> card`
///
/// # Panics
///
/// - If the cardinality constraint is an equality constraint
/// - If the number of literals or the bound exceeds [`isize::MAX`]
#[must_use]
pub fn lit_impl_card(lit: Lit, card: &CardConstraint) -> PbConstraint {
    assert!(
        !card.is_unsat(),
        "the constraint must be satisfiable to reify it: {card}"
    );
    match card {
        CardConstraint::Ub(c) => {
            let (lits, bound) = c.decompose_ref();
            let bound = lits.len() + bound;
            let mut lits: Vec<_> = lits.iter().map(|lit| (*lit, 1)).collect();
            lits.push((lit, lits.len()));
            PbConstraint::new_ub_unsigned(
                lits,
                isize::try_from(bound).expect("cannot handle bounds larger than `isize::MAX`"),
            )
        }
        CardConstraint::Lb(c) => {
            let (lits, bound) = c.decompose_ref();
            let mut lits: Vec<_> = lits.iter().map(|lit| (*lit, 1)).collect();
            lits.push((!lit, *bound));
            PbConstraint::new_lb_unsigned(
                lits,
                isize::try_from(*bound).expect("cannot handle bounds larger than `isize::MAX`"),
            )
        }
        CardConstraint::Eq(_) => panic!("equality constraint cannot be trivially reified"),
    }
}

/// Reification of a cardinality constraint implying a literal
///
/// `card -> lit`
///
/// # Panics
///
/// - If the cardinality constraint is an equality constraint
/// - If the constraint is unsatisfiable
/// - If the number of literals or the bound exceeds [`isize::MAX`]
#[must_use]
pub fn card_impl_lit(card: &CardConstraint, lit: Lit) -> PbConstraint {
    assert!(
        !card.is_unsat(),
        "the constraint must be satisfiable to reify it: {card}"
    );
    match card {
        CardConstraint::Ub(c) => {
            let (lits, bound) = c.decompose_ref();
            let bound = 2 * lits.len() - bound - 1;
            let mut lits: Vec<_> = lits.iter().map(|lit| (!*lit, 1)).collect();
            lits.push((!lit, lits.len()));
            PbConstraint::new_ub_unsigned(
                lits,
                isize::try_from(bound).expect("cannot handle bounds larger than `isize::MAX`"),
            )
        }
        CardConstraint::Lb(c) => {
            let (lits, bound) = c.decompose_ref();
            let bound = lits.len() - bound + 1;
            let mut lits: Vec<_> = lits.iter().map(|lit| (!*lit, 1)).collect();
            lits.push((lit, bound));
            PbConstraint::new_lb_unsigned(
                lits,
                isize::try_from(bound).expect("cannot handle bounds larger than `isize::MAX`"),
            )
        }
        CardConstraint::Eq(_) => panic!("equality constraint cannot be trivially reified"),
    }
}

/// Reification of a literal implying a pseudo-Boolean constraint
///
/// `lit -> pb`
///
/// # Panics
///
/// - If the PB constraint is an equality constraint
/// - If the constraint is unsatisfiable
/// - If the sum of weights exceeds [`isize::MAX`]
#[must_use]
pub fn lit_impl_pb(lit: Lit, pb: &PbConstraint) -> PbConstraint {
    assert!(
        !pb.is_unsat(),
        "the constraint must be satisfiable to reify it: {pb}"
    );
    let mut pb = pb.clone();
    match pb {
        PbConstraint::Ub(_) => {
            let ws = isize::try_from(pb.weight_sum())
                .expect("cannot handle sums of weight larger than `isize::MAX`");
            pb.add([(lit, ws)]);
            pb.set_bound(pb.bound() + ws);
        }
        PbConstraint::Lb(_) => {
            pb.add([(!lit, pb.bound())]);
        }
        PbConstraint::Eq(_) => panic!("equality constraint cannot be trivially reified"),
    }
    pb
}

/// Reification of a pseudo-Boolean constraint implying a literal
///
/// `pb -> lit`
///
/// # Panics
///
/// - If the PB constraint is an equality constraint
/// - If the constraint is unsatisfiable
/// - If the sum of weights exceeds [`isize::MAX`]
#[must_use]
pub fn pb_impl_lit(pb: &PbConstraint, lit: Lit) -> PbConstraint {
    assert!(
        !pb.is_unsat(),
        "the constraint must be satisfiable to reify it: {pb}"
    );
    match pb {
        PbConstraint::Ub(c) => {
            let ws = isize::try_from(pb.weight_sum())
                .expect("cannot handle sums of weight larger than `isize::MAX`");
            let (lits, bound) = c.decompose_ref();
            let bound = 2 * ws - bound - 1;
            let mut lits: Vec<_> = lits.iter().map(|(lit, w)| (!*lit, *w)).collect();
            lits.push((!lit, pb.weight_sum()));
            PbConstraint::new_ub_unsigned(lits, bound)
        }
        PbConstraint::Lb(c) => {
            let ws = isize::try_from(pb.weight_sum())
                .expect("cannot handle sums of weight larger than `isize::MAX`");
            let (lits, bound) = c.decompose_ref();
            let bound = ws - bound + 1;
            let mut lits: Vec<_> = lits
                .iter()
                .map(|(lit, w)| (!*lit, isize::try_from(*w).unwrap()))
                .collect();
            lits.push((lit, bound));
            PbConstraint::new_lb(lits, bound)
        }
        PbConstraint::Eq(_) => panic!("equality constraint cannot be trivially reified"),
    }
}
