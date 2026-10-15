//! # "Atomic"/"Trivial" Encodings

use crate::types::Clause;
use crate::types::Lit;
use crate::types::constraints::CardConstraint;
use crate::types::constraints::CardLbConstr;
use crate::types::constraints::CardUbConstr;
use crate::types::constraints::PbConstraint;
use crate::types::constraints::PbLbConstr;
use crate::types::constraints::PbUbConstr;

/// Implication of form `a -> b`
#[must_use]
pub fn lit_impl_lit(a: Lit, b: Lit) -> Clause {
    !a | b
}

/// Implication of form `a -> (b1 | b2 | ... | bm)`
#[must_use]
pub fn lit_impl_clause(a: Lit, b: &[Lit]) -> Clause {
    let mut cl = Clause::from(b);
    cl |= !a;
    cl
}

/// Implication of form `(a1 & a2 & ... & an) -> b`
#[must_use]
pub fn cube_impl_lit(a: &[Lit], b: Lit) -> Clause {
    let mut cl: Clause = a.iter().copied().map(std::ops::Not::not).collect();
    cl |= b;
    cl
}

/// Implication of form `(a1 & a2 & ... & an) -> (b1 | b2 | ... | bm)`
#[must_use]
pub fn cube_impl_clause(a: &[Lit], b: &[Lit]) -> Clause {
    let mut cl = Clause::from(b);
    cl.extend(a.iter().copied().map(std::ops::Not::not));
    cl
}

/// Implication of form `a -> (b1 & b2 & ... & bm)`
pub fn lit_impl_cube(a: Lit, b: &[Lit]) -> impl Iterator<Item = Clause> + '_ {
    b.iter().map(move |bi| !a | *bi)
}

/// Implication of form `(a1 | a2 | ... | an) -> b`
pub fn clause_impl_lit(a: &[Lit], b: Lit) -> impl Iterator<Item = Clause> + '_ {
    a.iter().map(move |ai| !*ai | b)
}

/// Implication of form `(a1 | a2 | ... | an) -> (b1 | b2 | ... | bm)`
pub fn clause_impl_clause<'all>(
    a: &'all [Lit],
    b: &'all [Lit],
) -> impl Iterator<Item = Clause> + 'all {
    a.iter().map(move |ai| {
        let mut cl = Clause::from(b);
        cl |= !*ai;
        cl
    })
}

/// Implication of form `(a1 | a2 | ... | an) -> (b1 & b2 & ... | bm)`
pub fn clause_impl_cube<'all>(
    a: &'all [Lit],
    b: &'all [Lit],
) -> impl Iterator<Item = Clause> + 'all {
    a.iter().flat_map(move |ai| b.iter().map(|bi| !*ai | *bi))
}

/// Implication of form `(a1 & a2 & ... & an) -> (b1 & b2 & ... & bm)`
pub fn cube_impl_cube<'all>(a: &'all [Lit], b: &'all [Lit]) -> impl Iterator<Item = Clause> + 'all {
    b.iter().map(move |bi| {
        let mut cl: Clause = a.iter().copied().map(std::ops::Not::not).collect();
        cl |= *bi;
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
/// - If the cardinality constraint is unsatisfiable
/// - If the number of literals or the bound exceeds [`isize::MAX`]
#[must_use]
pub fn lit_impl_card(lit: Lit, card: &CardConstraint) -> PbConstraint {
    match card {
        CardConstraint::Ub(c) => PbConstraint::Ub(lit_impl_card_ub(lit, c)),
        CardConstraint::Lb(c) => PbConstraint::Lb(lit_impl_card_lb(lit, c)),
        CardConstraint::Eq(_) => {
            panic!("equality constraint cannot be trivially reified")
        }
    }
}

/// Reification of a literal implying an upper-bounding cardinality constraint
///
/// `lit -> card <= b`
///
/// # Panics
///
/// - If the number of literals or the bound exceeds [`isize::MAX`]
#[must_use]
pub fn lit_impl_card_ub(lit: Lit, card: &CardUbConstr) -> PbUbConstr {
    let (lits, bound) = card.decompose_ref();
    let bound = lits.len() + bound;
    let mut lits: Vec<_> = lits.iter().map(|lit| (*lit, 1)).collect();
    lits.push((lit, lits.len()));
    PbUbConstr::new_unsigned(
        lits,
        isize::try_from(bound).expect("cannot handle bounds larger than `isize::MAX`"),
    )
}

/// Reification of a literal implying a lower-bounding cardinality constraint
///
/// `lit -> card >= b`
///
/// # Panics
///
/// - If the cardinality constraint is unsatisfiable
/// - If the number of literals or the bound exceeds [`isize::MAX`]
#[must_use]
pub fn lit_impl_card_lb(lit: Lit, card: &CardLbConstr) -> PbLbConstr {
    assert!(
        !card.is_unsat(),
        "the constraint must be satisfiable to reify it: {card}"
    );
    let (lits, &bound) = card.decompose_ref();
    PbLbConstr::new_unsigned(
        lits.iter().map(|&lit| (lit, 1)).chain([(!lit, bound)]),
        isize::try_from(bound).expect("cannot handle bounds larger than `isize::MAX`"),
    )
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
        CardConstraint::Eq(_) => {
            panic!("equality constraint cannot be trivially reified")
        }
    }
}

/// Reification of a lower-bounding cardinality constraint implying a literal
///
/// `card >= b -> lit`
///
/// # Panics
///
/// - If the constraint is unsatisfiable
/// - If the number of literals or the bound exceeds [`isize::MAX`]
#[must_use]
pub fn card_impl_lit_ub(card: &CardUbConstr, lit: Lit) -> PbUbConstr {
    let (lits, bound) = card.decompose_ref();
    let bound = 2 * lits.len() - bound - 1;
    let mut lits: Vec<_> = lits.iter().map(|lit| (!*lit, 1)).collect();
    lits.push((!lit, lits.len()));
    PbUbConstr::new_unsigned(
        lits,
        isize::try_from(bound).expect("cannot handle bounds larger than `isize::MAX`"),
    )
}

/// Reification of an upper-bounding cardinality constraint implying a literal
///
/// `card <= b -> lit`
///
/// # Panics
///
/// - If the constraint is unsatisfiable
/// - If the number of literals or the bound exceeds [`isize::MAX`]
#[must_use]
pub fn card_impl_lit_lb(card: &CardLbConstr, lit: Lit) -> PbLbConstr {
    assert!(
        !card.is_unsat(),
        "the constraint must be satisfiable to reify it: {card}"
    );
    let (lits, bound) = card.decompose_ref();
    let bound = lits.len() - bound + 1;
    let mut lits: Vec<_> = lits.iter().map(|lit| (!*lit, 1)).collect();
    lits.push((lit, bound));
    PbLbConstr::new_unsigned(
        lits,
        isize::try_from(bound).expect("cannot handle bounds larger than `isize::MAX`"),
    )
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
    match pb {
        PbConstraint::Ub(c) => PbConstraint::Ub(lit_impl_pb_ub(lit, c)),
        PbConstraint::Lb(c) => PbConstraint::Lb(lit_impl_pb_lb(lit, c)),
        PbConstraint::Eq(_) => {
            panic!("equality constraint cannot be trivially reified")
        }
    }
}

/// Reification of a literal implying an upper-bounding pseudo-Boolean constraint
///
/// `lit -> pb <= b`
///
/// # Panics
///
/// - If the constraint is unsatisfiable
/// - If the sum of weights exceeds [`isize::MAX`]
#[must_use]
pub fn lit_impl_pb_ub(lit: Lit, pb: &PbUbConstr) -> PbUbConstr {
    assert!(
        !pb.is_unsat(),
        "the constraint must be satisfiable to reify it: {pb}"
    );
    let ws = pb.weight_sum();
    let signed_ws = isize::try_from(pb.weight_sum())
        .expect("cannot handle sums of weight larger than `isize::MAX`");
    let (lits, bound) = pb.decompose_ref();
    PbUbConstr::new_unsigned(lits.iter().copied().chain([(lit, ws)]), *bound + signed_ws)
}

/// Reification of a literal implying a lower-bounding pseudo-Boolean constraint
///
/// `lit -> pb >= b`
///
/// # Panics
///
/// - If the constraint is unsatisfiable
#[must_use]
pub fn lit_impl_pb_lb(lit: Lit, pb: &PbLbConstr) -> PbLbConstr {
    assert!(
        !pb.is_unsat(),
        "the constraint must be satisfiable to reify it: {pb}"
    );
    let (lits, &bound) = pb.decompose_ref();
    PbLbConstr::new(
        lits.iter()
            .map(|&(lit, w)| {
                (
                    lit,
                    isize::try_from(w).expect("can't handle weights larger than `isize::MAX`"),
                )
            })
            .chain([(!lit, bound)]),
        bound,
    )
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
        PbConstraint::Ub(c) => PbConstraint::Ub(pb_ub_impl_lit(c, lit)),
        PbConstraint::Lb(c) => PbConstraint::Lb(pb_lb_impl_lit(c, lit)),
        PbConstraint::Eq(_) => {
            panic!("equality constraint cannot be trivially reified")
        }
    }
}

/// Reification of an upper-bounding pseudo-Boolean constraint implying a literal
///
/// `pb <= b -> lit`
///
/// # Panics
///
/// - If the constraint is unsatisfiable
/// - If the sum of weights exceeds [`isize::MAX`]
#[must_use]
pub fn pb_ub_impl_lit(pb: &PbUbConstr, lit: Lit) -> PbUbConstr {
    assert!(
        !pb.is_unsat(),
        "the constraint must be satisfiable to reify it: {pb}"
    );
    let ws = isize::try_from(pb.weight_sum())
        .expect("cannot handle sums of weight larger than `isize::MAX`");
    let (lits, bound) = pb.decompose_ref();
    let bound = 2 * ws - bound - 1;
    let mut lits: Vec<_> = lits.iter().map(|(lit, w)| (!*lit, *w)).collect();
    lits.push((!lit, pb.weight_sum()));
    PbUbConstr::new_unsigned(lits, bound)
}

/// Reification of a lower-bounding pseudo-Boolean constraint implying a literal
///
/// `pb >= b -> lit`
///
/// # Panics
///
/// - If the constraint is unsatisfiable
/// - If the sum of weights exceeds [`isize::MAX`]
#[must_use]
pub fn pb_lb_impl_lit(pb: &PbLbConstr, lit: Lit) -> PbLbConstr {
    assert!(
        !pb.is_unsat(),
        "the constraint must be satisfiable to reify it: {pb}"
    );
    let ws = isize::try_from(pb.weight_sum())
        .expect("cannot handle sums of weight larger than `isize::MAX`");
    let (lits, bound) = pb.decompose_ref();
    let bound = ws - bound + 1;
    let mut lits: Vec<_> = lits
        .iter()
        .map(|(lit, w)| (!*lit, isize::try_from(*w).unwrap()))
        .collect();
    lits.push((lit, bound));
    PbLbConstr::new(lits, bound)
}
