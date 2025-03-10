//! # Optimization Instance Representations

use std::{
    cmp,
    collections::{hash_map, BTreeSet},
    io,
    path::Path,
    slice,
};

use crate::{
    algs::maxsat,
    clause,
    encodings::{card, pb},
    solvers::Solve,
    types::{
        constraints::{CardConstraint, PbConstraint},
        Assignment, Clause, ClsIter, Lit, LitIter, RsHashMap, TernaryVal, Var, WClsIter, WLitIter,
    },
    utils::unreachable_none,
    RequiresClausal, RequiresSoftLits,
};

/// Internal objective type for not exposing variants
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
enum IntObj {
    Weighted {
        offset: isize,
        soft_lits: RsHashMap<Lit, usize>,
        soft_clauses: RsHashMap<Clause, usize>,
    },
    Unweighted {
        offset: isize,
        unit_weight: Option<usize>,
        soft_lits: Vec<Lit>,
        soft_clauses: Vec<Clause>,
    },
}

use super::{
    fio::{self, dimacs::WcnfLine},
    BasicVarManager, Cnf, ManageVars, ReindexVars, SatInstance,
};

/// Type representing an optimization objective.
/// This type currently supports soft clauses and soft literals.
/// All objectives are considered minimization objectives.
#[derive(Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Objective(IntObj);

impl From<IntObj> for Objective {
    fn from(obj: IntObj) -> Self {
        Self(obj)
    }
}

impl Default for Objective {
    fn default() -> Self {
        Self(IntObj::Unweighted {
            offset: 0,
            unit_weight: None,
            soft_lits: Vec::default(),
            soft_clauses: Vec::default(),
        })
    }
}

impl Objective {
    /// Creates a new empty objective
    #[must_use]
    pub fn new() -> Self {
        Objective::default()
    }

    /// Checks if the objective is empty, i.e., has constant value 0
    #[must_use]
    pub fn is_empty(&self) -> bool {
        match &self.0 {
            IntObj::Weighted {
                offset,
                soft_lits,
                soft_clauses,
            } => soft_lits.is_empty() && soft_clauses.is_empty() && offset == &0,
            IntObj::Unweighted {
                offset,
                soft_lits,
                soft_clauses,
                ..
            } => soft_lits.is_empty() && soft_clauses.is_empty() && offset == &0,
        }
    }

    /// Checks if the objective is a constant
    #[must_use]
    pub fn constant(&self) -> bool {
        match &self.0 {
            IntObj::Weighted {
                soft_lits,
                soft_clauses,
                ..
            } => soft_lits.is_empty() && soft_clauses.is_empty(),
            IntObj::Unweighted {
                soft_lits,
                soft_clauses,
                ..
            } => soft_lits.is_empty() && soft_clauses.is_empty(),
        }
    }

    /// Gets the number of soft literals in the objective
    #[must_use]
    pub fn n_lits(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_lits, .. } => soft_lits.len(),
            IntObj::Unweighted { soft_lits, .. } => soft_lits.len(),
        }
    }

    /// Gets the number of soft clauses in the objective
    #[must_use]
    pub fn n_clauses(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_clauses, .. } => soft_clauses.len(),
            IntObj::Unweighted { soft_clauses, .. } => soft_clauses.len(),
        }
    }

    /// Gets the number of soft literals and clauses in the objective
    #[must_use]
    pub fn n_softs(&self) -> usize {
        self.n_lits() + self.n_clauses()
    }

    /// Gets the weight sum of soft literals
    #[must_use]
    pub fn lit_weight_sum(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_lits, .. } => soft_lits.iter().fold(0, |s, (_, w)| s + w),
            IntObj::Unweighted {
                soft_lits,
                unit_weight,
                ..
            } => soft_lits.len() * unit_weight.unwrap_or(0),
        }
    }

    /// Gets the weight sum of soft clauses
    #[must_use]
    pub fn clause_weight_sum(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_clauses, .. } => soft_clauses.iter().fold(0, |s, (_, w)| s + w),
            IntObj::Unweighted {
                soft_clauses,
                unit_weight,
                ..
            } => soft_clauses.len() * unit_weight.unwrap_or(0),
        }
    }

    /// Gets the weight sum of all soft literals and clauses
    #[must_use]
    pub fn weight_sum(&self) -> usize {
        self.lit_weight_sum() + self.clause_weight_sum()
    }

    /// Gets the maximum weight of a soft literal
    #[must_use]
    pub fn max_lit_weight(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_lits, .. } => {
                soft_lits
                    .iter()
                    .fold(0, |s, (_, w)| if *w > s { *w } else { s })
            }
            IntObj::Unweighted { unit_weight, .. } => unit_weight.unwrap_or(0),
        }
    }

    /// Gets the maximum weight of a soft clause
    #[must_use]
    pub fn max_clause_weight(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_clauses, .. } => {
                soft_clauses
                    .iter()
                    .fold(0, |s, (_, w)| if *w > s { *w } else { s })
            }
            IntObj::Unweighted { unit_weight, .. } => unit_weight.unwrap_or(0),
        }
    }

    /// Gets the maximum weight of any soft
    #[must_use]
    pub fn max_weight(&self) -> usize {
        cmp::max(self.max_lit_weight(), self.max_clause_weight())
    }

    /// Gets the minimum weight of a soft literal
    #[must_use]
    pub fn min_lit_weight(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_lits, .. } => {
                soft_lits
                    .iter()
                    .fold(usize::MAX, |s, (_, w)| if *w < s { *w } else { s })
            }
            IntObj::Unweighted { unit_weight, .. } => unit_weight.unwrap_or(0),
        }
    }

    /// Gets the minimum weight of a soft clause
    #[must_use]
    pub fn min_clause_weight(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_clauses, .. } => soft_clauses
                .iter()
                .fold(usize::MAX, |s, (_, w)| if *w < s { *w } else { s }),
            IntObj::Unweighted { unit_weight, .. } => unit_weight.unwrap_or(0),
        }
    }

    /// Gets the minimum weight of any soft
    #[must_use]
    pub fn min_weight(&self) -> usize {
        cmp::min(self.min_lit_weight(), self.min_clause_weight())
    }

    /// Evaluates the objective under an assignment. Only clauses _falsified_
    /// and literals _set_ incur cost.
    ///
    /// # Panics
    ///
    /// If the objective value overflows
    #[must_use]
    pub fn evaluate(&self, sol: &Assignment) -> isize {
        // TODO: maybe improve in case evaluate_no_offset overflows, but the sum with the offset
        // does not
        isize::try_from(self.evaluate_no_offset(sol)).expect("objective value overflow")
            + self.offset()
    }

    /// Evaluates the objective under and assignment without considering the
    /// offset. Only clauses _falsified_ and literals _set_ incur cost.
    #[must_use]
    pub fn evaluate_no_offset(&self, sol: &Assignment) -> usize {
        match &self.0 {
            IntObj::Weighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                let cost = soft_lits.iter().fold(0, |c, (l, w)| {
                    if sol.lit_value(*l) == TernaryVal::True {
                        c + w
                    } else {
                        c
                    }
                });
                soft_clauses.iter().fold(cost, |c, (cl, w)| {
                    if cl.evaluate(sol) == TernaryVal::False {
                        c + w
                    } else {
                        c
                    }
                })
            }
            IntObj::Unweighted {
                unit_weight,
                soft_lits,
                soft_clauses,
                ..
            } => {
                let cost = soft_lits.iter().fold(0, |c, l| {
                    if sol.lit_value(*l) == TernaryVal::True {
                        c + 1
                    } else {
                        c
                    }
                });
                let cost = soft_clauses.iter().fold(cost, |c, cl| {
                    if cl.evaluate(sol) == TernaryVal::False {
                        c + 1
                    } else {
                        c
                    }
                });
                if let Some(unit_weight) = unit_weight {
                    cost * unit_weight
                } else {
                    debug_assert_eq!(cost, 0);
                    0
                }
            }
        }
    }

    /// Sets the value offset
    pub fn set_offset(&mut self, new_offset: isize) {
        match &mut self.0 {
            IntObj::Weighted { offset, .. } | IntObj::Unweighted { offset, .. } => {
                *offset = new_offset;
            }
        }
    }

    /// Gets the global value offset
    #[must_use]
    pub fn offset(&self) -> isize {
        match &self.0 {
            IntObj::Weighted { offset, .. } | IntObj::Unweighted { offset, .. } => *offset,
        }
    }

    /// Increases the value offset
    pub fn increase_offset(&mut self, offset_incr: isize) {
        match &mut self.0 {
            IntObj::Weighted { offset, .. } | IntObj::Unweighted { offset, .. } => {
                *offset += offset_incr;
            }
        }
    }

    /// Checks if the objective is weighted
    #[must_use]
    pub fn weighted(&self) -> bool {
        match &self.0 {
            IntObj::Weighted { .. } => true,
            IntObj::Unweighted { .. } => false,
        }
    }

    /// Converts an objective from unweighted to weighted
    fn unweighted_2_weighted(&mut self) {
        match &mut self.0 {
            IntObj::Weighted { .. } => (),
            IntObj::Unweighted {
                offset,
                unit_weight,
                soft_lits,
                soft_clauses,
            } => {
                if let Some(unit_weight) = unit_weight {
                    *self = IntObj::Weighted {
                        offset: *offset,
                        soft_lits: soft_lits.drain(..).map(|l| (l, *unit_weight)).collect(),
                        soft_clauses: soft_clauses
                            .drain(..)
                            .map(|cl| (cl, *unit_weight))
                            .collect(),
                    }
                    .into();
                } else {
                    *self = IntObj::Weighted {
                        offset: *offset,
                        soft_lits: RsHashMap::default(),
                        soft_clauses: RsHashMap::default(),
                    }
                    .into();
                }
            }
        }
    }

    /// Converts an objective from weighted to unweighted
    fn weighted_2_unweighted(&mut self) {
        match &mut self.0 {
            IntObj::Unweighted { .. } => (),
            IntObj::Weighted {
                offset,
                soft_lits,
                soft_clauses,
            } => {
                let mut soft_unit_lits = vec![];
                soft_lits
                    .drain()
                    .for_each(|(l, w)| soft_unit_lits.resize(soft_unit_lits.len() + w, l));
                let mut soft_unit_clauses = vec![];
                soft_clauses
                    .drain()
                    .for_each(|(cl, w)| soft_unit_clauses.resize(soft_unit_clauses.len() + w, cl));
                *self = IntObj::Unweighted {
                    offset: *offset,
                    unit_weight: Some(1),
                    soft_lits: soft_unit_lits,
                    soft_clauses: soft_unit_clauses,
                }
                .into();
            }
        }
    }

    /// Adds a soft literal or updates its weight. Returns the old weight, if
    /// the literal was already in the objective.
    pub fn add_soft_lit(&mut self, w: usize, l: Lit) -> Option<usize> {
        match &mut self.0 {
            IntObj::Weighted { soft_lits, .. } => {
                if w == 0 {
                    return soft_lits.remove(&l);
                }
                soft_lits.insert(l, w)
            }
            IntObj::Unweighted {
                unit_weight,
                soft_lits,
                ..
            } => {
                if w == 0 {
                    if let Some(idx) = soft_lits.iter().position(|l2| l2 == &l) {
                        soft_lits.swap_remove(idx);
                        return Some(unreachable_none!(*unit_weight));
                    }
                    None
                } else if let Some(unit_weight) = unit_weight {
                    if w == *unit_weight {
                        if soft_lits.iter().any(|l2| l2 == &l) {
                            return Some(*unit_weight);
                        }
                        soft_lits.push(l);
                        None
                    } else {
                        // Type changes from unweighted to weighted
                        self.unweighted_2_weighted();
                        // Add literal to new weighted objective
                        self.add_soft_lit(w, l)
                    }
                } else {
                    soft_lits.push(l);
                    *unit_weight = Some(w);
                    None
                }
            }
        }
    }

    /// Increases the weight of a soft literal. Returns the old weight, if the
    /// literal was already in the objective.
    pub fn increase_soft_lit(&mut self, add_w: usize, l: Lit) -> Option<usize> {
        if add_w == 0 {
            return self.lit_weight(l);
        }
        if self.lit_weight(l).is_none() {
            return self.add_soft_lit(add_w, l);
        }
        self.unweighted_2_weighted();
        match &mut self.0 {
            IntObj::Weighted { soft_lits, .. } => match soft_lits.get_mut(&l) {
                Some(old_w) => {
                    *old_w += add_w;
                    Some(*old_w - add_w)
                }
                None => soft_lits.insert(l, add_w),
            },
            IntObj::Unweighted { .. } => unreachable!(),
        }
    }

    /// Increases a soft literal with possibly negative weight. Internally all
    /// weights are positive, negative weights are represented by a global value
    /// offset and negated literals.
    /// This does _not_ update weights but increases them, since otherwise,
    /// adding literal l with a positive weight and afterwards -l with a
    /// negative weight would mess up the state.
    pub fn increase_soft_lit_int(&mut self, add_w: isize, l: Lit) {
        let unsigned_w = add_w.unsigned_abs();
        if add_w < 0 {
            self.increase_offset(add_w);
            self.increase_soft_lit(unsigned_w, !l);
        } else {
            self.increase_soft_lit(unsigned_w, l);
        }
    }

    /// Adds a soft clause or updates its weight. Returns the old weight, if
    /// the clause was already in the objective.
    ///
    /// # Panics
    ///
    /// If the clause is empty and `w` is larger than [`isize::MAX`]
    pub fn add_soft_clause(&mut self, w: usize, cl: Clause) -> Option<usize> {
        if cl.is_empty() {
            self.increase_offset(isize::try_from(w).expect("weight overflow"));
            return None;
        }
        if cl.len() == 1 {
            return self.add_soft_lit(w, !cl[0]);
        }
        match &mut self.0 {
            IntObj::Weighted { soft_clauses, .. } => {
                if w == 0 {
                    return soft_clauses.remove(&cl);
                }
                soft_clauses.insert(cl, w)
            }
            IntObj::Unweighted {
                unit_weight,
                soft_clauses,
                ..
            } => {
                if w == 0 {
                    if let Some(idx) = soft_clauses.iter().position(|cl2| cl2 == &cl) {
                        soft_clauses.swap_remove(idx);
                        return Some(unreachable_none!(*unit_weight));
                    }
                    None
                } else if let Some(unit_weight) = unit_weight {
                    if w == *unit_weight {
                        if soft_clauses.iter().any(|cl2| cl2 == &cl) {
                            return Some(*unit_weight);
                        }
                        soft_clauses.push(cl);
                        None
                    } else {
                        // Type changes from unweighted to weighted
                        self.unweighted_2_weighted();
                        // Add literal to new weighted objective
                        self.add_soft_clause(w, cl)
                    }
                } else {
                    soft_clauses.push(cl);
                    *unit_weight = Some(w);
                    None
                }
            }
        }
    }

    /// Increases the weight of a soft clause. Returns the old weight, if the
    /// clause was already in the objective.
    pub fn increase_soft_clause(&mut self, add_w: usize, cl: Clause) -> Option<usize> {
        if add_w == 0 {
            return self.clause_weight(&cl);
        }
        if self.clause_weight(&cl).is_none() {
            return self.add_soft_clause(add_w, cl);
        }
        self.unweighted_2_weighted();
        match &mut self.0 {
            IntObj::Weighted { soft_clauses, .. } => match soft_clauses.get_mut(&cl) {
                Some(old_w) => {
                    *old_w += add_w;
                    Some(*old_w - add_w)
                }
                None => soft_clauses.insert(cl, add_w),
            },
            IntObj::Unweighted { .. } => unreachable!(),
        }
    }

    /// Gets the weight of a soft literal
    #[must_use]
    pub fn lit_weight(&self, l: Lit) -> Option<usize> {
        match &self.0 {
            IntObj::Weighted { soft_lits, .. } => soft_lits.get(&l).copied(),
            IntObj::Unweighted {
                unit_weight,
                soft_lits,
                ..
            } => {
                if soft_lits.iter().any(|l2| l2 == &l) {
                    Some(unreachable_none!(*unit_weight))
                } else {
                    None
                }
            }
        }
    }

    /// Gets the weight of a soft clause
    #[must_use]
    pub fn clause_weight(&self, cl: &Clause) -> Option<usize> {
        match &self.0 {
            IntObj::Weighted { soft_clauses, .. } => soft_clauses.get(cl).copied(),
            IntObj::Unweighted {
                unit_weight,
                soft_clauses,
                ..
            } => {
                if soft_clauses.iter().any(|cl2| cl2 == cl) {
                    Some(unreachable_none!(*unit_weight))
                } else {
                    None
                }
            }
        }
    }

    /// Converts the objective to a set of soft clauses and an offset
    #[deprecated(
        since = "0.5.0",
        note = "as_soft_cls has been renamed to into_soft_cls and will be removed in a future release"
    )]
    #[must_use]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_soft_cls(self) -> (impl WClsIter, isize) {
        self.into_soft_cls()
    }

    /// Converts the objective to a set of soft clauses and an offset
    #[must_use]
    pub fn into_soft_cls(self) -> (impl WClsIter, isize) {
        match self.0 {
            IntObj::Unweighted {
                mut soft_clauses,
                soft_lits,
                offset,
                unit_weight,
            } => {
                soft_clauses.reserve(soft_lits.len());
                for l in soft_lits {
                    soft_clauses.push(clause![!l]);
                }
                let soft_clauses: Vec<(Clause, usize)> = soft_clauses
                    .into_iter()
                    .map(|cl| (cl, unreachable_none!(unit_weight)))
                    .collect();
                (soft_clauses, offset)
            }
            IntObj::Weighted {
                mut soft_clauses,
                soft_lits,
                offset,
            } => {
                soft_clauses.reserve(soft_lits.len());
                for (l, w) in soft_lits {
                    soft_clauses.insert(clause![!l], w);
                }
                let soft_clauses: Vec<(Clause, usize)> = Vec::from_iter(soft_clauses);
                (soft_clauses, offset)
            }
        }
    }

    /// Converts the objective to unweighted soft clauses, a unit weight and an offset. If the
    /// objective is weighted, the soft clause will appear as often as its
    /// weight in the output vector.
    #[deprecated(
        since = "0.5.0",
        note = "as_unweighted_soft_cls has been renamed to into_unweighted_soft_cls and will be removed in a future release"
    )]
    #[must_use]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_unweighted_soft_cls(self) -> (impl ClsIter, usize, isize) {
        self.into_unweighted_soft_cls()
    }

    /// Converts the objective to unweighted soft clauses, a unit weight and an offset. If the
    /// objective is weighted, the soft clause will appear as often as its
    /// weight in the output vector.
    #[must_use]
    pub fn into_unweighted_soft_cls(mut self) -> (impl ClsIter, usize, isize) {
        self.weighted_2_unweighted();
        match self.0 {
            IntObj::Weighted { .. } => unreachable!(),
            IntObj::Unweighted {
                offset,
                unit_weight,
                soft_lits,
                mut soft_clauses,
            } => {
                if let Some(unit_weight) = unit_weight {
                    soft_clauses.reserve(soft_lits.len());
                    for l in soft_lits {
                        soft_clauses.push(clause![!l]);
                    }
                    (soft_clauses, unit_weight, offset)
                } else {
                    (vec![], 1, offset)
                }
            }
        }
    }

    /// Converts the objective to soft literals in place, returning hardened clauses produced in
    /// the conversion.
    ///
    /// See [`Self::into_soft_lits`] if you do not need to convert in place.
    pub fn convert_to_soft_lits<VM>(&mut self, var_manager: &mut VM) -> Cnf
    where
        VM: ManageVars,
    {
        let mut cnf = Cnf::new();
        match &mut self.0 {
            IntObj::Weighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                cnf.clauses.reserve(soft_clauses.len());
                soft_lits.reserve(soft_clauses.len());
                for (mut cl, w) in soft_clauses.drain() {
                    debug_assert!(cl.len() > 1);
                    let relax_lit = var_manager.new_var().pos_lit();
                    cl.add(relax_lit);
                    cnf.add_clause(cl);
                    soft_lits.insert(relax_lit, w);
                }
            }
            IntObj::Unweighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                cnf.clauses.reserve(soft_clauses.len());
                soft_lits.reserve(soft_clauses.len());
                for mut cl in soft_clauses.drain(..) {
                    debug_assert!(cl.len() > 1);
                    let relax_lit = var_manager.new_var().pos_lit();
                    cl.add(relax_lit);
                    cnf.add_clause(cl);
                    soft_lits.push(relax_lit);
                }
            }
        }
        cnf
    }

    /// Converts the objective to a set of hard clauses, soft literals and an offset
    #[deprecated(
        since = "0.5.0",
        note = "as_soft_lits has been renamed to into_soft_lits and will be removed in a future release"
    )]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_soft_lits<VM>(self, var_manager: &mut VM) -> (Cnf, (impl WLitIter, isize))
    where
        VM: ManageVars,
    {
        self.into_soft_lits(var_manager)
    }

    /// Converts the objective to a set of hard clauses, soft literals and an offset
    ///
    /// See [`Self::convert_to_soft_lits`] for converting in place
    pub fn into_soft_lits<VM>(mut self, var_manager: &mut VM) -> (Cnf, (impl WLitIter, isize))
    where
        VM: ManageVars,
    {
        let cnf = self.convert_to_soft_lits(var_manager);
        self.unweighted_2_weighted();
        match self.0 {
            IntObj::Unweighted { .. } => unreachable!(),
            IntObj::Weighted {
                soft_lits,
                soft_clauses,
                offset,
            } => {
                debug_assert!(soft_clauses.is_empty());
                (cnf, (soft_lits, offset))
            }
        }
    }

    /// Converts the objective to hard clauses, unweighted soft literals, a unit
    /// weight and an offset. If the objective is weighted, the soft literals
    /// will appear as often as its weight in the output vector.
    #[deprecated(
        since = "0.5.0",
        note = "as_unweighted_soft_lits has been renamed to into_unweighted_soft_lits and will be removed in a future release"
    )]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_unweighted_soft_lits<VM>(
        self,
        var_manager: &mut VM,
    ) -> (Cnf, impl LitIter, usize, isize)
    where
        VM: ManageVars,
    {
        self.into_unweighted_soft_lits(var_manager)
    }

    /// Converts the objective to hard clauses, unweighted soft literals, a unit
    /// weight and an offset. If the objective is weighted, the soft literals
    /// will appear as often as its weight in the output vector.
    pub fn into_unweighted_soft_lits<VM>(
        mut self,
        var_manager: &mut VM,
    ) -> (Cnf, impl LitIter, usize, isize)
    where
        VM: ManageVars,
    {
        let cnf = self.convert_to_soft_lits(var_manager);
        match self.0 {
            IntObj::Weighted {
                soft_lits,
                soft_clauses,
                offset,
            } => {
                debug_assert!(soft_clauses.is_empty());
                let mut soft_unit_lits = vec![];
                soft_lits
                    .into_iter()
                    .for_each(|(l, w)| soft_unit_lits.resize(soft_unit_lits.len() + w, l));
                (cnf, soft_unit_lits, 1, offset)
            }
            IntObj::Unweighted {
                offset,
                unit_weight,
                soft_lits,
                soft_clauses,
            } => {
                debug_assert!(soft_clauses.is_empty());
                if let Some(unit_weight) = unit_weight {
                    (cnf, soft_lits, unit_weight, offset)
                } else {
                    (Cnf::new(), vec![], 1, offset)
                }
            }
        }
    }

    /// Gets the maximum variable in the objective
    #[must_use]
    pub fn max_var(&self) -> Option<Var> {
        let find_max = |mv, v| {
            if let Some(mv) = mv {
                if mv < v {
                    Some(v)
                } else {
                    Some(mv)
                }
            } else {
                Some(v)
            }
        };
        match &self.0 {
            IntObj::Weighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                let max_var = soft_lits
                    .iter()
                    .fold(None, |mv, (l, _)| find_max(mv, l.var()));
                soft_clauses.iter().fold(max_var, |mv, (cl, _)| {
                    cl.iter().fold(mv, |mv, l| find_max(mv, l.var()))
                })
            }
            IntObj::Unweighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                let max_var = soft_lits.iter().fold(None, |mv, l| find_max(mv, l.var()));
                soft_clauses.iter().fold(max_var, |mv, cl| {
                    cl.iter().fold(mv, |mv, l| find_max(mv, l.var()))
                })
            }
        }
    }

    /// Re-indexes all variables in the instance with a re-indexing variable manager
    #[must_use]
    pub fn reindex<R: ReindexVars>(self, reindexer: &mut R) -> Objective {
        match self.0 {
            IntObj::Weighted {
                soft_lits,
                soft_clauses,
                offset,
            } => {
                let soft_lits = soft_lits
                    .into_iter()
                    .map(|(l, w)| (reindexer.reindex_lit(l), w))
                    .collect::<RsHashMap<Lit, usize>>();
                let soft_clauses = soft_clauses
                    .into_iter()
                    .map(|(cl, w)| {
                        (
                            cl.into_iter().map(|l| reindexer.reindex_lit(l)).collect(),
                            w,
                        )
                    })
                    .collect();
                IntObj::Weighted {
                    soft_lits,
                    soft_clauses,
                    offset,
                }
                .into()
            }
            IntObj::Unweighted {
                soft_lits,
                soft_clauses,
                unit_weight,
                offset,
            } => {
                let soft_lits = soft_lits
                    .into_iter()
                    .map(|l| reindexer.reindex_lit(l))
                    .collect();
                let soft_clauses = soft_clauses
                    .into_iter()
                    .map(|cl| cl.into_iter().map(|l| reindexer.reindex_lit(l)).collect())
                    .collect();
                IntObj::Unweighted {
                    offset,
                    unit_weight,
                    soft_lits,
                    soft_clauses,
                }
                .into()
            }
        }
    }

    pub(crate) fn var_set(&self, varset: &mut BTreeSet<Var>) {
        match &self.0 {
            IntObj::Weighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                varset.extend(soft_lits.iter().map(|(l, _)| l.var()));
                varset.extend(
                    soft_clauses
                        .iter()
                        .flat_map(|(cl, _)| cl.iter().map(|l| l.var())),
                );
            }
            IntObj::Unweighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                varset.extend(soft_lits.iter().map(|l| l.var()));
                varset.extend(
                    soft_clauses
                        .iter()
                        .flat_map(|cl| cl.iter().map(|l| l.var())),
                );
            }
        }
    }

    /// Normalizes the objective to a unified representation. This sorts internal data structures.
    #[must_use]
    pub fn normalize(mut self) -> Self {
        match &mut self.0 {
            IntObj::Weighted { .. } => (),
            IntObj::Unweighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                soft_lits.sort_unstable();
                soft_clauses.sort_unstable();
            }
        };
        self
    }

    #[cfg(feature = "rand")]
    /// Randomly shuffles the order of literals
    #[must_use]
    pub fn shuffle(mut self) -> Self {
        use rand::seq::SliceRandom;
        match &mut self.0 {
            IntObj::Weighted { .. } => (),
            IntObj::Unweighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                let mut rng = rand::rng();
                (soft_lits[..]).shuffle(&mut rng);
                (soft_clauses[..]).shuffle(&mut rng);
            }
        };
        self
    }

    /// Gets a weighted literal iterator over only the soft literals
    ///
    /// # Errors
    ///
    /// If the objective contains soft clauses that this iterator would miss, returns
    /// [`RequiresSoftLits`]
    pub fn iter_soft_lits(&self) -> Result<impl WLitIter + '_, RequiresSoftLits> {
        if self.n_clauses() > 0 {
            return Err(RequiresSoftLits);
        }
        Ok(match &self.0 {
            IntObj::Weighted { soft_lits, .. } => ObjSoftLitIter::Weighted(soft_lits.iter()),
            IntObj::Unweighted {
                soft_lits,
                unit_weight,
                ..
            } => ObjSoftLitIter::Unweighted(soft_lits.iter(), unit_weight.unwrap_or(0)),
        })
    }

    /// Gets an iterator over the entire objective as soft clauses
    #[must_use]
    pub fn iter_soft_cls(&self) -> impl WClsIter + '_ {
        match &self.0 {
            IntObj::Weighted {
                soft_lits,
                soft_clauses,
                ..
            } => ObjSoftClauseIter::Weighted(soft_lits.iter(), soft_clauses.iter()),
            IntObj::Unweighted {
                unit_weight,
                soft_lits,
                soft_clauses,
                ..
            } => ObjSoftClauseIter::Unweighted(
                soft_lits.iter(),
                soft_clauses.iter(),
                unit_weight.unwrap_or(0),
            ),
        }
    }
}

/// A wrapper type for iterators over soft literals in an objective
enum ObjSoftLitIter<'a> {
    Weighted(hash_map::Iter<'a, Lit, usize>),
    Unweighted(slice::Iter<'a, Lit>, usize),
}

impl Iterator for ObjSoftLitIter<'_> {
    type Item = (Lit, usize);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ObjSoftLitIter::Weighted(iter) => iter.next().map(|(&l, &w)| (l, w)),
            ObjSoftLitIter::Unweighted(iter, w) => iter.next().map(|&l| (l, *w)),
        }
    }
}

/// A wrapper type for iterators over soft clauses in an objective
enum ObjSoftClauseIter<'a> {
    Weighted(
        hash_map::Iter<'a, Lit, usize>,
        hash_map::Iter<'a, Clause, usize>,
    ),
    Unweighted(slice::Iter<'a, Lit>, slice::Iter<'a, Clause>, usize),
}

impl Iterator for ObjSoftClauseIter<'_> {
    type Item = (Clause, usize);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ObjSoftClauseIter::Weighted(lit_iter, cl_iter) => {
                if let Some((&l, &w)) = lit_iter.next() {
                    return Some((clause![!l], w));
                }
                cl_iter.next().map(|(cl, &w)| (cl.clone(), w))
            }
            ObjSoftClauseIter::Unweighted(lit_iter, cl_iter, w) => {
                if let Some(&l) = lit_iter.next() {
                    return Some((clause![!l], *w));
                }
                cl_iter.next().map(|cl| (cl.clone(), *w))
            }
        }
    }
}

impl FromIterator<(Lit, usize)> for Objective {
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let mut obj = Self::default();
        iter.into_iter().for_each(|(l, w)| {
            obj.increase_soft_lit(w, l);
        });
        obj
    }
}

impl FromIterator<(Lit, isize)> for Objective {
    fn from_iter<T: IntoIterator<Item = (Lit, isize)>>(iter: T) -> Self {
        let mut obj = Self::default();
        iter.into_iter().for_each(|(l, w)| {
            obj.increase_soft_lit_int(w, l);
        });
        obj
    }
}

impl FromIterator<(Clause, usize)> for Objective {
    fn from_iter<T: IntoIterator<Item = (Clause, usize)>>(iter: T) -> Self {
        let mut obj = Self::default();
        iter.into_iter().for_each(|(cl, w)| {
            obj.increase_soft_clause(w, cl);
        });
        obj
    }
}

/// Type representing an optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Instance<VM: ManageVars = BasicVarManager> {
    pub(super) constrs: SatInstance<VM>,
    pub(super) obj: Objective,
}

impl<VM: ManageVars> Instance<VM> {
    /// Creates a new optimization instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> Self {
        Instance {
            constrs: SatInstance::new_with_manager(var_manager),
            obj: Objective::new(),
        }
    }

    /// Creates a new optimization instance from constraints and an objective
    pub fn compose(mut constraints: SatInstance<VM>, objective: Objective) -> Self {
        if let Some(mv) = objective.max_var() {
            constraints.var_manager_mut().increase_next_free(mv);
        }
        Instance {
            constrs: constraints,
            obj: objective,
        }
    }

    /// Decomposes the optimization instance to a [`SatInstance`] and an [`Objective`]
    pub fn decompose(mut self) -> (SatInstance<VM>, Objective) {
        if let Some(mv) = self.obj.max_var() {
            self.constrs.var_manager_mut().increase_next_free(mv + 1);
        }
        (self.constrs, self.obj)
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    #[deprecated(
        since = "0.5.0",
        note = "get_constraints has been renamed to constraints_mut and will be removed in a future release"
    )]
    pub fn get_constraints(&mut self) -> &mut SatInstance<VM> {
        &mut self.constrs
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    pub fn constraints_mut(&mut self) -> &mut SatInstance<VM> {
        &mut self.constrs
    }

    /// Gets a reference to the hard constraints
    pub fn constraints_ref(&self) -> &SatInstance<VM> {
        &self.constrs
    }

    /// Gets a mutable reference to the objective for modifying it
    #[deprecated(
        since = "0.5.0",
        note = "get_objective has been renamed to objective_mut and will be removed in a future release"
    )]
    pub fn get_objective(&mut self) -> &mut Objective {
        &mut self.obj
    }

    /// Gets a mutable reference to the objective for modifying it
    pub fn objective_mut(&mut self) -> &mut Objective {
        &mut self.obj
    }

    /// Gets a reference to the objective
    pub fn objective_ref(&self) -> &Objective {
        &self.obj
    }

    /// Reserves a new variable in the internal variable manager. This is a
    /// shortcut for `inst.get_constraints().var_manager().new_var()`.
    pub fn new_var(&mut self) -> Var {
        self.constraints_mut().var_manager_mut().new_var()
    }

    /// Reserves a new variable in the internal variable manager. This is a
    /// shortcut for `inst.get_constraints().var_manager().new_lit()`.
    pub fn new_lit(&mut self) -> Lit {
        self.constraints_mut().var_manager_mut().new_lit()
    }

    /// Gets the used variable with the highest index. This is a shortcut
    /// for `inst.get_constraints().var_manager().max_var()`.
    pub fn max_var(&self) -> Option<Var> {
        self.constraints_ref().var_manager_ref().max_var()
    }

    /// Converts the instance to a set of hard and soft clauses, an objective
    /// offset and a variable manager
    ///
    /// # Panic
    ///
    /// This might panic if the conversion to [`Cnf`] runs out of memory.
    pub fn into_hard_cls_soft_cls(self) -> (Cnf, (impl WClsIter, isize), VM) {
        let (cnf, mut vm) = self.constrs.into_cnf();
        if let Some(mv) = self.obj.max_var() {
            vm.increase_next_free(mv + 1);
        }
        (cnf, self.obj.into_soft_cls(), vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals, an
    /// objective offset and a variable manager
    ///
    /// # Panic
    ///
    /// This might panic if the conversion to [`Cnf`] runs out of memory.
    pub fn into_hard_cls_soft_lits(self) -> (Cnf, (impl WLitIter, isize), VM) {
        let (mut cnf, mut vm) = self.constrs.into_cnf();
        if let Some(mv) = self.obj.max_var() {
            vm.increase_next_free(mv + 1);
        }
        let (hard_softs, softs) = self.obj.into_soft_lits(&mut vm);
        cnf.extend(hard_softs);
        (cnf, softs, vm)
    }

    /// Converts the included variable manager to a different type
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> (Instance<VM2>, VM)
    where
        VM2: ManageVars,
        VMC: Fn(&VM) -> VM2,
    {
        let (constrs, vm) = self.constrs.change_var_manager(vm_converter);
        (
            Instance {
                constrs,
                obj: self.obj,
            },
            vm,
        )
    }

    /// Re-indexes all variables in the instance with a re-indexing variable manager
    #[must_use]
    pub fn reindex<R: ReindexVars>(self, mut reindexer: R) -> Instance<R> {
        let obj = self.obj.reindex(&mut reindexer);
        let constrs = self.constrs.reindex(reindexer);
        Instance { constrs, obj }
    }

    fn extend_var_set(&self, varset: &mut BTreeSet<Var>) {
        self.constrs.extend_var_set(varset);
        self.obj.var_set(varset);
    }

    /// Gets the set of variables in the instance
    pub fn var_set(&self) -> BTreeSet<Var> {
        let mut varset = BTreeSet::new();
        self.extend_var_set(&mut varset);
        varset
    }

    /// Re-index all variables in the instance in order
    ///
    /// If the re-indexing variable manager produces new free variables in order, this results in
    /// the variable _order_ being preserved with gaps in the variable space being closed
    #[must_use]
    pub fn reindex_ordered<R: ReindexVars>(self, mut reindexer: R) -> Instance<R> {
        let mut varset = BTreeSet::new();
        self.extend_var_set(&mut varset);
        // reindex variables in order to ensure ordered reindexing
        for var in varset {
            reindexer.reindex(var);
        }
        self.reindex(reindexer)
    }

    #[cfg(feature = "rand")]
    /// Randomly shuffles the order of constraints and the objective
    #[must_use]
    pub fn shuffle(mut self) -> Self {
        self.constrs = self.constrs.shuffle();
        self.obj = self.obj.shuffle();
        self
    }

    /// Writes the instance to a DIMACS WCNF file at a path
    ///
    /// # Performance
    ///
    /// For performance, consider using a [`std::io::BufWriter`] instance.
    #[deprecated(since = "0.5.0", note = "use write_dimacs_path instead")]
    #[allow(clippy::missing_errors_doc)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_dimacs_path<P: AsRef<Path>>(self, path: P) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        #[allow(deprecated)]
        self.to_dimacs(&mut writer)
    }

    /// Write to DIMACS WCNF (post 22)
    #[deprecated(since = "0.5.0", note = "use write_dimacs instead")]
    #[allow(clippy::missing_errors_doc)]
    #[allow(clippy::missing_panics_doc)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_dimacs<W: io::Write>(self, writer: &mut W) -> Result<(), io::Error> {
        #[allow(deprecated)]
        self.to_dimacs_with_encoders(
            |constr, cnf, vm| {
                card::default_encode_cardinality_constraint(constr, cnf, vm)
                    .expect("cardinality encoding ran out of memory");
            },
            |constr, cnf, vm| {
                pb::default_encode_pb_constraint(constr, cnf, vm)
                    .expect("pb encoding ran out of memory");
            },
            writer,
        )
    }

    /// Writes the instance to DIMACS WCNF (post 22) converting non-clausal
    /// constraints with specific encoders.
    #[deprecated(
        since = "0.5.0",
        note = "use convert_to_cnf_with_encoders and write_dimacs instead"
    )]
    #[allow(clippy::missing_errors_doc)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_dimacs_with_encoders<W, CardEnc, PBEnc>(
        self,
        card_encoder: CardEnc,
        pb_encoder: PBEnc,
        writer: &mut W,
    ) -> Result<(), io::Error>
    where
        W: io::Write,
        CardEnc: FnMut(CardConstraint, &mut Cnf, &mut dyn ManageVars),
        PBEnc: FnMut(PbConstraint, &mut Cnf, &mut dyn ManageVars),
    {
        let (cnf, vm) = self
            .constrs
            .into_cnf_with_encoders(card_encoder, pb_encoder);
        let soft_cls = self.obj.into_soft_cls();
        fio::dimacs::write_wcnf_annotated(writer, &cnf, soft_cls, Some(vm.n_used()))
    }

    /// Writes the instance to a DIMACS WCNF file at a path
    ///
    /// This requires that the instance is clausal, i.e., does not contain any non-converted
    /// cardinality of pseudo-boolean constraints. If necessary, the instance can be converted by
    /// [`SatInstance::convert_to_cnf`] or [`SatInstance::convert_to_cnf_with_encoders`] first.
    ///
    /// # Errors
    ///
    /// - If the instance is not clausal, returns [`RequiresClausal`]
    /// - Returns [`io::Error`] on errors during writing
    pub fn write_dimacs_path<P: AsRef<Path>>(&self, path: P) -> anyhow::Result<()> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.write_dimacs(&mut writer)
    }

    /// Write to DIMACS WCNF (post 22)
    ///
    /// This requires that the instance is clausal, i.e., does not contain any non-converted
    /// cardinality of pseudo-boolean constraints. If necessary, the instance can be converted by
    /// [`SatInstance::convert_to_cnf`] or [`SatInstance::convert_to_cnf_with_encoders`] first.
    ///
    /// # Performance
    ///
    /// For performance, consider using a [`std::io::BufWriter`] instance.
    ///
    /// # Errors
    ///
    /// - If the instance is not clausal, returns [`RequiresClausal`]
    /// - Returns [`io::Error`] on errors during writing
    pub fn write_dimacs<W: io::Write>(&self, writer: &mut W) -> anyhow::Result<()> {
        if self.constrs.n_cards() > 0 || self.constrs.n_pbs() > 0 {
            return Err(RequiresClausal.into());
        }
        let n_vars = self.constrs.n_vars();
        let offset = self.obj.offset();
        let soft_cls = self.obj.iter_soft_cls();
        Ok(fio::dimacs::write_wcnf_annotated(
            writer,
            &self.constrs.cnf,
            (soft_cls, offset),
            Some(n_vars),
        )?)
    }

    /// Writes the instance to an OPB file at a path
    ///
    /// # Performance
    ///
    /// For performance, consider using a [`std::io::BufWriter`] instance.
    #[deprecated(since = "0.5.0", note = "use write_opb_path instead")]
    #[allow(clippy::missing_errors_doc)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_opb_path<P: AsRef<Path>>(
        self,
        path: P,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        #[allow(deprecated)]
        self.to_opb(&mut writer, opts)
    }

    /// Writes the instance to an OPB file
    #[deprecated(since = "0.5.0", note = "use write_opb instead")]
    #[allow(clippy::missing_errors_doc)]
    #[allow(clippy::missing_panics_doc)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_opb<W: io::Write>(
        mut self,
        writer: &mut W,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        let var_manager = self.constrs.var_manager_mut();
        self.obj.convert_to_soft_lits(var_manager);
        let offset = self.obj.offset();
        let iter = self.obj.iter_soft_lits().unwrap();
        fio::opb::write_opt::<W, VM, _>(writer, &self.constrs, (iter, offset), opts)
    }

    /// Writes the instance to an OPB file at a path
    ///
    /// This requires that the objective does not contain soft clauses. If it does, use
    /// [`Objective::convert_to_soft_lits`] first.
    ///
    /// # Errors
    ///
    /// - If the objective contains soft literals, returns [`RequiresSoftLits`]
    /// - Returns [`io::Error`] on errors during writing
    pub fn write_opb_path<P: AsRef<Path>>(
        &self,
        path: P,
        opts: fio::opb::Options,
    ) -> anyhow::Result<()> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.write_opb(&mut writer, opts)
    }

    /// Writes the instance to an OPB file
    ///
    /// This requires that the objective does not contain soft clauses. If it does, use
    /// [`Objective::convert_to_soft_lits`] first.
    ///
    /// # Performance
    ///
    /// For performance, consider using a [`std::io::BufWriter`] instance(crate).
    ///
    /// # Errors
    ///
    /// - If the objective contains soft literals, returns [`RequiresSoftLits`]
    /// - Returns [`io::Error`] on errors during writing
    pub fn write_opb<W: io::Write>(
        &self,
        writer: &mut W,
        opts: fio::opb::Options,
    ) -> anyhow::Result<()> {
        let offset = self.obj.offset();
        let iter = self.obj.iter_soft_lits()?;
        Ok(fio::opb::write_opt::<W, VM, _>(
            writer,
            &self.constrs,
            (iter, offset),
            opts,
        )?)
    }

    /// Calculates the objective value of an assignment. Returns [`None`] if the
    /// assignment is not a solution.
    pub fn cost(&self, assign: &Assignment) -> Option<isize> {
        if self.constrs.evaluate(assign) != TernaryVal::True {
            return None;
        }
        Some(self.obj.evaluate(assign))
    }
}

impl<VM: ManageVars + Default> Instance<VM> {
    /// Creates a new optimization instance
    #[must_use]
    pub fn new() -> Self {
        Instance {
            constrs: SatInstance::new(),
            obj: Objective::new(),
        }
    }

    /// Parses a DIMACS instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this reader is either the [old DIMACS
    /// WCNF](https://maxsat-evaluations.github.io/2017/rules.html#input) format
    /// used in the MaxSAT evaluation before 2022 or the [new
    /// format](https://maxsat-evaluations.github.io/2022/rules.html#input) used
    /// since 2022.
    ///
    /// If a DIMACS MCNF file is passed to this function, all objectives but the
    /// first are ignored.
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_dimacs<R: io::BufRead>(reader: &mut R) -> anyhow::Result<Self> {
        Self::from_dimacs_with_idx(reader, 0)
    }

    /// Parses a DIMACS instance from a reader object, selecting the objective
    /// with index `obj_idx` if multiple are available. The index starts at 0.
    /// For more details see [`Instance::from_dimacs`].
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_dimacs_with_idx<R: io::BufRead>(
        reader: &mut R,
        obj_idx: usize,
    ) -> anyhow::Result<Self> {
        fio::dimacs::parse_wcnf_with_idx(reader, obj_idx)
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`Instance::from_dimacs`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_dimacs_path<P: AsRef<Path>>(path: P) -> anyhow::Result<Self> {
        let mut reader = fio::open_compressed_uncompressed_read(path)?;
        Self::from_dimacs(&mut reader)
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`Instance::from_dimacs_with_idx`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_dimacs_path_with_idx<P: AsRef<Path>>(
        path: P,
        obj_idx: usize,
    ) -> anyhow::Result<Self> {
        let mut reader = fio::open_compressed_uncompressed_read(path)?;
        Self::from_dimacs_with_idx(&mut reader, obj_idx)
    }

    /// Parses an OPB instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the OPB format for
    /// pseudo-boolean optimization instances. For details on the file format
    /// see [here](https://www.cril.univ-artois.fr/PB12/format.pdf).
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_opb<R: io::BufRead>(
        reader: &mut R,
        opts: fio::opb::Options,
    ) -> anyhow::Result<Self> {
        Self::from_opb_with_idx(reader, 0, opts)
    }

    /// Parses an OPB instance from a reader object, selecting the objective
    /// with index `obj_idx` if multiple are available. The index starts at 0.
    /// For more details see [`Instance::from_opb`].
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_opb_with_idx<R: io::BufRead>(
        reader: &mut R,
        obj_idx: usize,
        opts: fio::opb::Options,
    ) -> anyhow::Result<Self> {
        fio::opb::parse_opt_with_idx(reader, obj_idx, opts)
    }

    /// Parses an OPB instance from a file path. For more details see
    /// [`Instance::from_opb`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_opb_path<P: AsRef<Path>>(path: P, opts: fio::opb::Options) -> anyhow::Result<Self> {
        let mut reader = fio::open_compressed_uncompressed_read(path)?;
        Self::from_opb(&mut reader, opts)
    }

    /// Parses an OPB instance from a file path, selecting the objective with
    /// index `obj_idx` if multiple are available. The index starts at 0. For
    /// more details see [`Instance::from_opb`]. With feature
    /// `compression` supports bzip2 and gzip compression, detected by the file
    /// extension.
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_opb_path_with_idx<P: AsRef<Path>>(
        path: P,
        obj_idx: usize,
        opts: fio::opb::Options,
    ) -> anyhow::Result<Self> {
        let mut reader = fio::open_compressed_uncompressed_read(path)?;
        Self::from_opb_with_idx(&mut reader, obj_idx, opts)
    }

    /// Solves the instance with a [`maxsat::Solve`] algorithm
    ///
    /// # Panics
    ///
    /// - If any interaction with the solver errors
    /// - If the objective value overflows [`isize::MAX`]
    pub fn solve_maxsat<Alg>(self) -> Option<(Assignment, isize)>
    where
        Alg: maxsat::Solve,
        Alg::Solver: Default,
    {
        let mut solver = Alg::Solver::default();
        let (cnf, vm) = self.constrs.into_cnf();
        let mut vm = if let Some(max_var) = cmp::max(vm.max_var(), self.obj.max_var()) {
            BasicVarManager::from_next_free(max_var + 1)
        } else {
            BasicVarManager::default()
        };
        solver
            .add_cnf(cnf)
            .expect("failed adding clauses to solver");
        let handle_soft_cls = |(mut cl, weight): (Clause, usize)| {
            debug_assert!(!cl.is_empty());
            if cl.len() == 1 {
                return (!cl[0], weight);
            }
            let blit = vm.new_lit();
            cl.add(!blit);
            solver
                .add_clause(cl)
                .expect("failed adding clause to solver");
            (blit, weight)
        };
        let (iter, offset) = self.obj.into_soft_cls();
        let obj: Vec<_> = iter.into_iter().map(handle_soft_cls).collect();
        let (sol, cost) = Alg::solve(&mut solver, &obj)?;
        Some((
            sol,
            offset
                .checked_add_unsigned(cost)
                .expect("objective value overflow"),
        ))
    }
}

impl<VM: ManageVars + Default> FromIterator<WcnfLine> for Instance<VM> {
    fn from_iter<T: IntoIterator<Item = WcnfLine>>(iter: T) -> Self {
        let mut inst = Self::default();
        for line in iter {
            match line {
                WcnfLine::Comment(_) => (),
                WcnfLine::Hard(cl) => inst.constraints_mut().add_clause(cl),
                WcnfLine::Soft(cl, w) => {
                    inst.objective_mut().add_soft_clause(w, cl);
                }
            }
        }
        inst
    }
}
