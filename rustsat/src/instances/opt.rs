//! # Optimization Instance Representations

use std::{cmp, io, path::Path};

use crate::{
    clause,
    encodings::{card, pb},
    types::{
        constraints::{CardConstraint, PBConstraint},
        Assignment, Clause, ClsIter, Lit, LitIter, RsHashMap, TernaryVal, Var, WClsIter, WLitIter,
    },
};

/// Internal objective type for not exposing variants
#[derive(Clone, Debug, PartialEq, Eq)]
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
pub struct Objective(IntObj);

impl From<IntObj> for Objective {
    fn from(obj: IntObj) -> Self {
        Self(obj)
    }
}

impl Default for Objective {
    fn default() -> Self {
        Self(IntObj::Unweighted {
            offset: Default::default(),
            unit_weight: Default::default(),
            soft_lits: Default::default(),
            soft_clauses: Default::default(),
        })
    }
}

impl Objective {
    /// Creates a new empty objective
    pub fn new() -> Self {
        Default::default()
    }

    /// Checks if the objective is empty, i.e., has constant value 0
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
    pub fn n_lits(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_lits, .. } => soft_lits.len(),
            IntObj::Unweighted { soft_lits, .. } => soft_lits.len(),
        }
    }

    /// Gets the number of soft clauses in the objective
    pub fn n_clauses(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_clauses, .. } => soft_clauses.len(),
            IntObj::Unweighted { soft_clauses, .. } => soft_clauses.len(),
        }
    }

    /// Gets the number of soft literals and clauses in the objective
    pub fn n_softs(&self) -> usize {
        self.n_lits() + self.n_clauses()
    }

    /// Gets the weight sum of soft literals
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

    /// Gets the weight sum of all softs
    pub fn weight_sum(&self) -> usize {
        self.lit_weight_sum() + self.clause_weight_sum()
    }

    /// Gets the maximum weight of a soft literal
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
    pub fn max_weight(&self) -> usize {
        cmp::max(self.max_lit_weight(), self.max_clause_weight())
    }

    /// Gets the minimum weight of a soft literal
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
    pub fn min_clause_weight(&self) -> usize {
        match &self.0 {
            IntObj::Weighted { soft_clauses, .. } => soft_clauses
                .iter()
                .fold(usize::MAX, |s, (_, w)| if *w < s { *w } else { s }),
            IntObj::Unweighted { unit_weight, .. } => unit_weight.unwrap_or(0),
        }
    }

    /// Gets the minimum weight of any soft
    pub fn min_weight(&self) -> usize {
        cmp::min(self.min_lit_weight(), self.min_clause_weight())
    }

    /// Evaluates the objective under an assignment. Only clauses _falsified_
    /// and literals _set_ incur cost.
    pub fn evaluate(&self, sol: &Assignment) -> isize {
        self.evaluate_no_offset(sol) as isize + self.offset()
    }

    /// Evaluates the objective under and assignment without considering the
    /// offset. Only clauses _falsified_ and literals _set_ incur cost.
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
            IntObj::Weighted { offset, .. } => *offset = new_offset,
            IntObj::Unweighted { offset, .. } => *offset = new_offset,
        }
    }

    /// Gets the global value offset
    pub fn offset(&self) -> isize {
        match &self.0 {
            IntObj::Weighted { offset, .. } => *offset,
            IntObj::Unweighted { offset, .. } => *offset,
        }
    }

    /// Increases the value offset
    pub fn increase_offset(&mut self, offset_incr: isize) {
        match &mut self.0 {
            IntObj::Weighted { offset, .. } => *offset += offset_incr,
            IntObj::Unweighted { offset, .. } => *offset += offset_incr,
        }
    }

    /// Checks if the objective is weighted
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
                        soft_lits: soft_lits.iter_mut().map(|l| (*l, *unit_weight)).collect(),
                        soft_clauses: soft_clauses
                            .iter_mut()
                            .map(|cl| (cl.clone(), *unit_weight))
                            .collect(),
                    }
                    .into()
                } else {
                    *self = IntObj::Weighted {
                        offset: *offset,
                        soft_lits: RsHashMap::default(),
                        soft_clauses: RsHashMap::default(),
                    }
                    .into()
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
                    .iter_mut()
                    .for_each(|(l, w)| soft_unit_lits.resize(soft_unit_lits.len() + *w, *l));
                let mut soft_unit_clauses = vec![];
                soft_clauses.iter_mut().for_each(|(cl, w)| {
                    soft_unit_clauses.resize(soft_unit_clauses.len() + *w, cl.clone())
                });
                *self = IntObj::Unweighted {
                    offset: *offset,
                    unit_weight: Some(1),
                    soft_lits: soft_unit_lits,
                    soft_clauses: soft_unit_clauses,
                }
                .into()
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
                        return Some(unit_weight.unwrap());
                    }
                    None
                } else {
                    match unit_weight {
                        Some(unit_weight) => {
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
                        }
                        None => {
                            soft_lits.push(l);
                            *unit_weight = Some(w);
                            None
                        }
                    }
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
            IntObj::Unweighted { .. } => panic!(),
        }
    }

    /// Increases a soft literal with possibly negative weight. Internally all
    /// weights are positive, negative weights are represented by a global value
    /// offset and negated literals.
    /// This does _not_ update weights but increases them, since otherwise,
    /// adding literal l with a positive weight and afterwards -l with a
    /// negative weight would mess up the state.
    pub fn increase_soft_lit_int(&mut self, add_w: isize, l: Lit) {
        if add_w < 0 {
            self.increase_offset(add_w);
            self.increase_soft_lit(-add_w as usize, !l);
        } else {
            self.increase_soft_lit(add_w as usize, l);
        }
    }

    /// Adds a soft clause or updates its weight. Returns the old weight, if
    /// the clause was already in the objective.
    pub fn add_soft_clause(&mut self, w: usize, cl: Clause) -> Option<usize> {
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
                        return Some(unit_weight.unwrap());
                    }
                    None
                } else {
                    match unit_weight {
                        Some(unit_weight) => {
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
                        }
                        None => {
                            soft_clauses.push(cl);
                            *unit_weight = Some(w);
                            None
                        }
                    }
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
            IntObj::Unweighted { .. } => panic!(),
        }
    }

    /// Gets the weight of a soft literal
    pub fn lit_weight(&self, l: Lit) -> Option<usize> {
        match &self.0 {
            IntObj::Weighted { soft_lits, .. } => soft_lits.get(&l).copied(),
            IntObj::Unweighted {
                unit_weight,
                soft_lits,
                ..
            } => {
                if soft_lits.iter().any(|l2| l2 == &l) {
                    Some(unit_weight.unwrap())
                } else {
                    None
                }
            }
        }
    }

    /// Gets the weight of a soft clause
    pub fn clause_weight(&self, cl: &Clause) -> Option<usize> {
        match &self.0 {
            IntObj::Weighted { soft_clauses, .. } => soft_clauses.get(cl).copied(),
            IntObj::Unweighted {
                unit_weight,
                soft_clauses,
                ..
            } => {
                if soft_clauses.iter().any(|cl2| cl2 == cl) {
                    Some(unit_weight.unwrap())
                } else {
                    None
                }
            }
        }
    }

    /// Converts the objective to a set of soft clauses and an offset
    pub fn as_soft_cls(self) -> (impl WClsIter, isize) {
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
                    .map(|cl| (cl, unit_weight.unwrap()))
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
    pub fn as_unweighted_soft_cls(mut self) -> (impl ClsIter, usize, isize) {
        self.weighted_2_unweighted();
        match self.0 {
            IntObj::Weighted { .. } => panic!(),
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

    /// Converts the objective to a set of hard clauses, soft literals and an offset
    pub fn as_soft_lits<VM>(mut self, var_manager: &mut VM) -> (Cnf, (impl WLitIter, isize))
    where
        VM: ManageVars,
    {
        self.unweighted_2_weighted();
        match self.0 {
            IntObj::Unweighted { .. } => panic!(),
            IntObj::Weighted {
                mut soft_lits,
                soft_clauses,
                offset,
            } => {
                let mut cnf = Cnf::new();
                cnf.clauses.reserve(soft_clauses.len());
                soft_lits.reserve(soft_clauses.len());
                for (mut cl, w) in soft_clauses {
                    if cl.len() > 1 {
                        let relax_lit = var_manager.new_var().pos_lit();
                        cl.add(relax_lit);
                        cnf.add_clause(cl);
                        soft_lits.insert(relax_lit, w);
                    } else {
                        assert!(cl.len() == 1);
                        soft_lits.insert(!cl[0], w);
                    }
                }
                (cnf, (soft_lits, offset))
            }
        }
    }

    /// Converts the objective to hard clauses, unweighted soft literals, a unit
    /// weight and an offset. If the objective is weighted, the soft literals
    /// will appear as often as its weight in the output vector.
    pub fn as_unweighted_soft_lits<VM>(
        self,
        var_manager: &mut VM,
    ) -> (Cnf, impl LitIter, usize, isize)
    where
        VM: ManageVars,
    {
        match self.0 {
            IntObj::Weighted { .. } => {
                let (cnf, softs) = self.as_soft_lits(var_manager);
                let mut soft_unit_lits = vec![];
                softs
                    .0
                    .into_iter()
                    .for_each(|(l, w)| soft_unit_lits.resize(soft_unit_lits.len() + w, l));
                (cnf, soft_unit_lits, 1, softs.1)
            }
            IntObj::Unweighted {
                offset,
                unit_weight,
                mut soft_lits,
                soft_clauses,
            } => {
                if let Some(unit_weight) = unit_weight {
                    let mut cnf = Cnf::new();
                    cnf.clauses.reserve(soft_clauses.len());
                    soft_lits.reserve(soft_clauses.len());
                    for mut cl in soft_clauses {
                        if cl.len() > 1 {
                            let relax_lit = var_manager.new_var().pos_lit();
                            cl.add(relax_lit);
                            cnf.add_clause(cl);
                            soft_lits.push(relax_lit);
                        } else {
                            assert!(cl.len() == 1);
                            soft_lits.push(!cl[0]);
                        }
                    }
                    (cnf, soft_lits, unit_weight, offset)
                } else {
                    (Cnf::new(), vec![], 1, offset)
                }
            }
        }
    }

    /// Gets the maximum variable in the objective
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

    /// Reindexes all variables in the instance with a reindexing variable manager
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

    /// Normalizes the objective to a unified representation. This sorts internal data structures.
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
    pub fn shuffle(mut self) -> Self {
        use rand::seq::SliceRandom;
        match &mut self.0 {
            IntObj::Weighted { .. } => (),
            IntObj::Unweighted {
                soft_lits,
                soft_clauses,
                ..
            } => {
                let mut rng = rand::thread_rng();
                (soft_lits[..]).shuffle(&mut rng);
                (soft_clauses[..]).shuffle(&mut rng);
            }
        };
        self
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
pub struct OptInstance<VM: ManageVars = BasicVarManager> {
    pub(super) constrs: SatInstance<VM>,
    pub(super) obj: Objective,
}

impl<VM: ManageVars> OptInstance<VM> {
    /// Creates a new optimization instance with a specific var manager
    pub fn new_with_manager(var_manager: VM) -> Self {
        OptInstance {
            constrs: SatInstance::new_with_manager(var_manager),
            obj: Objective::new(),
        }
    }

    /// Creates a new optimization instance from constraints and an objective
    pub fn compose(mut constraints: SatInstance<VM>, objective: Objective) -> Self {
        if let Some(mv) = objective.max_var() {
            constraints.var_manager().increase_next_free(mv);
        }
        OptInstance {
            constrs: constraints,
            obj: objective,
        }
    }

    /// Decomposes the optimization instance to a [`SatInstance`] and an [`Objective`]
    pub fn decompose(mut self) -> (SatInstance<VM>, Objective) {
        if let Some(mv) = self.obj.max_var() {
            self.constrs.var_manager.increase_next_free(mv + 1);
        }
        (self.constrs, self.obj)
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    pub fn get_constraints(&mut self) -> &mut SatInstance<VM> {
        &mut self.constrs
    }

    /// Gets a mutable reference to the objective for modifying it
    pub fn get_objective(&mut self) -> &mut Objective {
        &mut self.obj
    }

    /// Converts the instance to a set of hard and soft clauses, an objective
    /// offset and a variable manager
    pub fn as_hard_cls_soft_cls(self) -> (Cnf, (impl WClsIter, isize), VM) {
        let (cnf, mut vm) = self.constrs.as_cnf();
        if let Some(mv) = self.obj.max_var() {
            vm.increase_next_free(mv + 1);
        }
        (cnf, self.obj.as_soft_cls(), vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals, an
    /// objective offset and a variable manager
    pub fn as_hard_cls_soft_lits(self) -> (Cnf, (impl WLitIter, isize), VM) {
        let (mut cnf, mut vm) = self.constrs.as_cnf();
        if let Some(mv) = self.obj.max_var() {
            vm.increase_next_free(mv + 1);
        }
        let (hard_softs, softs) = self.obj.as_soft_lits(&mut vm);
        cnf.extend(hard_softs);
        (cnf, softs, vm)
    }

    /// Converts the included variable manager to a different type
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> (OptInstance<VM2>, VM)
    where
        VM2: ManageVars,
        VMC: Fn(&VM) -> VM2,
    {
        let (constrs, vm) = self.constrs.change_var_manager(vm_converter);
        (
            OptInstance {
                constrs,
                obj: self.obj,
            },
            vm,
        )
    }

    /// Reindexes all variables in the instance with a reindexing variable manager
    pub fn reindex<R: ReindexVars>(self, mut reindexer: R) -> OptInstance<R> {
        let obj = self.obj.reindex(&mut reindexer);
        let constrs = self.constrs.reindex(reindexer);
        OptInstance { constrs, obj }
    }

    #[cfg(feature = "rand")]
    /// Randomly shuffles the order of constraints and the objective
    pub fn shuffle(mut self) -> Self {
        self.constrs = self.constrs.shuffle();
        self.obj = self.obj.shuffle();
        self
    }

    /// Writes the instance to a DIMACS WCNF file at a path
    pub fn to_dimacs_path<P: AsRef<Path>>(self, path: P) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.to_dimacs(&mut writer)
    }

    /// Write to DIMACS WCNF (post 22)
    pub fn to_dimacs<W: io::Write>(self, writer: &mut W) -> Result<(), io::Error> {
        self.to_dimacs_with_encoders(
            card::default_encode_cardinality_constraint,
            pb::default_encode_pb_constraint,
            writer,
        )
    }

    /// Writes the instance to DIMACS WCNF (post 22) converting non-clausal
    /// constraints with specific encoders.
    pub fn to_dimacs_with_encoders<W, CardEnc, PBEnc>(
        self,
        card_encoder: CardEnc,
        pb_encoder: PBEnc,
        writer: &mut W,
    ) -> Result<(), io::Error>
    where
        W: io::Write,
        CardEnc: FnMut(CardConstraint, &mut Cnf, &mut dyn ManageVars),
        PBEnc: FnMut(PBConstraint, &mut Cnf, &mut dyn ManageVars),
    {
        let (cnf, vm) = self.constrs.as_cnf_with_encoders(card_encoder, pb_encoder);
        let soft_cls = self.obj.as_soft_cls();
        fio::dimacs::write_wcnf_annotated(writer, cnf, soft_cls, vm.max_var())
    }

    /// Writes the instance to an OPB file at a path
    pub fn to_opb_path<P: AsRef<Path>>(
        self,
        path: P,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.to_opb(&mut writer, opts)
    }

    /// Writes the instance to an OPB file
    pub fn to_opb<W: io::Write>(
        self,
        writer: &mut W,
        opts: fio::opb::Options,
    ) -> Result<(), io::Error> {
        fio::opb::write_opt::<W, VM>(writer, self, opts)
    }

    /// Calculates the objective value of an assignment. Returns [`None`] if the
    /// assignment is not a solution.
    pub fn cost(&self, assign: &Assignment) -> Option<isize> {
        if !self.constrs.is_sat(assign) {
            return None;
        }
        Some(self.obj.evaluate(assign))
    }
}

impl<VM: ManageVars + Default> OptInstance<VM> {
    /// Creates a new optimization instance
    pub fn new() -> Self {
        OptInstance {
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
    pub fn from_dimacs<R: io::Read>(reader: R) -> Result<Self, fio::ParsingError> {
        Self::from_dimacs_with_idx(reader, 0)
    }

    /// Parses a DIMACS instance from a reader object, selecting the objective
    /// with index `obj_idx` if multiple are available. The index starts at 0.
    /// For more details see [`OptInstance::from_dimacs`].
    pub fn from_dimacs_with_idx<R: io::Read>(
        reader: R,
        obj_idx: usize,
    ) -> Result<Self, fio::ParsingError> {
        Ok(fio::dimacs::parse_wcnf_with_idx(reader, obj_idx)?)
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`OptInstance::from_dimacs`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_dimacs_path<P: AsRef<Path>>(path: P) -> Result<Self, fio::ParsingError> {
        match fio::open_compressed_uncompressed_read(path) {
            Err(why) => Err(fio::ParsingError::IO(why)),
            Ok(reader) => OptInstance::from_dimacs(reader),
        }
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`OptInstance::from_dimacs_with_idx`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_dimacs_path_with_idx<P: AsRef<Path>>(
        path: P,
        obj_idx: usize,
    ) -> Result<Self, fio::ParsingError> {
        match fio::open_compressed_uncompressed_read(path) {
            Err(why) => Err(fio::ParsingError::IO(why)),
            Ok(reader) => OptInstance::from_dimacs_with_idx(reader, obj_idx),
        }
    }

    /// Parses an OPB instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the OPB format for
    /// pseudo-boolean optimization instances. For details on the file format
    /// see [here](https://www.cril.univ-artois.fr/PB12/format.pdf).
    pub fn from_opb<R: io::Read>(
        reader: R,
        opts: fio::opb::Options,
    ) -> Result<Self, fio::ParsingError> {
        OptInstance::from_opb_with_idx(reader, 0, opts)
    }

    /// Parses an OPB instance from a reader object, selecting the objective
    /// with index `obj_idx` if multiple are available. The index starts at 0.
    /// For more details see [`OptInstance::from_opb`].
    pub fn from_opb_with_idx<R: io::Read>(
        reader: R,
        obj_idx: usize,
        opts: fio::opb::Options,
    ) -> Result<Self, fio::ParsingError> {
        Ok(fio::opb::parse_opt_with_idx(reader, obj_idx, opts)?)
    }

    /// Parses an OPB instance from a file path. For more details see
    /// [`OptInstance::from_opb`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_opb_path<P: AsRef<Path>>(
        path: P,
        opts: fio::opb::Options,
    ) -> Result<Self, fio::ParsingError> {
        match fio::open_compressed_uncompressed_read(path) {
            Err(why) => Err(fio::ParsingError::IO(why)),
            Ok(reader) => OptInstance::from_opb(reader, opts),
        }
    }

    /// Parses an OPB instance from a file path, selecting the objective with
    /// index `obj_idx` if multiple are available. The index starts at 0. For
    /// more details see [`OptInstance::from_opb`]. With feature
    /// `compression` supports bzip2 and gzip compression, detected by the file
    /// extension.
    pub fn from_opb_path_with_idx<P: AsRef<Path>>(
        path: P,
        obj_idx: usize,
        opts: fio::opb::Options,
    ) -> Result<Self, fio::ParsingError> {
        match fio::open_compressed_uncompressed_read(path) {
            Err(why) => Err(fio::ParsingError::IO(why)),
            Ok(reader) => OptInstance::from_opb_with_idx(reader, obj_idx, opts),
        }
    }
}

impl<VM: ManageVars + Default> FromIterator<WcnfLine> for OptInstance<VM> {
    fn from_iter<T: IntoIterator<Item = WcnfLine>>(iter: T) -> Self {
        let mut inst = Self::default();
        for line in iter {
            match line {
                WcnfLine::Comment(_) => (),
                WcnfLine::Hard(cl) => inst.get_constraints().add_clause(cl),
                WcnfLine::Soft(cl, w) => {
                    inst.get_objective().add_soft_clause(w, cl);
                }
            }
        }
        inst
    }
}
