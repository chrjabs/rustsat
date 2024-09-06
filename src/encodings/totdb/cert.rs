//! # Certified Totalizer Database

use std::ops;

use crate::{
    encodings::{
        atomics,
        nodedb::{NodeById, NodeId, NodeLike},
    },
    instances::ManageVars,
    lit,
    types::{Lit, Var},
    utils::unreachable_none,
};

use pidgeons::{AbsConstraintId, VarLike};

use super::{con_idx, LitData, Node, PrecondOutcome, Semantics, UnitNode, UnweightedPrecondResult};

/// Helper to get the output literal with a given index
macro_rules! get_olit {
    ($self:expr, $id:expr, $idx:expr) => {
        match &$self.nodes[$id.0] {
            Node::Leaf(lit) => {
                debug_assert_eq!($idx, 0);
                *lit
            }
            Node::Unit(UnitNode { lits, .. }) => *unreachable_none!(lits[$idx].lit()),
            Node::General(_) | Node::Dummy => unreachable!(),
        }
    };
}

impl super::Db {
    fn define_semantics<W>(
        &mut self,
        id: NodeId,
        val: usize,
        typ: SemDefTyp,
        leafs: impl Iterator<Item = (Lit, usize)>,
        proof: &mut pidgeons::Proof<W>,
    ) -> std::io::Result<SemDefinition>
    where
        W: std::io::Write,
    {
        use crate::types::constraints::PbConstraint;

        debug_assert!(val <= self[id].max_val() + 1);
        if let Some(defs) = self.semantic_defs.get(&(id, val)) {
            return Ok(defs.get(typ).into());
        }
        if self[id].is_leaf() {
            if val == 0 {
                let olit = *self[id].lit(1).unwrap();
                return Ok(olit.into());
            }
            return Ok(SemDefinition::None);
        }
        // must always add both semantic definitions straight away, later they might not be
        // trivially redundant anymore
        let defs = if val == 0 {
            let sem = PbConstraint::new_lb(
                leafs.map(|(l, w)| {
                    (
                        l,
                        isize::try_from(w).expect("cannot handle weights larger than `isize::MAX`"),
                    )
                }),
                isize::try_from(val).expect("cannot handle values larger than `isize::MAX`"),
            );
            SemDefs::new(None, Some(proof.redundant::<Var, _, _, _>(&sem, [], [])?))
        } else if val > self[id].max_val() {
            let sem = PbConstraint::new_lb(
                leafs.map(|(l, w)| {
                    (
                        !l,
                        isize::try_from(w).expect("cannot handle values larger than `isize::MAX`"),
                    )
                }),
                0,
            );
            SemDefs::new(Some(proof.redundant::<Var, _, _, _>(&sem, [], [])?), None)
        } else {
            let olit = *self[id].lit(val).unwrap();
            let sem = PbConstraint::new_lb(
                leafs.map(|(l, w)| {
                    (
                        l,
                        isize::try_from(w).expect("cannot handle weights larger than `isize::MAX`"),
                    )
                }),
                isize::try_from(val).expect("cannot handle values larger than `isize::MAX`"),
            );
            SemDefs::new(
                Some(proof.redundant(
                    &atomics::pb_impl_lit(&sem, olit),
                    [olit.var().substitute_fixed(true)],
                    None,
                )?),
                Some(proof.redundant(
                    &atomics::lit_impl_pb(olit, &sem),
                    [olit.var().substitute_fixed(false)],
                    None,
                )?),
            )
        };
        self.semantic_defs.insert((id, val), defs);
        Ok(defs.get(typ).into())
    }

    /// Gets the semantic definitions for an output value, if they exist
    #[must_use]
    pub fn get_semantics(&self, id: NodeId, value: usize) -> Option<SemDefs> {
        self.semantic_defs.get(&(id, value)).copied()
    }

    /// Generates the encoding to define the positive output literal with value `val`, if it is not
    /// already defined. The derivation of the generated clauses is certified in the provided
    /// proof. Recurses down the tree. The returned literal is the output literal and the encoding
    /// is added to the `collector`.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn define_weighted_cert<Col, W>(
        &mut self,
        id: NodeId,
        val: usize,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
        leafs: &mut [(Lit, usize)],
    ) -> anyhow::Result<Option<Lit>>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        use pidgeons::OperationLike;

        debug_assert!(val <= self[id].max_val());
        debug_assert!(val > 0);
        debug_assert_eq!(leafs.len(), self[id].n_leafs());
        match &self[id] {
            Node::Leaf(lit) => {
                debug_assert_eq!(val, 1);
                leafs[0] = (*lit, 1);
                if val != 1 {
                    return Ok(None);
                }
                Ok(Some(*lit))
            }
            Node::Unit(node) => {
                if val > node.lits.len() || val == 0 {
                    return Ok(None);
                }

                let mut unweighted_leafs: Vec<_> = leafs.iter().map(|(l, _)| *l).collect();
                let olit = self.define_unweighted_cert(
                    id,
                    val - 1,
                    Semantics::If,
                    collector,
                    var_manager,
                    proof,
                    &mut unweighted_leafs,
                )?;
                for (idx, &lit) in unweighted_leafs.iter().enumerate() {
                    leafs[idx] = (lit, 1);
                }
                Ok(Some(olit))
            }
            Node::General(node) => {
                // Check if already encoded
                if let Some(lit_data) = node.lits.get(&val) {
                    if let LitData::Lit {
                        lit,
                        semantics: Some(semantics),
                    } = lit_data
                    {
                        if semantics.has_if() {
                            let mut new_leafs: Vec<_> = self.leaf_iter(id).collect();
                            leafs.swap_with_slice(&mut new_leafs);
                            return Ok(Some(*lit));
                        }
                    }
                } else {
                    return Ok(None);
                }

                debug_assert!(node.lits.contains_key(&val));

                let lcon = node.left;
                let rcon = node.right;

                // Reserve variable for this node, if needed
                let olit = if let Some(&olit) = node.lit(val) {
                    olit
                } else {
                    let olit = var_manager.new_var().pos_lit();
                    *unreachable_none!(self[id].mut_general().lits.get_mut(&val)) =
                        LitData::new_lit(olit);
                    olit
                };

                let (left_leafs, right_leafs) = leafs.split_at_mut(self[lcon.id].n_leafs());

                // Propagate value
                if lcon.is_possible(val) && lcon.rev_map(val) <= self[lcon.id].max_val() {
                    if let Some(llit) = self.define_weighted_cert(
                        lcon.id,
                        lcon.rev_map(val),
                        collector,
                        var_manager,
                        proof,
                        left_leafs,
                    )? {
                        let left_def = self.define_semantics(
                            lcon.id,
                            lcon.rev_map(val),
                            SemDefTyp::OnlyIf,
                            left_leafs.iter().copied(),
                            proof,
                        )?;
                        let right_def = self.define_semantics(
                            rcon.id,
                            0,
                            SemDefTyp::OnlyIf,
                            right_leafs.iter().copied(),
                            proof,
                        )?;
                        let this_def = self.define_semantics(
                            id,
                            val,
                            SemDefTyp::If,
                            left_leafs
                                .iter()
                                .map(|(l, w)| (*l, *w * lcon.multiplier()))
                                .chain(
                                    right_leafs
                                        .iter()
                                        .map(|(l, w)| (*l, *w * rcon.multiplier())),
                                ),
                            proof,
                        )?;
                        let id = proof.operations(
                            &(this_def
                                + (left_def * lcon.multiplier())
                                + (right_def * rcon.multiplier()))
                            .saturate(),
                        )?;
                        collector.add_cert_clause(atomics::lit_impl_lit(llit, olit), id)?;
                    }
                }
                if rcon.is_possible(val) && rcon.rev_map(val) <= self[rcon.id].max_val() {
                    if let Some(rlit) = self.define_weighted_cert(
                        rcon.id,
                        rcon.rev_map(val),
                        collector,
                        var_manager,
                        proof,
                        right_leafs,
                    )? {
                        let left_def = self.define_semantics(
                            lcon.id,
                            0,
                            SemDefTyp::OnlyIf,
                            left_leafs.iter().copied(),
                            proof,
                        )?;
                        let right_def = self.define_semantics(
                            rcon.id,
                            rcon.rev_map(val),
                            SemDefTyp::OnlyIf,
                            right_leafs.iter().copied(),
                            proof,
                        )?;
                        let this_def = self.define_semantics(
                            id,
                            val,
                            SemDefTyp::If,
                            left_leafs
                                .iter()
                                .map(|(l, w)| (*l, *w * lcon.multiplier()))
                                .chain(
                                    right_leafs
                                        .iter()
                                        .map(|(l, w)| (*l, *w * rcon.multiplier())),
                                ),
                            proof,
                        )?;
                        let id = proof.operations(
                            &(this_def
                                + (left_def * lcon.multiplier())
                                + (right_def * rcon.multiplier()))
                            .saturate(),
                        )?;
                        collector.add_cert_clause(atomics::lit_impl_lit(rlit, olit), id)?;
                    };
                }

                // Propagate sums
                if lcon.map(lcon.offset() + 1) < val {
                    let lvals = self[lcon.id].vals(lcon.offset() + 1..lcon.rev_map_round_up(val));
                    let rmax = self[rcon.id].max_val();
                    for lval in lvals {
                        let rval = val - lcon.map(lval);
                        debug_assert!(rval > 0);
                        let rval_rev = rcon.rev_map(rval);
                        if rcon.is_possible(rval) && rval_rev <= rmax {
                            if let Some(rlit) = self.define_weighted_cert(
                                rcon.id,
                                rval_rev,
                                collector,
                                var_manager,
                                proof,
                                right_leafs,
                            )? {
                                debug_assert!(
                                    lcon.len_limit.is_none() || lcon.offset() + 1 == lval
                                );
                                let llit = unreachable_none!(self.define_weighted_cert(
                                    lcon.id,
                                    lval,
                                    collector,
                                    var_manager,
                                    proof,
                                    left_leafs
                                )?);
                                let left_def = self.define_semantics(
                                    lcon.id,
                                    lval,
                                    SemDefTyp::OnlyIf,
                                    left_leafs.iter().copied(),
                                    proof,
                                )?;
                                let right_def = self.define_semantics(
                                    rcon.id,
                                    rval_rev,
                                    SemDefTyp::OnlyIf,
                                    right_leafs.iter().copied(),
                                    proof,
                                )?;
                                let this_def = self.define_semantics(
                                    id,
                                    val,
                                    SemDefTyp::If,
                                    left_leafs
                                        .iter()
                                        .map(|(l, w)| (*l, *w * lcon.multiplier()))
                                        .chain(
                                            right_leafs
                                                .iter()
                                                .map(|(l, w)| (*l, *w * rcon.multiplier())),
                                        ),
                                    proof,
                                )?;
                                let id = proof.operations(
                                    &(this_def
                                        + (left_def * lcon.multiplier())
                                        + (right_def * rcon.multiplier()))
                                    .saturate(),
                                )?;
                                collector.add_cert_clause(
                                    atomics::cube_impl_lit(&[llit, rlit], olit),
                                    id,
                                )?;
                            }
                        }
                    }
                }

                // Only now finally multiply the leaf weights since they won't be used at lower
                // levels any more
                for (idx, (_, w)) in leafs.iter_mut().enumerate() {
                    if idx < self[lcon.id].n_leafs() {
                        *w *= lcon.multiplier();
                    } else {
                        *w *= rcon.multiplier();
                    }
                }

                // Mark "if" semantics as encoded
                unreachable_none!(self[id].mut_general().lits.get_mut(&val))
                    .add_semantics(Semantics::If);

                Ok(Some(olit))
            }
            Node::Dummy => Ok(None),
        }
    }

    /// Recursion for unweighted totalizer encoding with certificate
    fn recurse_unweighted_cert<Col, W>(
        &mut self,
        pre: &UnweightedPrecondResult,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
        leafs: &mut [Lit],
    ) -> anyhow::Result<()>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        let (left_leafs, right_leafs) = leafs.split_at_mut(self[pre.lcon.id].n_leafs());
        for lval in pre.left_if.clone() {
            if lval == 0 {
                continue;
            }
            self.define_unweighted_cert(
                pre.lcon.id,
                con_idx(lval - 1, pre.lcon),
                Semantics::If,
                collector,
                var_manager,
                proof,
                left_leafs,
            )?;
        }
        for rval in pre.right_if.clone() {
            if rval == 0 {
                continue;
            }
            self.define_unweighted_cert(
                pre.rcon.id,
                con_idx(rval - 1, pre.rcon),
                Semantics::If,
                collector,
                var_manager,
                proof,
                right_leafs,
            )?;
        }
        for lval in pre.left_only_if.clone() {
            if lval == self.con_len(pre.lcon) {
                continue;
            }
            self.define_unweighted_cert(
                pre.lcon.id,
                con_idx(lval, pre.lcon),
                Semantics::OnlyIf,
                collector,
                var_manager,
                proof,
                left_leafs,
            )?;
        }
        for rval in pre.right_only_if.clone() {
            if rval == self.con_len(pre.rcon) {
                continue;
            }
            self.define_unweighted_cert(
                pre.rcon.id,
                con_idx(rval, pre.rcon),
                Semantics::OnlyIf,
                collector,
                var_manager,
                proof,
                right_leafs,
            )?;
        }
        Ok(())
    }

    /// Last step of [`Self::define_unweighted_cert`]
    ///
    /// # Panics
    ///
    /// If the semantics are already encoded.
    #[allow(clippy::too_many_arguments)]
    fn encode_unweighted_cert<W, Col>(
        &mut self,
        id: NodeId,
        idx: usize,
        olit: Lit,
        req_semantics: Semantics,
        pre: &UnweightedPrecondResult,
        collector: &mut Col,
        proof: &mut pidgeons::Proof<W>,
        leafs: &mut [Lit],
    ) -> anyhow::Result<()>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        use pidgeons::OperationLike;

        // Store what part of the encoding we need to build
        let new_semantics = self[id].unit().lits[idx]
            .missing_semantics(req_semantics)
            .expect("semantics are already encoded");

        // Mark positive literal as encoded (done first to avoid borrow checker problems)
        self[id].mut_unit().lits[idx].add_semantics(req_semantics);

        let (left_leafs, right_leafs) = leafs.split_at(self[pre.lcon.id].n_leafs());

        // Encode
        // If semantics
        for lval in pre.left_if.clone() {
            let rval = idx + 1 - lval;
            debug_assert!(pre.right_if.contains(&rval));
            debug_assert!(new_semantics.has_if());
            let mut lhs = [lit![0], lit![0]]; // avoids allocation
            let mut nlits = 0;
            if lval > 0 {
                lhs[nlits] = get_olit!(self, pre.lcon.id, con_idx(lval - 1, pre.lcon));
                nlits += 1;
            }
            if rval > 0 {
                lhs[nlits] = get_olit!(self, pre.rcon.id, con_idx(rval - 1, pre.rcon));
                nlits += 1;
            }
            let left_def = self.define_semantics(
                pre.lcon.id,
                pre.lcon.rev_map(lval),
                SemDefTyp::OnlyIf,
                left_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let right_def = self.define_semantics(
                pre.rcon.id,
                pre.rcon.rev_map(rval),
                SemDefTyp::OnlyIf,
                right_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let this_def = self.define_semantics(
                id,
                idx + 1,
                SemDefTyp::If,
                leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let id = proof.operations(&(this_def + left_def + right_def).saturate())?;
            collector.add_cert_clause(atomics::cube_impl_lit(&lhs[..nlits], olit), id)?;
        }
        // Only if semantics
        for lval in pre.left_only_if.clone() {
            let rval = idx - lval;
            debug_assert!(pre.right_only_if.contains(&rval));
            debug_assert!(new_semantics.has_only_if());
            let mut lhs = [lit![0], lit![0]]; // avoids allocation
            let mut nlits = 0;
            if lval < self.con_len(pre.lcon) {
                lhs[nlits] = !get_olit!(self, pre.lcon.id, con_idx(lval, pre.lcon));
                nlits += 1;
            }
            if rval < self.con_len(pre.rcon) {
                lhs[nlits] = !get_olit!(self, pre.rcon.id, con_idx(rval, pre.rcon));
                nlits += 1;
            }
            let left_def = self.define_semantics(
                pre.lcon.id,
                pre.lcon.rev_map(lval + 1),
                SemDefTyp::If,
                left_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let right_def = self.define_semantics(
                pre.rcon.id,
                pre.rcon.rev_map(rval + 1),
                SemDefTyp::If,
                right_leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let this_def = self.define_semantics(
                id,
                idx + 1,
                SemDefTyp::OnlyIf,
                leafs.iter().map(|l| (*l, 1)),
                proof,
            )?;
            let id = proof.operations(&(this_def + left_def + right_def).saturate())?;
            collector.add_cert_clause(atomics::cube_impl_lit(&lhs[..nlits], !olit), id)?;
        }

        Ok(())
    }

    /// Defines a positive output, assuming that the structure is a non-weighted totalizer, and
    /// certifies its derivation in the provided proof
    ///
    /// The `idx` parameter is the output index, i.e., not the value represented by the output, but
    /// `value - 1`.
    ///
    /// Leafs must be a reference to a slice with length of the size of the given node (`id`). It
    /// is used to more efficiently keep track of the leafs affecting the given node, which is
    /// required for proof logging.
    ///
    /// # Errors
    ///
    /// - If the clause collector runs out of memory, returns [`crate::OutOfMemory`]
    /// - If writing the proof fails, returns [`std::io::Error`]
    #[allow(clippy::too_many_arguments)]
    pub fn define_unweighted_cert<Col, W>(
        &mut self,
        id: NodeId,
        idx: usize,
        semantics: Semantics,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
        proof: &mut pidgeons::Proof<W>,
        leafs: &mut [Lit],
    ) -> anyhow::Result<Lit>
    where
        Col: crate::encodings::CollectCertClauses,
        W: std::io::Write,
    {
        debug_assert_eq!(leafs.len(), self[id].len());

        let pre = match self.precond_unweighted(id, idx, semantics) {
            PrecondOutcome::Return(lit) => {
                let mut new_leafs: Vec<_> = self.leaf_iter(id).map(|(l, _)| l).collect();
                leafs.swap_with_slice(&mut new_leafs);
                return Ok(lit);
            }
            PrecondOutcome::Passthrough(_) => {
                // TODO: Decide what to do here
                // It probably doesn't make much sense to support this case with proof logging,
                // since the semantics of the output literals change when the dummy is replaced.
                // If the dummy is never replaced, then it should be avoided in the first place.
                todo!()
            }
            PrecondOutcome::Continue(pre) => pre,
        };

        // Encode children (recurse)
        self.recurse_unweighted_cert(&pre, collector, var_manager, proof, leafs)?;

        // Reserve variable for this node, if needed
        let olit = self.get_olit(id, idx, var_manager);

        // Encode this node
        self.encode_unweighted_cert(id, idx, olit, semantics, &pre, collector, proof, leafs)?;

        Ok(olit)
    }
}

/// The semantic definitions related to a totalizer output
#[derive(Hash, Clone, Copy, PartialEq, Eq, Debug)]
pub struct SemDefs {
    /// The if implication direction, i.e., `sum >= k -> olit`
    pub if_def: Option<AbsConstraintId>,
    /// The only if implication direction, i.e., `olit -> sum >= k`
    pub only_if_def: Option<AbsConstraintId>,
}

impl SemDefs {
    fn new(if_def: Option<AbsConstraintId>, only_if_def: Option<AbsConstraintId>) -> Self {
        Self {
            if_def,
            only_if_def,
        }
    }

    fn get(&self, typ: SemDefTyp) -> AbsConstraintId {
        match typ {
            SemDefTyp::If => self.if_def.unwrap(),
            SemDefTyp::OnlyIf => self.only_if_def.unwrap(),
        }
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq, Debug)]
enum SemDefinition {
    None,
    Id(AbsConstraintId),
    Axiom(Lit),
}

impl From<AbsConstraintId> for SemDefinition {
    fn from(value: AbsConstraintId) -> Self {
        Self::Id(value)
    }
}

impl From<Lit> for SemDefinition {
    fn from(value: Lit) -> Self {
        Self::Axiom(value)
    }
}

impl ops::Add<SemDefinition> for SemDefinition {
    type Output = pidgeons::OperationSequence<Var>;

    fn add(self, rhs: SemDefinition) -> Self::Output {
        match self {
            SemDefinition::None => match rhs {
                SemDefinition::None => pidgeons::OperationSequence::empty(),
                SemDefinition::Id(rhs) => rhs.into(),
                SemDefinition::Axiom(rhs) => pidgeons::Axiom::from(rhs).into(),
            },
            SemDefinition::Id(lhs) => match rhs {
                SemDefinition::None => lhs.into(),
                SemDefinition::Id(rhs) => Self::Output::from(lhs) + rhs,
                SemDefinition::Axiom(rhs) => lhs + pidgeons::Axiom::from(rhs),
            },
            SemDefinition::Axiom(lhs) => match rhs {
                SemDefinition::None => pidgeons::Axiom::from(lhs).into(),
                SemDefinition::Id(rhs) => pidgeons::Axiom::from(lhs) + rhs,
                SemDefinition::Axiom(rhs) => {
                    pidgeons::Axiom::from(lhs) + pidgeons::Axiom::from(rhs)
                }
            },
        }
    }
}

impl ops::Add<SemDefinition> for pidgeons::OperationSequence<Var> {
    type Output = pidgeons::OperationSequence<Var>;

    fn add(self, rhs: SemDefinition) -> Self::Output {
        match rhs {
            SemDefinition::None => self,
            SemDefinition::Id(rhs) => self + rhs,
            SemDefinition::Axiom(rhs) => self + pidgeons::Axiom::from(rhs),
        }
    }
}

impl ops::Add<pidgeons::OperationSequence<Var>> for SemDefinition {
    type Output = pidgeons::OperationSequence<Var>;

    fn add(self, rhs: pidgeons::OperationSequence<Var>) -> Self::Output {
        match self {
            SemDefinition::None => rhs,
            SemDefinition::Id(id) => id + rhs,
            SemDefinition::Axiom(ax) => pidgeons::Axiom::from(ax) + rhs,
        }
    }
}

impl ops::Mul<usize> for SemDefinition {
    type Output = pidgeons::OperationSequence<Var>;

    fn mul(self, rhs: usize) -> Self::Output {
        match self {
            SemDefinition::None => pidgeons::OperationSequence::empty(),
            SemDefinition::Id(id) => Self::Output::from(id) * rhs,
            SemDefinition::Axiom(ax) => pidgeons::Axiom::from(ax) * rhs,
        }
    }
}

#[derive(Hash, Clone, Copy, PartialEq, Eq)]
pub(super) enum SemDefTyp {
    If,
    OnlyIf,
}

#[cfg(test)]
mod tests {
    use std::{
        fs::File,
        io::{BufRead, BufReader},
        path::Path,
        process::Command,
    };

    use crate::{
        encodings::{
            nodedb::{NodeById, NodeLike},
            totdb::{Db, Semantics},
        },
        instances::{BasicVarManager, Cnf, ManageVars},
        lit, var,
    };

    fn print_file<P: AsRef<Path>>(path: P) {
        println!();
        for line in BufReader::new(File::open(path).expect("could not open file")).lines() {
            println!("{}", line.unwrap());
        }
        println!();
    }

    fn verify_proof<P1: AsRef<Path>, P2: AsRef<Path>>(instance: P1, proof: P2) {
        println!("start checking proof");
        let out = Command::new("veripb")
            .arg(instance.as_ref())
            .arg(proof.as_ref())
            .output()
            .expect("failed to run veripb");
        print_file(proof);
        if out.status.success() {
            return;
        }
        panic!("verification failed: {out:?}")
    }

    fn new_proof(
        num_constraints: usize,
        optimization: bool,
    ) -> pidgeons::Proof<tempfile::NamedTempFile> {
        let file = tempfile::NamedTempFile::new().expect("failed to create temporary proof file");
        pidgeons::Proof::new(file, num_constraints, optimization).expect("failed to start proof")
    }

    #[test]
    fn tot_db_if() {
        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut lits = [lit![0]; 4];
        db.define_unweighted_cert(
            root,
            0,
            Semantics::If,
            &mut cnf,
            &mut var_manager,
            &mut proof,
            &mut lits,
        )
        .unwrap();
        db.define_unweighted_cert(
            root,
            1,
            Semantics::If,
            &mut cnf,
            &mut var_manager,
            &mut proof,
            &mut lits,
        )
        .unwrap();
        db.define_unweighted_cert(
            root,
            2,
            Semantics::If,
            &mut cnf,
            &mut var_manager,
            &mut proof,
            &mut lits,
        )
        .unwrap();
        db.define_unweighted_cert(
            root,
            3,
            Semantics::If,
            &mut cnf,
            &mut var_manager,
            &mut proof,
            &mut lits,
        )
        .unwrap();

        let proof_file = proof
            .conclude(pidgeons::OutputGuarantee::None, &pidgeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn tot_db_only_if() {
        let mut db = Db::default();
        let root = db.lit_tree(&[lit![0], lit![1], lit![2], lit![3]]);
        debug_assert_eq!(db[root].depth(), 3);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut lits = [lit![0]; 4];
        db.define_unweighted_cert(
            root,
            0,
            Semantics::OnlyIf,
            &mut cnf,
            &mut var_manager,
            &mut proof,
            &mut lits,
        )
        .unwrap();
        db.define_unweighted_cert(
            root,
            1,
            Semantics::OnlyIf,
            &mut cnf,
            &mut var_manager,
            &mut proof,
            &mut lits,
        )
        .unwrap();
        db.define_unweighted_cert(
            root,
            2,
            Semantics::OnlyIf,
            &mut cnf,
            &mut var_manager,
            &mut proof,
            &mut lits,
        )
        .unwrap();
        db.define_unweighted_cert(
            root,
            3,
            Semantics::OnlyIf,
            &mut cnf,
            &mut var_manager,
            &mut proof,
            &mut lits,
        )
        .unwrap();

        let proof_file = proof
            .conclude(pidgeons::OutputGuarantee::None, &pidgeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }

    #[test]
    fn gte_db() {
        let mut db = Db::default();
        let root = db.weighted_lit_tree(&[(lit![0], 4), (lit![1], 3), (lit![2], 2), (lit![3], 1)]);
        assert_eq!(root.offset(), 0);
        assert_eq!(root.multiplier(), 1);
        let root = root.id;
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);

        let mut proof = new_proof(0, false);

        let mut cnf = Cnf::new();
        let mut lits = [(lit![0], 0); 4];
        db.define_weighted_cert(root, 1, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();
        db.define_weighted_cert(root, 2, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();
        db.define_weighted_cert(root, 3, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();
        db.define_weighted_cert(root, 4, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();
        db.define_weighted_cert(root, 5, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();
        db.define_weighted_cert(root, 6, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();
        db.define_weighted_cert(root, 7, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();
        db.define_weighted_cert(root, 8, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();
        db.define_weighted_cert(root, 9, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();
        db.define_weighted_cert(root, 10, &mut cnf, &mut var_manager, &mut proof, &mut lits)
            .unwrap();

        let proof_file = proof
            .conclude(pidgeons::OutputGuarantee::None, &pidgeons::Conclusion::None)
            .unwrap();
        let manifest = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        verify_proof(format!("{manifest}/data/empty.opb"), proof_file.path());
    }
}
