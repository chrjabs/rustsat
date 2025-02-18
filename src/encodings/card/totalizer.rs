//! # Totalizer Encoding
//!
//! Implementation of the binary adder tree totalizer encoding \[1\].
//! The implementation is incremental as extended in \[2\].
//! The implementation is recursive.
//!
//! For an alternative implementation based on a node database, see
//! [`crate::encodings::card::DbTotalizer`].
//!
//! ## References
//!
//! - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
//! - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.

use super::{
    BoundLower, BoundLowerIncremental, BoundUpper, BoundUpperIncremental, Encode,
    EncodeIncremental, Error,
};
use crate::{
    encodings::{atomics, CollectClauses, EncodeStats, IterInputs},
    instances::ManageVars,
    types::Lit,
};
use std::{
    cmp,
    ops::{Range, RangeBounds},
    slice,
};

/// Implementation of the binary adder tree totalizer encoding \[1\].
/// The implementation is incremental as extended in \[2\].
/// The implementation is recursive.
///
/// # References
///
/// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
/// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
#[derive(Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Totalizer {
    /// Input literals to the totalizer
    in_lits: Vec<Lit>,
    /// Index of the next literal in [`Totalizer::in_lits`] that is not in the tree yet
    not_enc_idx: usize,
    /// The root of the tree, if constructed
    root: Option<Node>,
    /// The number of variables in the totalizer
    n_vars: u32,
    /// The number of clauses in the totalizer
    n_clauses: usize,
}

impl Totalizer {
    /// Recursively builds the tree data structure. Attention, low level
    /// interface, might change!
    #[cfg_attr(feature = "internals", visibility::make(pub))]
    #[cfg_attr(docsrs, doc(cfg(feature = "internals")))]
    #[must_use]
    fn build_tree(lits: &[Lit]) -> Node {
        debug_assert_ne!(lits.len(), 0);

        if lits.len() == 1 {
            return Node::new_leaf(lits[0]);
        };

        let split = lits.len() / 2;
        let left = Totalizer::build_tree(&lits[..split]);
        let right = Totalizer::build_tree(&lits[split..]);

        Node::new_internal(left, right)
    }

    /// Extends the tree at the root node with added literals
    fn extend_tree(&mut self) {
        if self.not_enc_idx != self.in_lits.len() {
            let subtree = Totalizer::build_tree(&self.in_lits[self.not_enc_idx..]);
            self.root = match self.root.take() {
                None => Some(subtree),
                Some(old_root) => {
                    let new_root = Node::new_internal(old_root, subtree);
                    Some(new_root)
                }
            };
            self.not_enc_idx = self.in_lits.len();
        }
    }

    /// Gets the maximum depth of the tree
    #[must_use]
    pub fn depth(&self) -> usize {
        match &self.root {
            None => 0,
            Some(root_node) => root_node.depth(),
        }
    }

    /// Fully builds the tree, then returns it
    #[cfg(feature = "internals")]
    #[cfg_attr(docsrs, doc(cfg(feature = "internals")))]
    #[must_use]
    pub fn tree(mut self) -> Option<Node> {
        self.extend_tree();
        self.root
    }
}

impl Encode for Totalizer {
    fn n_lits(&self) -> usize {
        self.in_lits.len()
    }
}

impl IterInputs for Totalizer {
    type Iter<'a> = TotIter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }
}

impl EncodeIncremental for Totalizer {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.extend_tree();
        if let Some(root) = &mut self.root {
            root.reserve_all_vars_rec(var_manager);
        }
    }
}

impl BoundUpper for Totalizer {
    fn encode_ub<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        let range = super::prepare_ub_range(self, range);
        if range.is_empty() {
            return Ok(());
        };
        self.extend_tree();
        match &mut self.root {
            None => (),
            Some(root) => {
                let n_vars_before = var_manager.n_used();
                let n_clauses_before = collector.n_clauses();
                root.rec_encode_ub(range, collector, var_manager)?;
                self.n_clauses += collector.n_clauses() - n_clauses_before;
                self.n_vars += var_manager.n_used() - n_vars_before;
            }
        };
        Ok(())
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        if ub >= self.in_lits.len() {
            return Ok(vec![]);
        };
        if self.not_enc_idx != self.in_lits.len() {
            return Err(Error::NotEncoded);
        };
        match &self.root {
            None => Err(Error::NotEncoded),
            Some(root_node) => match root_node {
                Node::Leaf { lit } => Ok(vec![!*lit]),
                Node::Internal {
                    out_lits, ub_range, ..
                } => {
                    if ub_range.contains(&ub) {
                        Ok(vec![!out_lits[ub].unwrap()])
                    } else {
                        Err(Error::NotEncoded)
                    }
                }
            },
        }
    }
}

impl BoundLower for Totalizer {
    fn encode_lb<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        let range = super::prepare_lb_range(self, range);
        if range.is_empty() {
            return Ok(());
        };
        self.extend_tree();
        match &mut self.root {
            None => (),
            Some(root) => {
                let n_vars_before = var_manager.n_used();
                let n_clauses_before = collector.n_clauses();
                root.rec_encode_lb(range, collector, var_manager)?;
                self.n_clauses += collector.n_clauses() - n_clauses_before;
                self.n_vars += var_manager.n_used() - n_vars_before;
            }
        };
        Ok(())
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, Error> {
        if self.not_enc_idx != self.in_lits.len() {
            return Err(Error::NotEncoded);
        };
        if lb > self.in_lits.len() {
            return Err(Error::Unsat);
        } else if lb == 0 {
            return Ok(vec![]);
        };
        match &self.root {
            None => Err(Error::NotEncoded),
            Some(root_node) => match root_node {
                Node::Leaf { lit } => Ok(vec![*lit]),
                Node::Internal {
                    out_lits, lb_range, ..
                } => {
                    if lb_range.contains(&lb) {
                        Ok(vec![out_lits[lb - 1].unwrap()])
                    } else {
                        Err(Error::NotEncoded)
                    }
                }
            },
        }
    }
}

impl BoundUpperIncremental for Totalizer {
    fn encode_ub_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        let range = super::prepare_ub_range(self, range);
        if range.is_empty() {
            return Ok(());
        };
        self.extend_tree();
        match &mut self.root {
            None => (),
            Some(root) => {
                let n_vars_before = var_manager.n_used();
                let n_clauses_before = collector.n_clauses();
                root.rec_encode_ub_change(range, collector, var_manager)?;
                self.n_clauses += collector.n_clauses() - n_clauses_before;
                self.n_vars += var_manager.n_used() - n_vars_before;
            }
        };
        Ok(())
    }
}

impl BoundLowerIncremental for Totalizer {
    fn encode_lb_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
        R: RangeBounds<usize>,
    {
        let range = super::prepare_lb_range(self, range);
        if range.is_empty() {
            return Ok(());
        };
        self.extend_tree();
        match &mut self.root {
            None => (),
            Some(root) => {
                let n_vars_before = var_manager.n_used();
                let n_clauses_before = collector.n_clauses();
                root.rec_encode_lb_change(range, collector, var_manager)?;
                self.n_clauses += collector.n_clauses() - n_clauses_before;
                self.n_vars += var_manager.n_used() - n_vars_before;
            }
        };
        Ok(())
    }
}

impl EncodeStats for Totalizer {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<Vec<Lit>> for Totalizer {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            not_enc_idx: Default::default(),
            root: None,
            n_vars: 0,
            n_clauses: 0,
        }
    }
}

impl FromIterator<Lit> for Totalizer {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            in_lits: Vec::from_iter(iter),
            not_enc_idx: Default::default(),
            root: None,
            n_vars: 0,
            n_clauses: 0,
        }
    }
}

impl Extend<Lit> for Totalizer {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.in_lits.extend(iter);
    }
}

pub(super) type TotIter<'a> = std::iter::Copied<std::slice::Iter<'a, Lit>>;

/// A node in the totalizer tree. This is only exposed publicly to be reused in
/// more complex encodings, for using the totalizer, this should not be directly
/// accessed but only through [`Totalizer`].
#[cfg_attr(feature = "internals", visibility::make(pub))]
#[cfg_attr(docsrs, doc(cfg(feature = "internals")))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
enum Node {
    /// An input literal, i.e., a leaf node of the tree
    Leaf {
        /// The input literal to the tree
        lit: Lit,
    },
    /// An internal node of the tree
    Internal {
        /// The output literals of this node
        out_lits: Vec<Option<Lit>>,
        /// The path length to the leaf furthest away in the sub-tree
        depth: usize,
        /// The number of clauses this node produced
        n_clauses: usize,
        /// The maximum output this node can have
        max_val: usize,
        /// The range encoded for upper bounding
        ub_range: Range<usize>,
        /// The range encoded for lower bounding
        lb_range: Range<usize>,
        /// The left child
        left: Box<Node>,
        /// The right child
        right: Box<Node>,
    },
}

impl Node {
    /// Constructs a new leaf node
    #[must_use]
    pub fn new_leaf(lit: Lit) -> Node {
        Node::Leaf { lit }
    }

    /// Constructs a new internal node
    #[must_use]
    pub fn new_internal(left: Node, right: Node) -> Node {
        Node::Internal {
            out_lits: vec![],
            depth: cmp::max(left.depth() + 1, right.depth() + 1),
            n_clauses: 0,
            ub_range: 0..0,
            lb_range: 0..0,
            max_val: left.max_val() + right.max_val(),
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Gets the maximum depth of the sub-tree rooted in this node
    #[must_use]
    pub fn depth(&self) -> usize {
        match self {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => *depth,
        }
    }

    /// Gets the maximum value that the node represents
    #[must_use]
    pub fn max_val(&self) -> usize {
        match self {
            Node::Leaf { .. } => 1,
            Node::Internal { max_val, .. } => *max_val,
        }
    }

    /// Encodes the upper bound adder for this node in a given range. This
    /// method only produces the encoding and does _not_ change any of the stats
    /// of the node.
    fn encode_ub_range<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Ok(());
        }

        // Reserve vars if needed
        self.reserve_vars_range(range.clone(), var_manager);
        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                out_lits,
                left,
                right,
                ..
            } => {
                // Encode adder for current node
                let tmp_opt_lit_l;
                let tmp_opt_lit_r;
                let left_lits = match &**left {
                    Node::Leaf { lit } => {
                        tmp_opt_lit_l = Some(*lit);
                        slice::from_ref(&tmp_opt_lit_l)
                    }
                    Node::Internal { out_lits, .. } => &out_lits[..],
                };
                let right_lits = match &**right {
                    Node::Leaf { lit } => {
                        tmp_opt_lit_r = Some(*lit);
                        slice::from_ref(&tmp_opt_lit_r)
                    }
                    Node::Internal { out_lits, .. } => &out_lits[..],
                };
                // Iterate through all value combinations
                let clause_for_vals = |left_val: usize, right_val: usize| {
                    let sum_val = left_val + right_val;
                    if sum_val > range.end || sum_val <= range.start {
                        return None;
                    }
                    let mut lhs: Vec<Lit> = vec![];
                    if left_val != 0 {
                        lhs.push(left_lits[left_val - 1].unwrap());
                    }
                    if right_val != 0 {
                        lhs.push(right_lits[right_val - 1].unwrap());
                    }
                    if !lhs.is_empty() {
                        // (left > x) & (right > y) -> (out > x+y)
                        return Some(atomics::cube_impl_lit(&lhs, out_lits[sum_val - 1].unwrap()));
                    }
                    None
                };
                let clause_iter = (0..=left_lits.len()).flat_map(|left_val| {
                    (0..=right_lits.len())
                        .filter_map(move |right_val| clause_for_vals(left_val, right_val))
                });
                collector.extend_clauses(clause_iter)?;
            }
        };

        Ok(())
    }

    /// Encodes the lower bound adder for this node in a given range. This
    /// method only produces the encoding and does _not_ change any of the stats
    /// of the node.
    fn encode_lb_range<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Ok(());
        }

        // Reserve vars if needed
        self.reserve_vars_range(
            if range.start > 0 { range.start - 1 } else { 0 }..if range.end > 0 {
                range.end - 1
            } else {
                0
            },
            var_manager,
        );
        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                out_lits,
                left,
                right,
                ..
            } => {
                // Encode adder for current node
                let tmp_opt_lit_l;
                let tmp_opt_lit_r;
                let left_lits = match &**left {
                    Node::Leaf { lit } => {
                        tmp_opt_lit_l = Some(*lit);
                        slice::from_ref(&tmp_opt_lit_l)
                    }
                    Node::Internal { out_lits, .. } => &out_lits[..],
                };
                let right_lits = match &**right {
                    Node::Leaf { lit } => {
                        tmp_opt_lit_r = Some(*lit);
                        slice::from_ref(&tmp_opt_lit_r)
                    }
                    Node::Internal { out_lits, .. } => &out_lits[..],
                };
                // Iterate through all value combinations
                let clause_for_vals = |left_val: usize, right_val: usize| {
                    let sum_val = left_val + right_val;
                    if sum_val + 1 >= range.end || sum_val + 1 < range.start {
                        return None;
                    }
                    let mut lhs = vec![];
                    if left_val < left_lits.len() {
                        lhs.push(!left_lits[left_val].unwrap());
                    }
                    if right_val < right_lits.len() {
                        lhs.push(!right_lits[right_val].unwrap());
                    }
                    if !lhs.is_empty() {
                        // (left <= x) & (right <= y) -> (out <= x+y)
                        return Some(atomics::cube_impl_lit(&lhs, !out_lits[sum_val].unwrap()));
                    }
                    None
                };
                let clause_iter = (0..=left_lits.len()).flat_map(|left_val| {
                    (0..=right_lits.len())
                        .filter_map(move |right_val| clause_for_vals(left_val, right_val))
                });
                collector.extend_clauses(clause_iter)?;
            }
        };

        Ok(())
    }

    /// Encodes the upper bound adder from the children to this node in a given
    /// range. Recurses depth first. Always returns the full requested CNF
    /// encoding, i.e., non-incremental.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn rec_encode_ub<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Ok(());
        }

        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                left,
                right,
                lb_range,
                ..
            } => {
                // Copy to avoid borrow checker
                let lb_range = lb_range.clone();

                let left_range = Node::compute_required_range(range.clone(), right.max_val());
                let right_range = Node::compute_required_range(range.clone(), left.max_val());
                // Recurse
                left.rec_encode_ub(left_range, collector, var_manager)?;
                right.rec_encode_ub(right_range, collector, var_manager)?;

                // Ignore all previous encoding and encode from scratch
                let n_clauses_before = collector.n_clauses();
                self.encode_ub_range(range.clone(), collector, var_manager)?;

                self.update_stats(range, lb_range, collector.n_clauses() - n_clauses_before);
            }
        }
        Ok(())
    }

    /// Encodes the lower bound adder from the children to this node in a given
    /// range. Recurses depth first. Always returns the full requested CNF
    /// encoding.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn rec_encode_lb<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Ok(());
        }

        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                left,
                right,
                ub_range,
                ..
            } => {
                // Copy to avoid borrow checker
                let ub_range = ub_range.clone();

                let left_range = Node::compute_required_range(range.clone(), right.max_val());
                let right_range = Node::compute_required_range(range.clone(), left.max_val());
                // Recurse
                left.rec_encode_lb(left_range, collector, var_manager)?;
                right.rec_encode_lb(right_range, collector, var_manager)?;

                // Ignore all previous encoding and encode from scratch
                let n_clauses_before = collector.n_clauses();
                self.encode_lb_range(range.clone(), collector, var_manager)?;

                self.update_stats(ub_range, range, collector.n_clauses() - n_clauses_before);
            }
        };

        Ok(())
    }

    /// Encodes the upper bound adder from the children to this node in a given
    /// range. Recurses depth first. Incrementally only encodes new clauses.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn rec_encode_ub_change<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        let range = self.limit_range(range);
        if range.is_empty() {
            return Ok(());
        }

        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                left,
                right,
                ub_range,
                lb_range,
                ..
            } => {
                // Copy to avoid borrow checker
                let lb_range = lb_range.clone();
                let ub_range = ub_range.clone();

                let left_range = Node::compute_required_range(range.clone(), right.max_val());
                let right_range = Node::compute_required_range(range.clone(), left.max_val());
                // Recurse
                left.rec_encode_ub_change(left_range, collector, var_manager)?;
                right.rec_encode_ub_change(right_range, collector, var_manager)?;

                // Encode changes for current node
                let n_clauses_before = collector.n_clauses();
                if ub_range.is_empty() {
                    // First time encoding this node
                    self.encode_ub_range(range.clone(), collector, var_manager)?;
                } else {
                    // Part already encoded
                    if range.start < ub_range.start {
                        self.encode_ub_range(range.start..ub_range.start, collector, var_manager)?;
                    };
                    if range.end > ub_range.end {
                        self.encode_ub_range(ub_range.end..range.end, collector, var_manager)?;
                    };
                };

                self.update_stats(range, lb_range, collector.n_clauses() - n_clauses_before);
            }
        };

        Ok(())
    }

    /// Encodes the lower bound adder from the children to this node in a given
    /// range. Recurses depth first. Incrementally only encodes new clauses.
    ///
    /// # Errors
    ///
    /// If the clause collector runs out of memory, returns [`crate::OutOfMemory`].
    pub fn rec_encode_lb_change<Col>(
        &mut self,
        range: Range<usize>,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), crate::OutOfMemory>
    where
        Col: CollectClauses,
    {
        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                left,
                right,
                ub_range,
                lb_range,
                ..
            } => {
                // Copy to avoid borrow checker
                let lb_range = lb_range.clone();
                let ub_range = ub_range.clone();

                let left_range = Node::compute_required_range(range.clone(), right.max_val());
                let right_range = Node::compute_required_range(range.clone(), left.max_val());
                // Recurse
                left.rec_encode_lb_change(left_range, collector, var_manager)?;
                right.rec_encode_lb_change(right_range, collector, var_manager)?;

                // Encode changes for current node
                let n_clauses_before = collector.n_clauses();
                if lb_range.is_empty() {
                    // First time encoding this node
                    self.encode_lb_range(range.clone(), collector, var_manager)?;
                } else {
                    // Part already encoded
                    if range.start < lb_range.start {
                        self.encode_lb_range(range.start..lb_range.start, collector, var_manager)?;
                    };
                    if range.end > lb_range.end {
                        self.encode_lb_range(lb_range.end..range.end, collector, var_manager)?;
                    };
                };

                self.update_stats(ub_range, range, collector.n_clauses() - n_clauses_before);
            }
        };

        Ok(())
    }

    /// Reserves variables this node might need for indices in a given range.
    fn reserve_vars_range(
        &mut self,
        mut idx_range: Range<usize>,
        var_manager: &mut dyn ManageVars,
    ) {
        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                out_lits, max_val, ..
            } => {
                idx_range.end = if idx_range.end > *max_val {
                    *max_val
                } else {
                    idx_range.end
                };
                if out_lits.len() < idx_range.end {
                    out_lits.resize(idx_range.end, None);
                };
                for olit in out_lits
                    .iter_mut()
                    .take(idx_range.end)
                    .skip(idx_range.start)
                {
                    if olit.is_none() {
                        *olit = Some(var_manager.new_var().pos_lit());
                    }
                }
                debug_assert!(out_lits.len() <= *max_val);
            }
        }
    }

    /// Reserves all variables this node might need. This is used if variables
    /// in the totalizer should have consecutive indices.
    fn reserve_all_vars(&mut self, var_manager: &mut dyn ManageVars) {
        let max_val = match self {
            Node::Leaf { .. } => return,
            Node::Internal { max_val, .. } => *max_val,
        };
        #[allow(clippy::range_plus_one)]
        self.reserve_vars_range(0..max_val + 1, var_manager);
    }

    /// Reserves all variables this node and the lower sub-tree might need. This
    /// is used if variables in the totalizer should have consecutive indices.
    pub fn reserve_all_vars_rec(&mut self, var_manager: &mut dyn ManageVars) {
        match self {
            Node::Leaf { .. } => return,
            Node::Internal { left, right, .. } => {
                // Recursion
                left.reserve_all_vars_rec(var_manager);
                right.reserve_all_vars_rec(var_manager);
            }
        };
        self.reserve_all_vars(var_manager);
    }

    /// Computes the required encoding range for a node given a requested range
    /// for the parent and the maximum value of the sibling.
    fn compute_required_range(requested_range: Range<usize>, max_sibling: usize) -> Range<usize> {
        if requested_range.is_empty() {
            0..0
        } else if requested_range.start > max_sibling {
            requested_range.start - max_sibling..requested_range.end
        } else {
            0..requested_range.end
        }
    }

    /// Limits a range by the maximum of the node
    fn limit_range(&self, range: Range<usize>) -> Range<usize> {
        match self {
            Node::Leaf { .. } => range.start..cmp::min(2, range.end),
            Node::Internal { max_val, .. } => range.start..cmp::min(*max_val + 1, range.end),
        }
    }

    /// Updates the statistics of the node by increasing the number of clauses
    /// and updating the encoded ranges
    fn update_stats(
        &mut self,
        new_upper_range: Range<usize>,
        new_lower_range: Range<usize>,
        new_n_clauses: usize,
    ) {
        match self {
            Node::Leaf { .. } => debug_assert_eq!(new_n_clauses, 0),
            Node::Internal {
                n_clauses,
                ub_range,
                lb_range,
                max_val,
                ..
            } => {
                *n_clauses += new_n_clauses;
                *ub_range = if (*ub_range).is_empty() {
                    new_upper_range.start..cmp::min(*max_val + 1, new_upper_range.end)
                } else {
                    cmp::min(new_upper_range.start, ub_range.start)
                        ..cmp::min(*max_val + 1, cmp::max(new_upper_range.end, ub_range.end))
                };
                *lb_range = if (*lb_range).is_empty() {
                    new_lower_range.start..cmp::min(*max_val + 1, new_lower_range.end)
                } else {
                    cmp::min(new_lower_range.start, lb_range.start)
                        ..cmp::min(*max_val + 1, cmp::max(new_lower_range.end, lb_range.end))
                };
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Node, Totalizer};
    use crate::{
        encodings::{
            card::{
                BoundBoth, BoundLower, BoundLowerIncremental, BoundUpper, BoundUpperIncremental,
                EncodeIncremental,
            },
            EncodeStats, Error,
        },
        instances::{BasicVarManager, Cnf, ManageVars},
        lit, var,
    };

    #[test]
    fn adder_1() {
        // Child nodes
        let child1 = Node::new_leaf(lit![0]);
        let child2 = Node::new_leaf(lit![1]);
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![2]);
        let mut cnf = Cnf::new();
        node.encode_ub_range(0..3, &mut cnf, &mut var_manager)
            .unwrap();
        node.encode_lb_range(0..3, &mut cnf, &mut var_manager)
            .unwrap();
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 2),
        };
        assert_eq!(cnf.len(), 6);
    }

    #[test]
    fn adder_2() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![Some(lit![1]), Some(lit![2])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            ub_range: 0..3,
            lb_range: 0..3,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![Some(lit![3]), Some(lit![4])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            ub_range: 0..3,
            lb_range: 0..3,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![5]);
        let mut cnf = Cnf::new();
        node.encode_ub_range(0..5, &mut cnf, &mut var_manager)
            .unwrap();
        node.encode_lb_range(0..5, &mut cnf, &mut var_manager)
            .unwrap();
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.len(), 16);
    }

    #[test]
    fn adder_3() {
        // Child nodes
        let child1 = Node::new_leaf(lit![0]);
        let child2 = Node::new_leaf(lit![1]);
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![2]);
        let mut cnf = Cnf::new();
        node.encode_lb_range(0..2, &mut cnf, &mut var_manager)
            .unwrap();
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 1),
        };
        assert_eq!(cnf.len(), 1);
    }

    #[test]
    fn partial_adder_1() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![Some(lit![1]), Some(lit![2]), Some(lit![3])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            ub_range: 0..3,
            lb_range: 0..3,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![Some(lit![4]), Some(lit![5]), Some(lit![6])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            ub_range: 0..3,
            lb_range: 0..3,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![7]);
        let mut cnf = Cnf::new();
        node.encode_ub_range(0..4, &mut cnf, &mut var_manager)
            .unwrap();
        node.encode_lb_range(0..4, &mut cnf, &mut var_manager)
            .unwrap();
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.len(), 18);
    }

    #[test]
    fn partial_adder_already_encoded() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![Some(lit![1]), Some(lit![2]), Some(lit![3])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            ub_range: 0..3,
            lb_range: 0..3,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![Some(lit![4]), Some(lit![5]), Some(lit![6])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            ub_range: 0..3,
            lb_range: 0..3,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![7]);
        let mut cnf = Cnf::new();
        node.encode_ub_range(3..3, &mut cnf, &mut var_manager)
            .unwrap();
        node.encode_lb_range(3..3, &mut cnf, &mut var_manager)
            .unwrap();
        assert_eq!(cnf.len(), 0);
    }

    #[test]
    fn partial_adder_2() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![Some(lit![1]), Some(lit![2]), Some(lit![3])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            ub_range: 0..3,
            lb_range: 0..3,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![Some(lit![4]), Some(lit![5]), Some(lit![6])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            ub_range: 0..3,
            lb_range: 0..3,
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![7]);
        let mut cnf = Cnf::new();
        node.encode_ub_range(2..4, &mut cnf, &mut var_manager)
            .unwrap();
        node.encode_lb_range(2..4, &mut cnf, &mut var_manager)
            .unwrap();
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.len(), 12);
    }

    #[test]
    fn tot_functions() {
        let mut tot = Totalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        assert_eq!(tot.enforce_ub(2), Err(Error::NotEncoded));
        assert_eq!(tot.enforce_lb(2), Err(Error::NotEncoded));
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf = Cnf::new();
        tot.encode_ub(0..5, &mut cnf, &mut var_manager).unwrap();
        tot.encode_lb(0..5, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(tot.depth(), 3);
        assert_eq!(cnf.len(), 28);
        assert_eq!(tot.n_clauses(), 28);
        assert_eq!(tot.n_vars(), 8);
        assert_eq!(tot.enforce_ub(2).unwrap().len(), 1);
        assert_eq!(tot.enforce_lb(2).unwrap().len(), 1);
    }

    #[test]
    fn tot_functions_min_rhs() {
        let mut tot = Totalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf = Cnf::new();
        tot.encode_both(3..4, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(tot.depth(), 3);
        assert_eq!(cnf.len(), 12);
        assert_eq!(cnf.len(), tot.n_clauses());
    }

    #[test]
    fn tot_incremental_building_ub() {
        let mut tot1 = Totalizer::default();
        tot1.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf1 = Cnf::new();
        tot1.encode_ub(0..5, &mut cnf1, &mut var_manager).unwrap();
        let mut tot2 = Totalizer::default();
        tot2.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf2 = Cnf::new();
        tot2.encode_ub(0..3, &mut cnf2, &mut var_manager).unwrap();
        tot2.encode_ub_change(0..5, &mut cnf2, &mut var_manager)
            .unwrap();
        assert_eq!(cnf1.len(), cnf2.len());
        assert_eq!(cnf1.len(), tot1.n_clauses());
        assert_eq!(cnf2.len(), tot2.n_clauses());
    }

    #[test]
    fn tot_incremental_building_lb() {
        let mut tot1 = Totalizer::default();
        tot1.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf1 = Cnf::new();
        tot1.encode_lb(0..5, &mut cnf1, &mut var_manager).unwrap();
        let mut tot2 = Totalizer::default();
        tot2.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::default();
        var_manager.increase_next_free(var![4]);
        let mut cnf2 = Cnf::new();
        tot2.encode_lb(0..3, &mut cnf2, &mut var_manager).unwrap();
        tot2.encode_lb_change(0..5, &mut cnf2, &mut var_manager)
            .unwrap();
        assert_eq!(cnf1.len(), cnf2.len());
        assert_eq!(cnf1.len(), tot1.n_clauses());
        assert_eq!(cnf2.len(), tot2.n_clauses());
    }

    #[test]
    fn reserve() {
        let mut tot = Totalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::from_next_free(var![4]);
        tot.reserve(&mut var_manager);
        assert_eq!(var_manager.n_used(), 12);
        let mut cnf = Cnf::new();
        tot.encode_ub(0..3, &mut cnf, &mut var_manager).unwrap();
        assert_eq!(var_manager.n_used(), 12);
    }
}
