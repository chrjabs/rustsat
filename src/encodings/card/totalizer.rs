//! # Totalizer Encoding
//!
//! Implementation of the binary adder tree totalizer encoding \[1\].
//! The implementation is incremental as extended in \[2\].
//! The implementation is recursive.
//!
//! ## References
//!
//! - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
//! - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.

use super::{Encode, EncodingError, IncEncode, IncLB, IncUB, LB, UB};
use crate::{
    encodings::EncodeStats,
    instances::{ManageVars, CNF},
    types::Lit,
};
use std::{cmp, slice};

/// Implementation of the binary adder tree totalizer encoding \[1\].
/// The implementation is incremental as extended in \[2\].
/// The implementation is recursive.
///
/// # References
///
/// - \[1\] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
/// - \[2\] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.
#[derive(Default)]
pub struct Totalizer {
    /// Input literals to the totalizer
    in_lits: Vec<Lit>,
    /// Index of the next literal in [`Totalizer::in_lit`] that is not in the tree yet
    not_enc_idx: usize,
    /// The root of the tree, if constructed
    root: Option<Box<Node>>,
    /// The number of variables in the totalizer
    n_vars: usize,
    /// The number of clauses in the totalizer
    n_clauses: usize,
}

impl Totalizer {
    /// Recursively builds the tree data structure
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
                None => Some(Box::new(subtree)),
                Some(old_root) => {
                    let new_root = Node::new_internal(*old_root, subtree);
                    Some(Box::new(new_root))
                }
            };
            self.not_enc_idx = self.in_lits.len();
        }
    }

    /// Gets the maximum depth of the tree
    pub fn get_depth(&mut self) -> usize {
        match &self.root {
            None => 0,
            Some(root_node) => root_node.get_depth(),
        }
    }
}

impl Encode for Totalizer {
    type Iter<'a> = TotIter<'a>;

    fn iter(&self) -> Self::Iter<'_> {
        self.in_lits.iter().copied()
    }

    fn n_lits(&self) -> usize {
        self.in_lits.len()
    }
}

impl IncEncode for Totalizer {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        if let Some(root) = &mut self.root {
            root.reserve_all_vars_rec(var_manager);
        }
    }
}

impl UB for Totalizer {
    fn encode_ub(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        if min_ub > max_ub {
            return Err(EncodingError::InvalidLimits);
        };
        self.extend_tree();
        Ok(match &mut self.root {
            None => CNF::new(),
            Some(root) => {
                let n_vars_before = var_manager.n_used();
                let cnf = root.encode_ub_rec(min_ub, max_ub, var_manager);
                self.n_clauses += cnf.n_clauses();
                self.n_vars += var_manager.n_used() - n_vars_before;
                cnf
            }
        })
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, EncodingError> {
        if self.not_enc_idx != self.in_lits.len() {
            return Err(EncodingError::NotEncoded);
        };
        if ub >= self.in_lits.len() {
            return Ok(vec![]);
        };
        match &self.root {
            None => Err(EncodingError::NotEncoded),
            Some(root_node) => match &**root_node {
                Node::Leaf { lit } => Ok(vec![!*lit]),
                Node::Internal {
                    out_lits,
                    min_max_ub,
                    ..
                } => {
                    if let Some((min_ub, max_ub)) = min_max_ub {
                        if *max_ub < ub || *min_ub > ub {
                            Err(EncodingError::NotEncoded)
                        } else {
                            Ok(vec![!out_lits[ub].unwrap()])
                        }
                    } else {
                        Err(EncodingError::NotEncoded)
                    }
                }
            },
        }
    }
}

impl LB for Totalizer {
    fn encode_lb(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        if min_lb > max_lb {
            return Err(EncodingError::InvalidLimits);
        };
        self.extend_tree();
        Ok(match &mut self.root {
            None => CNF::new(),
            Some(root) => {
                let n_vars_before = var_manager.n_used();
                let cnf = root.encode_lb_rec(min_lb, max_lb, var_manager);
                self.n_clauses += cnf.n_clauses();
                self.n_vars += var_manager.n_used() - n_vars_before;
                cnf
            }
        })
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, EncodingError> {
        if self.not_enc_idx != self.in_lits.len() {
            return Err(EncodingError::NotEncoded);
        };
        if lb > self.in_lits.len() {
            return Err(EncodingError::Unsat);
        } else if lb == 0 {
            return Ok(vec![]);
        };
        match &self.root {
            None => Err(EncodingError::NotEncoded),
            Some(root_node) => match &**root_node {
                Node::Leaf { lit } => Ok(vec![*lit]),
                Node::Internal {
                    out_lits,
                    min_max_lb,
                    ..
                } => {
                    if let Some((min_lb, max_lb)) = min_max_lb {
                        if *max_lb < lb || *min_lb > lb {
                            Err(EncodingError::NotEncoded)
                        } else {
                            Ok(vec![out_lits[lb - 1].unwrap()])
                        }
                    } else {
                        Err(EncodingError::NotEncoded)
                    }
                }
            },
        }
    }
}

impl IncUB for Totalizer {
    fn encode_ub_change(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        if min_ub > max_ub {
            return Err(EncodingError::InvalidLimits);
        };
        self.extend_tree();
        Ok(match &mut self.root {
            None => CNF::new(),
            Some(root) => {
                let n_vars_before = var_manager.n_used();
                let cnf = root.encode_ub_change_rec(min_ub, max_ub, var_manager);
                self.n_clauses += cnf.n_clauses();
                self.n_vars += var_manager.n_used() - n_vars_before;
                cnf
            }
        })
    }
}

impl IncLB for Totalizer {
    fn encode_lb_change(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> Result<CNF, EncodingError> {
        if min_lb > max_lb {
            return Err(EncodingError::InvalidLimits);
        };
        self.extend_tree();
        Ok(match &mut self.root {
            None => CNF::new(),
            Some(root) => {
                let n_vars_before = var_manager.n_used();
                let cnf = root.encode_lb_change_rec(min_lb, max_lb, var_manager);
                self.n_clauses += cnf.n_clauses();
                self.n_vars += var_manager.n_used() - n_vars_before;
                cnf
            }
        })
    }
}

impl EncodeStats for Totalizer {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> usize {
        self.n_vars
    }
}

impl From<Vec<Lit>> for Totalizer {
    fn from(lits: Vec<Lit>) -> Self {
        Self {
            in_lits: lits,
            not_enc_idx: Default::default(),
            root: Default::default(),
            n_vars: Default::default(),
            n_clauses: Default::default(),
        }
    }
}

impl FromIterator<Lit> for Totalizer {
    fn from_iter<T: IntoIterator<Item = Lit>>(iter: T) -> Self {
        Self {
            in_lits: Vec::from_iter(iter),
            not_enc_idx: Default::default(),
            root: Default::default(),
            n_vars: Default::default(),
            n_clauses: Default::default(),
        }
    }
}

impl Extend<Lit> for Totalizer {
    fn extend<T: IntoIterator<Item = Lit>>(&mut self, iter: T) {
        self.in_lits.extend(iter)
    }
}

type TotIter<'a> = std::iter::Copied<std::slice::Iter<'a, Lit>>;

enum Node {
    Leaf {
        /// The input literal to the tree
        lit: Lit,
    },
    Internal {
        /// The output literals of this node
        out_lits: Vec<Option<Lit>>,
        /// The path length to the leaf furthest away in the subtree
        depth: usize,
        /// The number of clauses this node produced
        n_clauses: usize,
        /// The maximum output this node can have
        max_val: usize,
        /// The minimum and maximum upper bound encoded by this node
        min_max_ub: Option<(usize, usize)>,
        /// The minimum and maximum upper bound encoded by this node
        min_max_lb: Option<(usize, usize)>,
        /// The left child
        left: Box<Node>,
        /// The right child
        right: Box<Node>,
    },
}

impl Node {
    /// Constructs a new leaf node
    fn new_leaf(lit: Lit) -> Node {
        Node::Leaf { lit }
    }

    /// Constructs a new internal node
    fn new_internal(left: Node, right: Node) -> Node {
        let left_depth = match left {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => depth,
        };
        let right_depth = match right {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => depth,
        };
        Node::Internal {
            out_lits: vec![],
            depth: if left_depth > right_depth {
                left_depth + 1
            } else {
                right_depth + 1
            },
            n_clauses: 0,
            min_max_ub: None,
            min_max_lb: None,
            max_val: match left {
                Node::Leaf { .. } => 1,
                Node::Internal { max_val, .. } => max_val,
            } + match right {
                Node::Leaf { .. } => 1,
                Node::Internal { max_val, .. } => max_val,
            },
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Gets the maximum depth of the subtree rooted in this node
    fn get_depth(&self) -> usize {
        match self {
            Node::Leaf { .. } => 1,
            Node::Internal { depth, .. } => *depth,
        }
    }

    /// Encodes the upper bound adder for this node from `min_ub` to `max_ub`.
    /// This method only produces the encoding and does _not_ change any of the
    /// stats of the node.
    fn encode_ub_from_till(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> CNF {
        if min_ub > max_ub {
            return CNF::new();
        };
        // Reserve vars if needed
        self.reserve_vars_from_till(min_ub, max_ub, var_manager);
        match self {
            Node::Leaf { .. } => CNF::new(),
            Node::Internal {
                out_lits,
                max_val,
                left,
                right,
                ..
            } => {
                if min_ub > *max_val {
                    return CNF::new();
                };
                let max_ub = if max_ub > *max_val { *max_val } else { max_ub };
                // Encode adder for current node
                let mut cnf = CNF::new();
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
                for left_val in 0..=left_lits.len() {
                    for right_val in 0..=right_lits.len() {
                        let sum_val = left_val + right_val;
                        if sum_val > max_ub + 1 || sum_val <= min_ub {
                            continue;
                        }
                        let mut lhs = vec![];
                        if left_val != 0 {
                            lhs.push(left_lits[left_val - 1].unwrap());
                        }
                        if right_val != 0 {
                            lhs.push(right_lits[right_val - 1].unwrap());
                        }
                        if !lhs.is_empty() {
                            // (left > x) & (right > y) -> (out > x+y)
                            cnf.add_cube_impl_lit(lhs, out_lits[sum_val - 1].unwrap());
                        }
                    }
                }
                cnf
            }
        }
    }

    /// Encodes the lower bound adder for this node from `min_lb` to `max_lb`.
    /// This method only produces the encoding and does _not_ change any of the
    /// stats of the node.
    fn encode_lb_from_till(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> CNF {
        if min_lb > max_lb {
            return CNF::new();
        };
        // Reserve vars if needed
        self.reserve_vars_from_till(
            if min_lb > 1 { min_lb - 1 } else { 0 },
            if max_lb > 1 { max_lb - 1 } else { 0 },
            var_manager,
        );
        match self {
            Node::Leaf { .. } => CNF::new(),
            Node::Internal {
                out_lits,
                max_val,
                left,
                right,
                ..
            } => {
                if min_lb > *max_val {
                    return CNF::new();
                };
                let max_lb = if max_lb > *max_val { *max_val } else { max_lb };
                // Encode adder for current node
                let mut cnf = CNF::new();
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
                for left_val in 0..=left_lits.len() {
                    for right_val in 0..=right_lits.len() {
                        let sum_val = left_val + right_val;
                        if sum_val >= max_lb || sum_val + 1 < min_lb {
                            continue;
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
                            cnf.add_cube_impl_lit(lhs, !out_lits[sum_val].unwrap());
                        }
                    }
                }
                cnf
            }
        }
    }

    /// Encodes the upper bound adder from the children to this node between
    /// `min_ub` and `max_ub`. Recurses depth first. Always returns the full
    /// requested CNF encoding.
    fn encode_ub_rec(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> CNF {
        let mut cnf = match self {
            Node::Leaf { .. } => return CNF::new(),
            Node::Internal { left, right, .. } => {
                let left_min_ub = Node::compute_required_min_rhs(min_ub, max_ub, right);
                let right_min_ub = Node::compute_required_min_rhs(min_ub, max_ub, left);
                // Recurse
                let mut cnf = left.encode_ub_rec(left_min_ub, max_ub, var_manager);
                cnf.extend(right.encode_ub_rec(right_min_ub, max_ub, var_manager));
                cnf
            }
        };
        // Ignore all previous encoding and encode from scratch
        let local_cnf = self.encode_ub_from_till(min_ub, max_ub, var_manager);
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                min_max_ub,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *min_max_ub = Some((min_ub, cmp::min(*max_val, max_ub)));
                *n_clauses += local_cnf.n_clauses();
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Encodes the lower bound adder from the children to this node between
    /// `min_rhs` and `max_rhs`. Recurses depth first. Always returns the full
    /// requested CNF encoding.
    fn encode_lb_rec(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> CNF {
        let mut cnf = match self {
            Node::Leaf { .. } => return CNF::new(),
            Node::Internal { left, right, .. } => {
                let left_min_lb = Node::compute_required_min_rhs(min_lb, max_lb, right);
                let right_min_lb = Node::compute_required_min_rhs(min_lb, max_lb, left);
                // Recurse
                let mut cnf = left.encode_lb_rec(left_min_lb, max_lb, var_manager);
                cnf.extend(right.encode_lb_rec(right_min_lb, max_lb, var_manager));
                cnf
            }
        };
        // Ignore all previous encoding and encode from scratch
        let local_cnf = self.encode_lb_from_till(min_lb, max_lb, var_manager);
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                min_max_lb,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *min_max_lb = Some((min_lb, cmp::min(*max_val, max_lb)));
                *n_clauses += local_cnf.n_clauses();
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Encodes the upper bound adder from the children to this node between a
    /// given `min_ub` and `max_ub`. Recurses depth first. Incrementally only
    /// encodes new clauses.
    fn encode_ub_change_rec(
        &mut self,
        min_ub: usize,
        max_ub: usize,
        var_manager: &mut dyn ManageVars,
    ) -> CNF {
        let (mut cnf, min_max_already_encoded) = match self {
            Node::Leaf { .. } => return CNF::new(),
            Node::Internal {
                left,
                right,
                min_max_ub,
                ..
            } => {
                let left_min_ub = Node::compute_required_min_rhs(min_ub, max_ub, right);
                let right_min_ub = Node::compute_required_min_rhs(min_ub, max_ub, left);
                // Recurse
                let mut cnf = left.encode_ub_change_rec(left_min_ub, max_ub, var_manager);
                cnf.extend(right.encode_ub_change_rec(right_min_ub, max_ub, var_manager));
                (cnf, *min_max_ub)
            }
        };
        // Encode changes for current node
        let local_cnf = match min_max_already_encoded {
            None => {
                // First time encoding this node
                self.encode_ub_from_till(min_ub, max_ub, var_manager)
            }
            Some((old_min_ub, old_max_ub)) => {
                // Part already encoded
                let mut local_cnf = CNF::new();
                if min_ub < old_min_ub {
                    local_cnf.extend(self.encode_ub_from_till(min_ub, old_min_ub - 1, var_manager));
                };
                if max_ub > old_max_ub {
                    local_cnf.extend(self.encode_ub_from_till(old_max_ub + 1, max_ub, var_manager));
                };
                local_cnf
            }
        };
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                min_max_ub,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *n_clauses += local_cnf.n_clauses();
                *min_max_ub = if let Some((old_min_ub, old_max_ub)) = *min_max_ub {
                    Some((
                        cmp::min(min_ub, old_min_ub),
                        cmp::min(*max_val, cmp::max(max_ub, old_max_ub)),
                    ))
                } else {
                    Some((min_ub, cmp::min(max_ub, *max_val)))
                };
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Encodes the lower bound adder from the children to this node between a given
    /// `min_lb` and `max_lb`. Recurses depth first.
    /// Incrementally only
    /// encodes new clauses.
    fn encode_lb_change_rec(
        &mut self,
        min_lb: usize,
        max_lb: usize,
        var_manager: &mut dyn ManageVars,
    ) -> CNF {
        let (mut cnf, min_max_already_encoded) = match self {
            Node::Leaf { .. } => return CNF::new(),
            Node::Internal {
                left,
                right,
                min_max_lb,
                ..
            } => {
                let left_min_lb = Node::compute_required_min_rhs(min_lb, max_lb, right);
                let right_min_lb = Node::compute_required_min_rhs(min_lb, max_lb, left);
                // Recurse
                let mut cnf = left.encode_lb_change_rec(left_min_lb, max_lb, var_manager);
                cnf.extend(right.encode_lb_change_rec(right_min_lb, max_lb, var_manager));
                (cnf, *min_max_lb)
            }
        };
        // Encode changes for current node
        let local_cnf = match min_max_already_encoded {
            None => {
                // First time encoding this node
                self.encode_lb_from_till(min_lb, max_lb, var_manager)
            }
            Some((old_min_rhs, old_max_rhs)) => {
                // Part already encoded
                let mut local_cnf = CNF::new();
                if min_lb < old_min_rhs {
                    local_cnf.extend(self.encode_lb_from_till(
                        min_lb,
                        old_min_rhs - 1,
                        var_manager,
                    ));
                };
                if max_lb > old_max_rhs {
                    local_cnf.extend(self.encode_lb_from_till(
                        old_max_rhs + 1,
                        max_lb,
                        var_manager,
                    ));
                };
                local_cnf
            }
        };
        match self {
            Node::Leaf { .. } => local_cnf,
            Node::Internal {
                min_max_lb,
                max_val,
                n_clauses,
                ..
            } => {
                // Update stats
                *n_clauses += local_cnf.n_clauses();
                *min_max_lb = if let Some((old_min_lb, old_max_lb)) = *min_max_lb {
                    Some((
                        cmp::min(min_lb, old_min_lb),
                        cmp::min(*max_val, cmp::max(max_lb, old_max_lb)),
                    ))
                } else {
                    Some((min_lb, cmp::min(max_lb, *max_val)))
                };
                cnf.extend(local_cnf);
                cnf
            }
        }
    }

    /// Reserves variables this node might need for indices `min_idx` to
    /// `max_idx`.
    fn reserve_vars_from_till(
        &mut self,
        min_idx: usize,
        max_idx: usize,
        var_manager: &mut dyn ManageVars,
    ) {
        match self {
            Node::Leaf { .. } => (),
            Node::Internal {
                out_lits, max_val, ..
            } => {
                let max_idx = if max_idx >= *max_val {
                    *max_val - 1
                } else {
                    max_idx
                };
                if out_lits.len() < max_idx + 1 {
                    out_lits.resize(max_idx + 1, None);
                };
                for olit in out_lits.iter_mut().take(max_idx + 1).skip(min_idx) {
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
        self.reserve_vars_from_till(0, max_val, var_manager);
    }

    /// Reserves all variables this node and the lower subtree might need. This
    /// is used if variables in the totalizer should have consecutive indices.
    fn reserve_all_vars_rec(&mut self, var_manager: &mut dyn ManageVars) {
        match self {
            Node::Leaf { .. } => return,
            Node::Internal { left, right, .. } => {
                // Recursion
                left.reserve_all_vars_rec(var_manager);
                right.reserve_all_vars_rec(var_manager);
            }
        };
        self.reserve_all_vars(var_manager)
    }

    /// Computes the required `min_rhs` for a node given a requested `min_rhs`
    /// and `max_rhs` of the parent and its sibling.
    fn compute_required_min_rhs(
        min_rhs_requested: usize,
        max_rhs_requested: usize,
        sibling: &Node,
    ) -> usize {
        match *sibling {
            Node::Leaf { .. } => {
                if min_rhs_requested > 1 {
                    min_rhs_requested - 1
                } else {
                    0
                }
            }
            Node::Internal { max_val, .. } => {
                if max_rhs_requested < max_val {
                    if min_rhs_requested > max_rhs_requested {
                        min_rhs_requested - max_rhs_requested
                    } else {
                        0
                    }
                } else if min_rhs_requested > max_val {
                    min_rhs_requested - max_val
                } else {
                    0
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Node, Totalizer};
    use crate::{
        encodings::{
            card::{BothB, IncLB, IncUB, LB, UB},
            EncodeStats, EncodingError,
        },
        instances::{BasicVarManager, ManageVars},
        lit,
        types::Lit,
    };

    #[test]
    fn adder_1() {
        // Child nodes
        let child1 = Node::new_leaf(lit![0]);
        let child2 = Node::new_leaf(lit![1]);
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let mut cnf = node.encode_ub_from_till(0, 2, &mut var_manager);
        cnf.extend(node.encode_lb_from_till(0, 2, &mut var_manager));
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 2),
        };
        assert_eq!(cnf.n_clauses(), 6);
    }

    #[test]
    fn adder_2() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![Some(lit![1]), Some(lit![2])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            min_max_ub: Some((0, 2)),
            min_max_lb: Some((0, 2)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![Some(lit![3]), Some(lit![4])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            min_max_ub: Some((0, 2)),
            min_max_lb: Some((0, 2)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let mut cnf = node.encode_ub_from_till(0, 4, &mut var_manager);
        cnf.extend(node.encode_lb_from_till(0, 4, &mut var_manager));
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.n_clauses(), 16);
    }

    #[test]
    fn adder_3() {
        // Child nodes
        let child1 = Node::new_leaf(lit![0]);
        let child2 = Node::new_leaf(lit![1]);
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let cnf = node.encode_lb_from_till(0, 1, &mut var_manager);
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 1),
        };
        assert_eq!(cnf.n_clauses(), 1);
    }

    #[test]
    fn partial_adder_1() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![Some(lit![1]), Some(lit![2]), Some(lit![3])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            min_max_ub: Some((0, 2)),
            min_max_lb: Some((0, 2)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![Some(lit![4]), Some(lit![5]), Some(lit![6])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            min_max_ub: Some((0, 2)),
            min_max_lb: Some((0, 2)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let mut cnf = node.encode_ub_from_till(0, 3, &mut var_manager);
        cnf.extend(node.encode_lb_from_till(0, 3, &mut var_manager));
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.n_clauses(), 18);
    }

    #[test]
    fn partial_adder_already_encoded() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![Some(lit![1]), Some(lit![2]), Some(lit![3])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            min_max_ub: Some((0, 2)),
            min_max_lb: Some((0, 2)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![Some(lit![4]), Some(lit![5]), Some(lit![6])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            min_max_ub: Some((0, 2)),
            min_max_lb: Some((0, 2)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let mut cnf = node.encode_ub_from_till(3, 2, &mut var_manager);
        cnf.extend(node.encode_lb_from_till(3, 2, &mut var_manager));
        assert_eq!(cnf.n_clauses(), 0);
    }

    #[test]
    fn partial_adder_2() {
        // (Inconsistent) child nodes
        let child1 = Node::Internal {
            out_lits: vec![Some(lit![1]), Some(lit![2]), Some(lit![3])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            min_max_ub: Some((0, 2)),
            min_max_lb: Some((0, 2)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let child2 = Node::Internal {
            out_lits: vec![Some(lit![4]), Some(lit![5]), Some(lit![6])],
            depth: 1,
            n_clauses: 0,
            max_val: 2,
            min_max_ub: Some((0, 2)),
            min_max_lb: Some((0, 2)),
            // Dummy nodes for children
            left: Box::new(Node::new_leaf(lit![0])),
            right: Box::new(Node::new_leaf(lit![0])),
        };
        let mut node = Node::new_internal(child1, child2);
        let mut var_manager = BasicVarManager::new();
        let mut cnf = node.encode_ub_from_till(2, 3, &mut var_manager);
        cnf.extend(node.encode_lb_from_till(2, 3, &mut var_manager));
        match &node {
            Node::Leaf { .. } => panic!(),
            Node::Internal { out_lits, .. } => assert_eq!(out_lits.len(), 4),
        };
        assert_eq!(cnf.n_clauses(), 12);
    }

    #[test]
    fn tot_functions() {
        let mut tot = Totalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        assert_eq!(tot.enforce_ub(2), Err(EncodingError::NotEncoded));
        assert_eq!(tot.enforce_lb(2), Err(EncodingError::NotEncoded));
        let mut var_manager = BasicVarManager::new();
        let mut cnf = tot.encode_ub(0, 4, &mut var_manager).unwrap();
        cnf.extend(tot.encode_lb(0, 4, &mut var_manager).unwrap());
        assert_eq!(tot.get_depth(), 3);
        assert_eq!(cnf.n_clauses(), 28);
        assert_eq!(tot.n_clauses(), 28);
        assert_eq!(tot.n_vars(), 8);
        assert_eq!(tot.enforce_ub(2).unwrap().len(), 1);
        assert_eq!(tot.enforce_lb(2).unwrap().len(), 1);
    }

    #[test]
    fn tot_functions_min_rhs() {
        let mut tot = Totalizer::default();
        tot.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let cnf = tot.encode_both(3, 3, &mut var_manager).unwrap();
        assert_eq!(tot.get_depth(), 3);
        assert_eq!(cnf.n_clauses(), 12);
        assert_eq!(cnf.n_clauses(), tot.n_clauses());
    }

    #[test]
    fn tot_incremental_building_ub() {
        let mut tot1 = Totalizer::default();
        tot1.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let cnf1 = tot1.encode_ub(0, 4, &mut var_manager).unwrap();
        let mut tot2 = Totalizer::default();
        tot2.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let mut cnf2 = tot2.encode_ub(0, 2, &mut var_manager).unwrap();
        cnf2.extend(tot2.encode_ub_change(0, 4, &mut var_manager).unwrap());
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
        assert_eq!(cnf1.n_clauses(), tot1.n_clauses());
        assert_eq!(cnf2.n_clauses(), tot2.n_clauses());
    }

    #[test]
    fn tot_incremental_building_lb() {
        let mut tot1 = Totalizer::default();
        tot1.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let cnf1 = tot1.encode_lb(0, 4, &mut var_manager).unwrap();
        let mut tot2 = Totalizer::default();
        tot2.extend(vec![lit![0], lit![1], lit![2], lit![3]]);
        let mut var_manager = BasicVarManager::new();
        let mut cnf2 = tot2.encode_lb(0, 2, &mut var_manager).unwrap();
        cnf2.extend(tot2.encode_lb_change(0, 4, &mut var_manager).unwrap());
        assert_eq!(cnf1.n_clauses(), cnf2.n_clauses());
        assert_eq!(cnf1.n_clauses(), tot1.n_clauses());
        assert_eq!(cnf2.n_clauses(), tot2.n_clauses());
    }

    #[test]
    fn invalid_useage() {
        let mut tot = Totalizer::default();
        let mut var_manager = BasicVarManager::new();
        assert_eq!(
            tot.encode_ub(5, 4, &mut var_manager),
            Err(EncodingError::InvalidLimits)
        );
    }
}
