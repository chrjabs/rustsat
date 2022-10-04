//! # Totalizer Encoding
//!
//! Implementation of the binary adder tree totalizer encoding [1].
//! The implementation is incremental as extended in [2].
//!
//! The implementation is recursive.
//!
//! ## References
//!
//! [1] Olivier Bailleux and Yacine Boufkhad: _Efficient CNF Encoding of Boolean Cardinality Constraints_, CP 2003.
//! [2] Ruben Martins and Saurabh Joshi and Vasco Manquinho and Ines Lynce: _Incremental Cardinality Constraints for MaxSAT_, CP 2014.

use crate::{
    encodings::BoundType,
    instances::{ManageVars, SatInstance},
    types::Lit,
};

pub struct Totalizer {
    /// Input literals already in the tree
    in_lits: Vec<Lit>,
    /// Input literals not yet in the tree
    lit_buffer: Vec<Lit>,
    /// The root of the tree, if constructed
    root: Option<TotNode>,
}

impl Totalizer {
    /// Recursively builds the tree data structure
    fn build_tree(in_lits: &[Lit]) -> TotNode {
        assert_ne!(in_lits.len(), 0);

        if in_lits.len() == 1 {
            return TotNode::new_leaf(in_lits[0]);
        };

        let split = in_lits.len() / 2;
        let left = Totalizer::build_tree(&in_lits[..split]);
        let right = Totalizer::build_tree(&in_lits[split..]);

        TotNode::new_internal(left, right)
    }
}

enum TotNode {
    Leaf {
        /// The input literal to the tree
        lit: Lit,
    },
    Internal {
        /// The output literals of this node
        out_lits: Vec<Lit>,
        /// The path length to leaf furthest away in the subtree
        depth: u64,
        /// The number of clauses this node produced
        n_clauses: u64,
        /// The maximum output this node can have
        max_val: u64,
        /// The maximum right hand side encoded by this node
        max_rhs: u64,
        /// The left child
        left: Box<TotNode>,
        /// The right child
        right: Box<TotNode>,
    },
}

impl TotNode {
    /// Constructs a new leaf node
    fn new_leaf(lit: Lit) -> TotNode {
        TotNode::Leaf { lit }
    }

    /// Constructs a new internal node
    fn new_internal(left: TotNode, right: TotNode) -> TotNode {
        let left_depth = match left {
            TotNode::Leaf { .. } => 0,
            TotNode::Internal { depth, .. } => depth,
        };
        let right_depth = match right {
            TotNode::Leaf { .. } => 0,
            TotNode::Internal { depth, .. } => depth,
        };
        TotNode::Internal {
            out_lits: vec![],
            depth: if left_depth > right_depth {
                left_depth + 1
            } else {
                right_depth + 1
            },
            n_clauses: 0,
            max_rhs: 0,
            max_val: match left {
                TotNode::Leaf { .. } => 1,
                TotNode::Internal { max_val, .. } => max_val,
            } + match right {
                TotNode::Leaf { .. } => 1,
                TotNode::Internal { max_val, .. } => max_val,
            },
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// Encodes the adder for this node from values `min_enc` to `max_enc`.
    /// This method only produces the encoding and does _not_ change any of the stats of the node.
    fn encode_from_till<VM: ManageVars>(
        &self,
        min_enc: u64,
        max_enc: u64,
        var_manager: &mut VM,
        bound_type: BoundType,
    ) -> SatInstance<VM> {
        match self {
            TotNode::Leaf { .. } => return SatInstance::new(),
            TotNode::Internal {
                out_lits,
                max_val,
                left,
                right,
                ..
            } => {
                if min_enc > max_val {
                    return SatInstance::new();
                };
                let max_enc = if max_enc > max_val { *max_val } else { max_enc };
                // Reserve vars if needed
                if (out_lits.len() as u64) < max_enc {
                    self.reserver_vars_to(max_enc, var_manager);
                }
                // Encode adder for current node
                let inst = SatInstance::new_with_manager(var_manager);
                let left_lits = match **left {
                    TotNode::Leaf { lit } => &vec![lit][..],
                    TotNode::Internal { out_lits: lits, .. } => &lits[..],
                };
                let right_lits = match **right {
                    TotNode::Leaf { lit } => &vec![lit][..],
                    TotNode::Internal { out_lits: lits, .. } => &lits[..],
                };
                // Iterate through all value combinations
                for left_val in 0..=left_lits.len() {
                    for right_val in 0..=right_lits.len() {
                        let sum_val = left_val + right_val;
                        if sum_val > max_enc + 1 || sum_val < min_enc {
                            continue;
                        }
                        // Upper bounding
                        match bound_type {
                            BoundType::UB | BoundType::EQ => {
                                let mut lhs = vec![];
                                if left_val != 0 {
                                    lhs.push(left_lits[left_val - 1]);
                                }
                                if right_val != 0 {
                                    lhs.push(right_lits[right_val - 1]);
                                }
                                if lhs.len() > 0 {
                                    // (left > x) & (right > y) -> (out > x+y)
                                    inst.add_and_impl_lit(lhs, out_lits[sum_val - 1]);
                                }
                            }
                            _ => (),
                        };
                        // Lower bounding
                        match bound_type {
                            BoundType::LB | BoundType::EQ => {
                                let mut lhs = vec![];
                                if left_val < left_lits.len() {
                                    lhs.push(!left_lits[left_val]);
                                }
                                if right_val < left_lits.len() {
                                    lhs.push(!right_lits[right_val]);
                                }
                                if lhs.len() > 0 {
                                    // (left <= x) & (right <= y) -> (out <= x+y)
                                    inst.add_and_impl_lit(lhs, !out_lits[sum_val]);
                                }
                            }
                            _ => (),
                        };
                    }
                }
                inst
            }
        }
    }

    /// Encodes the adder from the children to this node up to a given maximum
    /// right hand side. Recurses depth first. Returns  the number of newly
    /// added clauses. Always encodes the full totalizer.
    fn encode_rec<VM: ManageVars>(
        &mut self,
        max_enc: u64,
        var_manager: &mut VM,
        bound_type: BoundType,
    ) -> SatInstance<VM> {
        match self {
            TotNode::Leaf { .. } => {
                return self.encode_from_till(0, max_enc, var_manager, bound_type)
            }
            TotNode::Internal {
                max_rhs,
                max_val,
                n_clauses,
                left,
                right,
                ..
            } => {
                // Ignore all previous encoding and encode from scratch
                // Recurse
                let inst = left.encode_rec(max_enc, var_manager, bound_type);
                inst.extend(right.encode_rec(max_enc, var_manager, bound_type));
                // Encode adder for current node
                let local_inst = self.encode_from_till(0, max_enc, var_manager, bound_type);
                // Update stats
                *n_clauses += local_inst.n_clauses() as u64;
                *max_rhs = if max_enc < *max_val {
                    max_enc
                } else {
                    *max_val
                };
                inst.extend(local_inst);
                inst
            }
        }
    }

    /// Encodes the adder from the children to this node up to a given maximum
    /// right hand side. Recurses depth first. Returns the new `next_idx` and
    /// the number of newly added clauses. Incrementally only encodes new
    /// clauses.
    fn encode_change_rec<VM: ManageVars>(
        &mut self,
        max_enc: u64,
        var_manager: &mut VM,
        bound_type: BoundType,
    ) -> SatInstance<VM> {
        match self {
            TotNode::Leaf { .. } => {
                return self.encode_from_till(0, max_enc, var_manager, bound_type)
            }
            TotNode::Internal {
                max_rhs,
                max_val,
                n_clauses,
                left,
                right,
                ..
            } => {
                // Ignore all previous encoding and encode from scratch
                // Recurse
                let inst = left.encode_change_rec(max_enc, var_manager, bound_type);
                inst.extend(right.encode_change_rec(max_enc, var_manager, bound_type));
                // Encode adder for current node
                let local_inst = self.encode_from_till(*max_rhs, max_enc, var_manager, bound_type);
                // Update stats
                *n_clauses += local_inst.n_clauses() as u64;
                *max_rhs = if max_enc < *max_val {
                    max_enc
                } else {
                    *max_val
                };
                inst.extend(local_inst);
                inst
            }
        }
    }

    /// Reserves variables this node might need up to `max_res`.
    fn reserve_vars_to<VM: ManageVars>(&mut self, max_res: u64, var_manager: &mut VM) {
        match self {
            TotNode::Leaf { .. } => (),
            TotNode::Internal {
                out_lits, max_val, ..
            } => {
                let max_res = if max_res > max_val {
                    *max_val as usize
                } else {
                    max_res as usize
                };
                out_lits.reserve(max_res - out_lits.len());
                for _ in out_lits.len()..max_res {
                    out_lits.push(var_manager.next_free().pos_lit());
                }
            }
        }
    }

    /// Reserves all variables this node might need. This is used if variables
    /// in the totalizer should have consecutive indices.
    fn reserve_all_vars<VM: ManageVars>(&mut self, var_manager: &mut VM) {
        match self {
            TotNode::Leaf { .. } => (),
            TotNode::Internal { max_val, .. } => self.reserve_vars_to(*max_val, var_manager),
        }
    }

    /// Reserves all variables this node and the lower subtree might need. This
    /// is used if variables in the totalizer should have consecutive indices.
    fn reserve_all_vars_rec<VM: ManageVars>(&mut self, var_manager: &mut VM) {
        match self {
            TotNode::Leaf { .. } => (),
            TotNode::Internal { left, right, .. } => {
                // Recursion
                left.reserve_vars_rec(var_manager);
                right.reserve_vars_rec(var_manager);
            }
        };
        self.reserve_all_vars(var_manager)
    }
}
