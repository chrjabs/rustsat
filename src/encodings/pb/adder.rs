//! # Binary Adder Encoding
//!
//! Implementation of the binary adder encoding first described in \[1\].
//! The implementation follows the description in \[2\].
//!
//! **Note**: the CNF definition of the full adder in \[2\] is incorrect, but it is implemented
//! correctly here.
//!
//! ## References
//!
//! - \[1\] Joose P. Warners: _A linear-time transformation of linear inequalities into conjunctive
//!     normal form_, Inf. Process. Lett. 1998.
//! - \[2\] Niklas Eén and Niklas Sörensson: _Translating Pseudo-Boolean Constraints into SAT_,
//!     JSAT 2006.

#![allow(clippy::module_name_repetitions)]

use std::collections::VecDeque;

use crate::{
    clause,
    encodings::{CollectClauses, EncodeStats, Error},
    instances::ManageVars,
    types::{Clause, Lit, RsHashMap},
    OutOfMemory,
};

use super::{
    BoundLower, BoundLowerIncremental, BoundUpper, BoundUpperIncremental, Encode, EncodeIncremental,
};

/// Implementation of the binary adder encoding first described in \[1\].
/// The implementation follows the description in \[2\].
///
/// ## References
///
/// - \[1\] Joose P. Warners: _A linear-time transformation of linear inequalities into conjunctive
///     normal form_, Inf. Process. Lett. 1998.
/// - \[2\] Niklas Eén and Niklas Sörensson: _Translating Pseudo-Boolean Constraints into SAT_,
///     JSAT 2006.
#[derive(Default, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct BinaryAdder {
    /// Input literals and weights for the encoding
    lit_buffer: RsHashMap<Lit, usize>,
    /// The encoding structure
    structure: Option<Structure>,
    /// Sum of all input weight
    weight_sum: usize,
    /// The number of variables
    n_vars: u32,
    /// The number of clauses
    n_clauses: usize,
    /// The node database of this encoding
    nodes: Vec<Node>,
}

/// The structure of a binary adder encoding
#[cfg_attr(feature = "internals", visibility::make(pub))]
#[cfg_attr(docsrs, doc(cfg(feature = "internals")))]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone)]
struct Structure {
    /// The output bits of the structure
    outputs: Vec<Option<Connection>>,
    /// Comparator structure for providing assumptions
    comparator: Vec<Option<Output>>,
}

impl BinaryAdder {
    fn extend_structure(&mut self) {
        if self.lit_buffer.is_empty() {
            return;
        }

        let mut buckets = Vec::new();

        // Add new input literals into buckets
        for (lit, weight) in self.lit_buffer.drain() {
            debug_assert_ne!(weight, 0);
            self.weight_sum += weight;
            let max_bucket = (usize::BITS - weight.leading_zeros()) as usize;
            if max_bucket >= buckets.len() {
                buckets.resize_with(max_bucket + 1, || VecDeque::with_capacity(1));
            }
            for (idx, bucket) in buckets.iter_mut().take(max_bucket + 1).enumerate() {
                if weight & (1usize << idx) != 0 {
                    // NOTE: we push to the front here in order to get input literals into the
                    // structure first
                    bucket.push_back(Connection::Input(lit));
                }
            }
        }

        // Add existing structure into buckets
        if let Some(structure) = &self.structure {
            if buckets.len() < structure.outputs.len() {
                buckets.resize_with(structure.outputs.len(), || VecDeque::with_capacity(1));
            }
            for (bucket, &output) in buckets.iter_mut().zip(&structure.outputs) {
                let Some(output) = output else {
                    continue;
                };
                bucket.push_back(output);
            }
        }

        // Build the encoding
        let mut idx = 0;
        while idx < buckets.len() {
            if idx == buckets.len() - 1 && buckets[idx].len() >= 2 {
                buckets.resize_with(buckets.len() + 1, || VecDeque::with_capacity(1));
            }
            while buckets[idx].len() >= 3 {
                let a = buckets[idx].pop_front().unwrap();
                let b = buckets[idx].pop_front().unwrap();
                let c = buckets[idx].pop_front().unwrap();

                self.nodes.push(Node::full(a, b, c));

                buckets[idx].push_back(Connection::Sum(self.nodes.len() - 1));
                buckets[idx + 1].push_back(Connection::Carry(self.nodes.len() - 1));
            }
            if buckets[idx].len() == 2 {
                let a = buckets[idx].pop_front().unwrap();
                let b = buckets[idx].pop_front().unwrap();

                self.nodes.push(Node::half(a, b));

                buckets[idx].push_back(Connection::Sum(self.nodes.len() - 1));
                buckets[idx + 1].push_back(Connection::Carry(self.nodes.len() - 1));
            }
            idx += 1;
        }

        // Store the structure
        self.structure = Some(Structure {
            outputs: buckets
                .into_iter()
                .map(|mut q| {
                    debug_assert!(q.len() <= 1);
                    q.pop_front()
                })
                .collect(),
            comparator: Vec::new(),
        });
    }
}

impl Encode for BinaryAdder {
    fn weight_sum(&self) -> usize {
        self.lit_buffer
            .iter()
            .fold(self.weight_sum, |sum, (_, w)| sum + w)
    }
}

impl BoundUpper for BinaryAdder {
    fn encode_ub<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), OutOfMemory>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize>,
    {
        // reset previous encoding status
        for node in &mut self.nodes {
            if let Node::Full { sum: Some(out), .. } | Node::Half { sum: Some(out), .. } = node {
                out.enc_if = false;
                out.enc_only_if = false;
            }
            if let Node::Full {
                carry: Some(out), ..
            }
            | Node::Half {
                carry: Some(out), ..
            } = node
            {
                out.enc_if = false;
                out.enc_only_if = false;
            }
        }
        self.encode_ub_change(range, collector, var_manager)
    }

    fn enforce_ub(&self, ub: usize) -> Result<Vec<Lit>, Error> {
        if ub >= self.weight_sum() {
            return Ok(vec![]);
        }
        let Some(structure) = &self.structure else {
            return Err(Error::NotEncoded);
        };
        let Some(Some(Output {
            bit, enc_if: true, ..
        })) = structure.comparator.get(ub)
        else {
            return Err(Error::NotEncoded);
        };
        Ok(vec![!*bit])
    }
}

impl BoundUpperIncremental for BinaryAdder {
    fn encode_ub_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), OutOfMemory>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize>,
    {
        let range = super::prepare_ub_range(self, range);
        if range.is_empty() {
            return Ok(());
        }

        let n_vars_before = var_manager.n_used();
        let n_clauses_before = collector.n_clauses();

        self.extend_structure();
        if let Some(structure) = &mut self.structure {
            // TODO: could maybe optimize some edge cases here where we are guaranteed to never use
            // certain outputs of the adder
            let mut outputs = Vec::with_capacity(structure.outputs.len());
            for con in &structure.outputs {
                if let Some(con) = con {
                    outputs.push(Some(get_bit_if(
                        *con,
                        &mut self.nodes,
                        collector,
                        var_manager,
                    )?));
                } else {
                    outputs.push(None);
                }
            }
            if structure.comparator.len() < range.end {
                structure.comparator.resize(range.end, None);
            }
            for val in range {
                let output = if let Some(output) = &mut structure.comparator[val] {
                    if output.enc_if {
                        continue;
                    }
                    output.enc_if = true;
                    output.bit
                } else {
                    let bit = var_manager.new_lit();
                    structure.comparator[val] = Some(Output {
                        bit,
                        enc_if: true,
                        enc_only_if: false,
                    });
                    bit
                };
                comparator_if(val, output, &outputs, collector)?;
            }
        }

        self.n_clauses += collector.n_clauses() - n_clauses_before;
        self.n_vars += var_manager.n_used() - n_vars_before;
        Ok(())
    }
}

impl BoundLower for BinaryAdder {
    fn encode_lb<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), OutOfMemory>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize>,
    {
        // reset previous encoding status
        for node in &mut self.nodes {
            if let Node::Full { sum: Some(out), .. } | Node::Half { sum: Some(out), .. } = node {
                out.enc_if = false;
                out.enc_only_if = false;
            }
            if let Node::Full {
                carry: Some(out), ..
            }
            | Node::Half {
                carry: Some(out), ..
            } = node
            {
                out.enc_if = false;
                out.enc_only_if = false;
            }
        }
        self.encode_lb_change(range, collector, var_manager)
    }

    fn enforce_lb(&self, lb: usize) -> Result<Vec<Lit>, Error> {
        if lb > self.weight_sum() {
            return Err(Error::Unsat);
        }
        if lb == 0 {
            return Ok(vec![]);
        }
        let Some(structure) = &self.structure else {
            return Err(Error::NotEncoded);
        };
        let Some(Some(Output {
            bit,
            enc_only_if: true,
            ..
        })) = structure.comparator.get(lb - 1)
        else {
            return Err(Error::NotEncoded);
        };
        Ok(vec![*bit])
    }
}

impl BoundLowerIncremental for BinaryAdder {
    fn encode_lb_change<Col, R>(
        &mut self,
        range: R,
        collector: &mut Col,
        var_manager: &mut dyn ManageVars,
    ) -> Result<(), OutOfMemory>
    where
        Col: CollectClauses,
        R: std::ops::RangeBounds<usize>,
    {
        let range = super::prepare_lb_range(self, range);
        if range.is_empty() {
            return Ok(());
        }

        let n_vars_before = var_manager.n_used();
        let n_clauses_before = collector.n_clauses();

        self.extend_structure();
        if let Some(structure) = &mut self.structure {
            // TODO: could maybe optimize some edge cases here where we are guaranteed to never use
            // certain outputs of the adder
            let mut outputs = Vec::with_capacity(structure.outputs.len());
            for con in &structure.outputs {
                if let Some(con) = con {
                    outputs.push(Some(get_bit_only_if(
                        *con,
                        &mut self.nodes,
                        collector,
                        var_manager,
                    )?));
                } else {
                    outputs.push(None);
                }
            }
            if structure.comparator.len() < range.end {
                structure.comparator.resize(range.end, None);
            }
            for val in range {
                let output = if let Some(output) = &mut structure.comparator[val - 1] {
                    if output.enc_if {
                        continue;
                    }
                    output.enc_only_if = true;
                    output.bit
                } else {
                    let bit = var_manager.new_lit();
                    structure.comparator[val - 1] = Some(Output {
                        bit,
                        enc_if: false,
                        enc_only_if: true,
                    });
                    bit
                };
                comparator_only_if(val - 1, output, &outputs, collector)?;
            }
        }

        self.n_clauses += collector.n_clauses() - n_clauses_before;
        self.n_vars += var_manager.n_used() - n_vars_before;
        Ok(())
    }
}

impl EncodeIncremental for BinaryAdder {
    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        self.extend_structure();

        if let Some(structure) = &self.structure {
            for &o in &structure.outputs {
                if let Some(Connection::Sum(node) | Connection::Carry(node)) = o {
                    reserve(&mut self.nodes[..=node], var_manager);
                }
            }
        }
    }
}

impl EncodeStats for BinaryAdder {
    fn n_clauses(&self) -> usize {
        self.n_clauses
    }

    fn n_vars(&self) -> u32 {
        self.n_vars
    }
}

impl From<RsHashMap<Lit, usize>> for BinaryAdder {
    fn from(lits: RsHashMap<Lit, usize>) -> Self {
        Self {
            lit_buffer: lits,
            ..Default::default()
        }
    }
}

impl FromIterator<(Lit, usize)> for BinaryAdder {
    fn from_iter<T: IntoIterator<Item = (Lit, usize)>>(iter: T) -> Self {
        let lits: RsHashMap<Lit, usize> = RsHashMap::from_iter(iter);
        Self::from(lits)
    }
}

impl Extend<(Lit, usize)> for BinaryAdder {
    fn extend<T: IntoIterator<Item = (Lit, usize)>>(&mut self, iter: T) {
        iter.into_iter().for_each(|(l, w)| {
            // Insert into buffer to be added to tree
            match self.lit_buffer.get_mut(&l) {
                Some(old_w) => *old_w += w,
                None => {
                    self.lit_buffer.insert(l, w);
                }
            };
        });
    }
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
enum Node {
    Full {
        a: Connection,
        b: Connection,
        c: Connection,
        sum: Option<Output>,
        carry: Option<Output>,
    },
    Half {
        a: Connection,
        b: Connection,
        sum: Option<Output>,
        carry: Option<Output>,
    },
}

impl Node {
    fn full(a: Connection, b: Connection, c: Connection) -> Self {
        Node::Full {
            a,
            b,
            c,
            sum: None,
            carry: None,
        }
    }

    fn half(a: Connection, b: Connection) -> Self {
        Node::Half {
            a,
            b,
            sum: None,
            carry: None,
        }
    }

    fn reserve(&mut self, var_manager: &mut dyn ManageVars) {
        match self {
            Node::Full { sum, carry, .. } | Node::Half { sum, carry, .. } => {
                if sum.is_none() {
                    *sum = Some(Output {
                        bit: var_manager.new_lit(),
                        enc_if: false,
                        enc_only_if: false,
                    });
                }
                if carry.is_none() {
                    *carry = Some(Output {
                        bit: var_manager.new_lit(),
                        enc_if: false,
                        enc_only_if: false,
                    });
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
enum Connection {
    Input(Lit),
    Sum(usize),
    Carry(usize),
}

#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
struct Output {
    bit: Lit,
    enc_if: bool,
    enc_only_if: bool,
}

#[inline]
fn get_bit_if<Col>(
    con: Connection,
    nodes: &mut [Node],
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) -> Result<Lit, OutOfMemory>
where
    Col: CollectClauses,
{
    match con {
        Connection::Input(bit) => Ok(bit),
        Connection::Sum(node) => {
            let nodes = &mut nodes[..=node];
            sum_if(nodes, collector, var_manager)
        }
        Connection::Carry(node) => {
            let nodes = &mut nodes[..=node];
            carry_if(nodes, collector, var_manager)
        }
    }
}

#[inline]
fn get_bit_only_if<Col>(
    con: Connection,
    nodes: &mut [Node],
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) -> Result<Lit, OutOfMemory>
where
    Col: CollectClauses,
{
    match con {
        Connection::Input(bit) => Ok(bit),
        Connection::Sum(node) => {
            let nodes = &mut nodes[..=node];
            sum_only_if(nodes, collector, var_manager)
        }
        Connection::Carry(node) => {
            let nodes = &mut nodes[..=node];
            carry_only_if(nodes, collector, var_manager)
        }
    }
}

/// Encodes the if direction of the sum bit for the last node in `nodes` recursively
fn sum_if<Col>(
    nodes: &mut [Node],
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) -> Result<Lit, OutOfMemory>
where
    Col: CollectClauses,
{
    let (nodes, node) = nodes.split_at_mut(nodes.len() - 1);
    let node = &mut node[0];

    match node {
        Node::Full { a, b, c, sum, .. } => {
            let sum = if let Some(sum) = sum {
                if sum.enc_if {
                    return Ok(sum.bit);
                }
                sum.enc_if = true;
                sum.bit
            } else {
                let bit = var_manager.new_lit();
                *sum = Some(Output {
                    bit,
                    enc_if: true,
                    enc_only_if: false,
                });
                bit
            };

            let a = get_bit_if(*a, nodes, collector, var_manager)?;
            let b = get_bit_if(*b, nodes, collector, var_manager)?;
            let c = get_bit_if(*c, nodes, collector, var_manager)?;

            collector.add_clause(clause![!a, !b, !c, sum])?;
            collector.add_clause(clause![!a, b, c, sum])?;
            collector.add_clause(clause![a, !b, c, sum])?;
            collector.add_clause(clause![a, b, !c, sum])?;

            Ok(sum)
        }
        Node::Half { a, b, sum, .. } => {
            let sum = if let Some(sum) = sum {
                if sum.enc_if {
                    return Ok(sum.bit);
                }
                sum.enc_if = true;
                sum.bit
            } else {
                let bit = var_manager.new_lit();
                *sum = Some(Output {
                    bit,
                    enc_if: true,
                    enc_only_if: false,
                });
                bit
            };

            let a = get_bit_if(*a, nodes, collector, var_manager)?;
            let b = get_bit_if(*b, nodes, collector, var_manager)?;

            collector.add_clause(clause![!a, b, sum])?;
            collector.add_clause(clause![a, !b, sum])?;

            Ok(sum)
        }
    }
}

/// Encodes the only-if direction of the sum bit for the last node in `nodes` recursively
fn sum_only_if<Col>(
    nodes: &mut [Node],
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) -> Result<Lit, OutOfMemory>
where
    Col: CollectClauses,
{
    let (nodes, node) = nodes.split_at_mut(nodes.len() - 1);
    let node = &mut node[0];

    match node {
        Node::Full { a, b, c, sum, .. } => {
            let sum = if let Some(sum) = sum {
                if sum.enc_only_if {
                    return Ok(sum.bit);
                }
                sum.enc_only_if = true;
                sum.bit
            } else {
                let bit = var_manager.new_lit();
                *sum = Some(Output {
                    bit,
                    enc_if: false,
                    enc_only_if: true,
                });
                bit
            };

            let a = get_bit_only_if(*a, nodes, collector, var_manager)?;
            let b = get_bit_only_if(*b, nodes, collector, var_manager)?;
            let c = get_bit_only_if(*c, nodes, collector, var_manager)?;

            collector.add_clause(clause![a, b, c, !sum])?;
            collector.add_clause(clause![a, !b, !c, !sum])?;
            collector.add_clause(clause![!a, b, !c, !sum])?;
            collector.add_clause(clause![!a, !b, c, !sum])?;

            Ok(sum)
        }
        Node::Half { a, b, sum, .. } => {
            let sum = if let Some(sum) = sum {
                if sum.enc_only_if {
                    return Ok(sum.bit);
                }
                sum.enc_only_if = true;
                sum.bit
            } else {
                let bit = var_manager.new_lit();
                *sum = Some(Output {
                    bit,
                    enc_if: false,
                    enc_only_if: true,
                });
                bit
            };

            let a = get_bit_only_if(*a, nodes, collector, var_manager)?;
            let b = get_bit_only_if(*b, nodes, collector, var_manager)?;

            collector.add_clause(clause![a, b, !sum])?;
            collector.add_clause(clause![!a, !b, !sum])?;

            Ok(sum)
        }
    }
}

/// Encodes the if direction of the carry bit for the last node in `nodes` recursively
fn carry_if<Col>(
    nodes: &mut [Node],
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) -> Result<Lit, OutOfMemory>
where
    Col: CollectClauses,
{
    let (nodes, node) = nodes.split_at_mut(nodes.len() - 1);
    let node = &mut node[0];

    match node {
        Node::Full { a, b, c, carry, .. } => {
            let carry = if let Some(carry) = carry {
                if carry.enc_if {
                    return Ok(carry.bit);
                }
                carry.enc_if = true;
                carry.bit
            } else {
                let bit = var_manager.new_lit();
                *carry = Some(Output {
                    bit,
                    enc_if: true,
                    enc_only_if: false,
                });
                bit
            };

            let a = get_bit_if(*a, nodes, collector, var_manager)?;
            let b = get_bit_if(*b, nodes, collector, var_manager)?;
            let c = get_bit_if(*c, nodes, collector, var_manager)?;

            collector.add_clause(clause![!b, !c, carry])?;
            collector.add_clause(clause![!a, !c, carry])?;
            collector.add_clause(clause![!a, !b, carry])?;

            Ok(carry)
        }
        Node::Half { a, b, carry, .. } => {
            let carry = if let Some(carry) = carry {
                if carry.enc_if {
                    return Ok(carry.bit);
                }
                carry.enc_if = true;
                carry.bit
            } else {
                let bit = var_manager.new_lit();
                *carry = Some(Output {
                    bit,
                    enc_if: true,
                    enc_only_if: false,
                });
                bit
            };

            let a = get_bit_if(*a, nodes, collector, var_manager)?;
            let b = get_bit_if(*b, nodes, collector, var_manager)?;

            collector.add_clause(clause![!a, !b, carry])?;

            Ok(carry)
        }
    }
}

/// Encodes the only-if direction of the carry bit for the last node in `nodes` recursively
fn carry_only_if<Col>(
    nodes: &mut [Node],
    collector: &mut Col,
    var_manager: &mut dyn ManageVars,
) -> Result<Lit, OutOfMemory>
where
    Col: CollectClauses,
{
    let (nodes, node) = nodes.split_at_mut(nodes.len() - 1);
    let node = &mut node[0];

    match node {
        Node::Full { a, b, c, carry, .. } => {
            let carry = if let Some(carry) = carry {
                if carry.enc_only_if {
                    return Ok(carry.bit);
                }
                carry.enc_only_if = true;
                carry.bit
            } else {
                let bit = var_manager.new_lit();
                *carry = Some(Output {
                    bit,
                    enc_if: false,
                    enc_only_if: true,
                });
                bit
            };

            let a = get_bit_if(*a, nodes, collector, var_manager)?;
            let b = get_bit_if(*b, nodes, collector, var_manager)?;
            let c = get_bit_if(*c, nodes, collector, var_manager)?;

            collector.add_clause(clause![b, c, !carry])?;
            collector.add_clause(clause![a, c, !carry])?;
            collector.add_clause(clause![a, b, !carry])?;

            Ok(carry)
        }
        Node::Half { a, b, carry, .. } => {
            let carry = if let Some(carry) = carry {
                if carry.enc_only_if {
                    return Ok(carry.bit);
                }
                carry.enc_if = true;
                carry.bit
            } else {
                let bit = var_manager.new_lit();
                *carry = Some(Output {
                    bit,
                    enc_if: true,
                    enc_only_if: false,
                });
                bit
            };

            let a = get_bit_if(*a, nodes, collector, var_manager)?;
            let b = get_bit_if(*b, nodes, collector, var_manager)?;

            collector.add_clause(clause![a, !carry])?;
            collector.add_clause(clause![b, !carry])?;

            Ok(carry)
        }
    }
}

/// Reserves the variables for the last node in `nodes` recursively
fn reserve(nodes: &mut [Node], var_manager: &mut dyn ManageVars) {
    let (nodes, node) = nodes.split_at_mut(nodes.len());

    let node = &mut node[0];
    node.reserve(var_manager);

    let mut recurse = |con: Connection| match con {
        Connection::Input(_) => {}
        Connection::Sum(node) | Connection::Carry(node) => {
            reserve(&mut nodes[..=node], var_manager);
        }
    };

    match node {
        Node::Full { a, b, c, .. } => {
            recurse(*a);
            recurse(*b);
            recurse(*c);
        }
        Node::Half { a, b, .. } => {
            recurse(*a);
            recurse(*b);
        }
    }
}

fn comparator_if<Col>(
    rhs: usize,
    output: Lit,
    lhs: &[Option<Lit>],
    collector: &mut Col,
) -> Result<(), OutOfMemory>
where
    Col: CollectClauses,
{
    debug_assert!(rhs < (1usize << lhs.len()));

    let y = |idx: usize| -> bool { rhs & (1usize << idx) != 0 };

    let comp_clause = |i: usize| -> Option<Clause> {
        if y(i) {
            return None;
        }

        let mut cl = clause![];

        let lhs_i = lhs[i]?;
        cl.add(!lhs_i);

        #[allow(clippy::needless_range_loop)]
        for j in i + 1..lhs.len() {
            if y(j) {
                let lhs_j = lhs[j]?;
                cl.add(!lhs_j);
            } else if let Some(lhs_j) = lhs[j] {
                cl.add(lhs_j);
            }
        }

        cl.add(output);

        Some(cl)
    };

    collector.extend_clauses((0..lhs.len()).filter_map(comp_clause))
}

fn comparator_only_if<Col>(
    rhs: usize,
    output: Lit,
    lhs: &[Option<Lit>],
    collector: &mut Col,
) -> Result<(), OutOfMemory>
where
    Col: CollectClauses,
{
    debug_assert!(rhs < (1usize << lhs.len()));

    if rhs == (1usize << lhs.len()) - 1 {
        return collector.add_clause(clause![!output]);
    }

    let rhs = rhs + 1;

    let y = |idx: usize| -> bool { rhs & (1usize << idx) != 0 };

    let comp_clause = |i: usize| -> Option<Clause> {
        if !y(i) {
            return None;
        }

        let mut cl = clause![];

        if let Some(lhs_i) = lhs[i] {
            cl.add(lhs_i);
        }

        #[allow(clippy::needless_range_loop)]
        for j in i + 1..lhs.len() {
            if y(j) {
                let lhs_j = lhs[j]?;
                cl.add(!lhs_j);
            } else if let Some(lhs_j) = lhs[j] {
                cl.add(lhs_j);
            }
        }

        cl.add(!output);

        Some(cl)
    };

    collector.extend_clauses((0..lhs.len()).filter_map(comp_clause))
}

#[cfg(test)]
mod tests {
    use crate::{
        encodings::pb::{BoundLower, BoundUpper},
        instances::{BasicVarManager, Cnf, ManageVars},
        lit,
        types::{Assignment, Lit, TernaryVal},
        var,
    };

    const N: u32 = 4;

    const ALL_LITS: [Option<Lit>; N as usize] =
        [Some(lit![0]), Some(lit![1]), Some(lit![2]), Some(lit![3])];
    const SOME_LITS: [Option<Lit>; N as usize] =
        [Some(lit![0]), None, Some(lit![2]), Some(lit![3])];
    const LESS_LITS: [Option<Lit>; N as usize] = [Some(lit![0]), None, None, Some(lit![3])];

    fn make_assignment(val: usize) -> Assignment {
        let mut assign = Assignment::default();
        for idx in 0..=N {
            assign.assign_var(var![idx], TernaryVal::from(val & (1usize << idx) != 0));
        }
        assign
    }

    fn value(lits: &[Option<Lit>], assign: &Assignment) -> usize {
        let mut val = 0;
        for (idx, lit) in lits.iter().enumerate() {
            if lit.is_some_and(|lit| assign.lit_value(lit) == TernaryVal::True) {
                val += 1usize << idx;
            }
        }
        val
    }

    fn comparator_if(output: Lit, lits: &[Option<Lit>]) {
        for rhs in 0..(1usize << N) {
            let mut cnf = Cnf::new();
            super::comparator_if(rhs, output, lits, &mut cnf).unwrap();
            dbg!(&cnf);
            for assign in 0..(1usize << (N + 1)) {
                let assign = make_assignment(assign);
                let lhs = value(lits, &assign);
                dbg!(lhs, rhs, assign.lit_value(output));
                if assign.lit_value(output) == TernaryVal::True || lhs <= rhs {
                    assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
                } else {
                    assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
                }
            }
        }
    }

    #[test]
    fn comparator_if_all() {
        let output = lit![N];
        comparator_if(output, &ALL_LITS);
    }

    #[test]
    fn comparator_if_some() {
        let output = lit![N];
        comparator_if(output, &SOME_LITS);
    }

    #[test]
    fn comparator_if_less() {
        let output = lit![N];
        comparator_if(output, &LESS_LITS);
    }

    fn comparator_only_if(output: Lit, lits: &[Option<Lit>]) {
        for rhs in 0..(1usize << N) {
            let mut cnf = Cnf::new();
            super::comparator_only_if(rhs, output, lits, &mut cnf).unwrap();
            dbg!(&cnf);
            for assign in 0..(1usize << (N + 1)) {
                let assign = make_assignment(assign);
                let lhs = value(lits, &assign);
                dbg!(lhs, rhs, assign.lit_value(output));
                if assign.lit_value(output) == TernaryVal::False || lhs > rhs {
                    assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
                } else {
                    assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
                }
            }
        }
    }

    #[test]
    fn comparator_only_if_all() {
        let output = lit![N];
        comparator_only_if(output, &ALL_LITS);
    }

    #[test]
    fn comparator_only_if_some() {
        let output = lit![N];
        comparator_only_if(output, &SOME_LITS);
    }

    #[test]
    fn comparator_only_if_less() {
        let output = lit![N];
        comparator_only_if(output, &LESS_LITS);
    }

    fn comparator_if_and_only_if(output: Lit, lits: &[Option<Lit>]) {
        for rhs in 0..(1usize << N) {
            let mut cnf = Cnf::new();
            super::comparator_if(rhs, output, lits, &mut cnf).unwrap();
            super::comparator_only_if(rhs, output, lits, &mut cnf).unwrap();
            dbg!(&cnf);
            for assign in 0..(1usize << (N + 1)) {
                let assign = make_assignment(assign);
                let lhs = value(lits, &assign);
                dbg!(lhs, rhs, assign.lit_value(output));
                if lhs <= rhs {
                    assert_eq!(cnf.evaluate(&assign), !assign.lit_value(output));
                } else {
                    assert_eq!(cnf.evaluate(&assign), assign.lit_value(output));
                }
            }
        }
    }

    #[test]
    fn comparator_if_and_only_if_all() {
        let output = lit![N];
        comparator_if_and_only_if(output, &ALL_LITS);
    }

    #[test]
    fn comparator_if_and_only_if_some() {
        let output = lit![N];
        comparator_if_and_only_if(output, &SOME_LITS);
    }

    #[test]
    fn comparator_if_and_only_if_less() {
        let output = lit![N];
        comparator_if_and_only_if(output, &LESS_LITS);
    }

    #[test]
    fn full_adder_sum_if() {
        let mut nodes = vec![super::Node::Full {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            c: super::Connection::Input(lit![2]),
            sum: Some(super::Output {
                bit: lit![3],
                enc_if: false,
                enc_only_if: false,
            }),
            carry: None,
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        super::sum_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 4) {
            let val = (assign & 0b111).count_ones();
            dbg!(val);
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![3]) == TernaryVal::False) && ((val & 0b1) != 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            }
        }
    }

    #[test]
    fn full_adder_sum_only_if() {
        let mut nodes = vec![super::Node::Full {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            c: super::Connection::Input(lit![2]),
            sum: Some(super::Output {
                bit: lit![3],
                enc_if: false,
                enc_only_if: false,
            }),
            carry: None,
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        super::sum_only_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 4) {
            let val = (assign & 0b111).count_ones();
            dbg!(val);
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![3]) == TernaryVal::True) && ((val & 0b1) == 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            }
        }
    }

    #[test]
    fn full_adder_sum_if_and_only_if() {
        let mut nodes = vec![super::Node::Full {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            c: super::Connection::Input(lit![2]),
            sum: Some(super::Output {
                bit: lit![3],
                enc_if: false,
                enc_only_if: false,
            }),
            carry: None,
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        super::sum_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        super::sum_only_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 4) {
            let val = (assign & 0b111).count_ones();
            dbg!(val);
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![3]) == TernaryVal::True) == ((val & 0b1) != 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            }
        }
    }

    #[test]
    fn full_adder_carry_if() {
        let mut nodes = vec![super::Node::Full {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            c: super::Connection::Input(lit![2]),
            sum: None,
            carry: Some(super::Output {
                bit: lit![3],
                enc_if: false,
                enc_only_if: false,
            }),
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        super::carry_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 4) {
            let val = (assign & 0b111).count_ones();
            dbg!(val);
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![3]) == TernaryVal::False) && ((val & 0b10) != 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            }
        }
    }

    #[test]
    fn full_adder_carry_only_if() {
        let mut nodes = vec![super::Node::Full {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            c: super::Connection::Input(lit![2]),
            sum: None,
            carry: Some(super::Output {
                bit: lit![3],
                enc_if: false,
                enc_only_if: false,
            }),
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        super::carry_only_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 4) {
            let val = (assign & 0b111).count_ones();
            dbg!(val);
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![3]) == TernaryVal::True) && ((val & 0b10) == 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            }
        }
    }

    #[test]
    fn full_adder_carry_if_and_only_if() {
        let mut nodes = vec![super::Node::Full {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            c: super::Connection::Input(lit![2]),
            sum: None,
            carry: Some(super::Output {
                bit: lit![3],
                enc_if: false,
                enc_only_if: false,
            }),
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        super::carry_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        super::carry_only_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 4) {
            let val = (assign & 0b111).count_ones();
            dbg!(val);
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![3]) == TernaryVal::True) == ((val & 0b10) != 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            }
        }
    }

    #[test]
    fn half_adder_sum_if() {
        let mut nodes = vec![super::Node::Half {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            sum: Some(super::Output {
                bit: lit![2],
                enc_if: false,
                enc_only_if: false,
            }),
            carry: None,
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![3]);
        super::sum_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 3) {
            let val = (assign & 0b11).count_ones();
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![2]) == TernaryVal::False) && ((val & 0b1) != 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            }
        }
    }

    #[test]
    fn half_adder_sum_only_if() {
        let mut nodes = vec![super::Node::Half {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            sum: Some(super::Output {
                bit: lit![2],
                enc_if: false,
                enc_only_if: false,
            }),
            carry: None,
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![3]);
        super::sum_only_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 3) {
            let val = (assign & 0b11).count_ones();
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![2]) == TernaryVal::True) && ((val & 0b1) == 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            }
        }
    }

    #[test]
    fn half_adder_sum_if_and_only_if() {
        let mut nodes = vec![super::Node::Half {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            sum: Some(super::Output {
                bit: lit![2],
                enc_if: false,
                enc_only_if: false,
            }),
            carry: None,
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![3]);
        super::sum_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        super::sum_only_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 3) {
            let val = (assign & 0b11).count_ones();
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![2]) == TernaryVal::True) == ((val & 0b1) != 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            }
        }
    }

    #[test]
    fn half_adder_carry_if() {
        let mut nodes = vec![super::Node::Half {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            sum: None,
            carry: Some(super::Output {
                bit: lit![2],
                enc_if: false,
                enc_only_if: false,
            }),
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![3]);
        super::carry_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 3) {
            let val = (assign & 0b11).count_ones();
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![2]) == TernaryVal::False) && ((val & 0b10) != 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            }
        }
    }

    #[test]
    fn half_adder_carry_only_if() {
        let mut nodes = vec![super::Node::Half {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            sum: None,
            carry: Some(super::Output {
                bit: lit![2],
                enc_if: false,
                enc_only_if: false,
            }),
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![3]);
        super::carry_only_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 3) {
            let val = (assign & 0b11).count_ones();
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![2]) == TernaryVal::True) && ((val & 0b10) == 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            }
        }
    }

    #[test]
    fn half_adder_carry_if_and_only_if() {
        let mut nodes = vec![super::Node::Half {
            a: super::Connection::Input(lit![0]),
            b: super::Connection::Input(lit![1]),
            sum: None,
            carry: Some(super::Output {
                bit: lit![2],
                enc_if: false,
                enc_only_if: false,
            }),
        }];
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![3]);
        super::carry_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        super::carry_only_if(&mut nodes, &mut cnf, &mut vm).unwrap();
        dbg!(&cnf);
        for assign in 0..(1usize << 3) {
            let val = (assign & 0b11).count_ones();
            let assign = make_assignment(assign);
            dbg!(&assign);
            if (assign.lit_value(lit![2]) == TernaryVal::True) == ((val & 0b10) != 0) {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::True);
            } else {
                assert_eq!(cnf.evaluate(&assign), TernaryVal::False);
            }
        }
    }

    #[test]
    fn basic_ub() {
        let mut adder: super::BinaryAdder =
            [(lit![0], 1), (lit![1], 2), (lit![2], 3), (lit![3], 4)]
                .into_iter()
                .collect();
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        adder.encode_ub(0..=6, &mut cnf, &mut vm).unwrap();
        assert_eq!(vm.n_used(), 17);
        assert_eq!(cnf.len(), 32);
    }

    #[test]
    fn basic_lb() {
        let mut adder: super::BinaryAdder =
            [(lit![0], 1), (lit![1], 2), (lit![2], 3), (lit![3], 4)]
                .into_iter()
                .collect();
        let mut cnf = Cnf::new();
        let mut vm = BasicVarManager::from_next_free(var![4]);
        adder.encode_lb(0..=6, &mut cnf, &mut vm).unwrap();
        assert_eq!(vm.n_used(), 16);
        assert_eq!(cnf.len(), 27);
    }
}
