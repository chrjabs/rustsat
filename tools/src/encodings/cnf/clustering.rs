//! # Constrained Correlation Clustering
//!
//! Constrained correlation clustering encodings following \[1\].
//!
//! ## References
//!
//! - \[1\] Jeremias Berg and Matti Järvisalo: _Cost-optimal constrained
//!     correlation clustering via weighted partial Maximum Satisfiability_, AIJ
//!     2017.

use std::io;

use nom::{
    branch::alt,
    character::complete::{alphanumeric1, char, multispace1},
    combinator::{map, recognize},
    multi::many1,
    number::complete::double,
    sequence::{terminated, tuple},
};
use rustsat::{
    clause,
    instances::{fio::dimacs, ManageVars},
    types::{RsHashMap, Var},
    utils,
};

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
enum VarId {
    /// `b i k`
    Binary(u32, u32),
    /// `EQ i j k`
    Eq(u32, u32, u32),
    /// `S i j`
    Same(u32, u32),
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct VarManager {
    next_var: Var,
    vars: RsHashMap<VarId, Var>,
}

impl VarManager {
    fn id(&mut self, id: VarId) -> Var {
        if let Some(var) = self.vars.get(&id) {
            return *var;
        }
        let var = self.new_var();
        self.vars.insert(id, var);
        var
    }
}

impl ManageVars for VarManager {
    fn new_var(&mut self) -> Var {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    fn max_var(&self) -> Option<Var> {
        if self.next_var == Var::new(0) {
            None
        } else {
            Some(self.next_var - 1)
        }
    }

    fn increase_next_free(&mut self, v: Var) -> bool {
        if v > self.next_var {
            self.next_var = v;
            return true;
        };
        false
    }

    fn combine(&mut self, other: Self) {
        if other.next_var > self.next_var {
            self.next_var = other.next_var;
        };
    }

    fn n_used(&self) -> u32 {
        self.next_var.idx32()
    }

    fn forget_from(&mut self, min_var: Var) {
        if min_var < self.next_var {
            self.vars.retain(|_, var| *var < min_var);
            self.next_var = min_var;
        }
    }
}

impl Default for VarManager {
    fn default() -> Self {
        Self {
            next_var: Var::new(0),
            vars: Default::default(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Similarity {
    Similar(usize),
    DisSimilar(usize),
    DontCare,
    MustLink,
    CannotLink,
}

enum Clause {
    /// `EQUALITY i j k 0..3`
    Eq(u32, u32, u32, u8),
    /// `SameCluster i j 0..a`
    Same(u32, u32, u32),
    /// `ML i j 0..2a`
    MustLink(u32, u32, u32),
    /// `CL i j`
    CannotLink(u32, u32),
    /// `S i j`
    Similar(u32, u32),
    /// `-S i j`
    DisSimilar(u32, u32),
}

pub struct Encoding {
    similarities: Vec<Similarity>,
    n: u32,
    a: u32,
    var_manager: VarManager,
    next_clause: Clause,
}

impl Encoding {
    pub fn new<R: io::BufRead, Map: Fn(f64) -> Similarity>(
        in_reader: R,
        sim_map: Map,
    ) -> anyhow::Result<Self> {
        let mut ident_map = RsHashMap::default();
        let mut next_idx: u32 = 0;
        let process_line =
            |line: Result<String, io::Error>| -> Option<anyhow::Result<(String, String, f64)>> {
                let line = line.ok()?;
                let line = line.trim_start();
                if line.starts_with('%') {
                    return None;
                }
                let (_, tup) = tuple((
                    terminated(ident, multispace1),
                    terminated(ident, multispace1),
                    double,
                ))(line)
                .ok()?;
                if !ident_map.contains_key(&tup.0) {
                    ident_map.insert(tup.0.clone(), next_idx);
                    next_idx += 1;
                }
                if !ident_map.contains_key(&tup.1) {
                    ident_map.insert(tup.1.clone(), next_idx);
                    next_idx += 1;
                }
                Some(Ok(tup))
            };
        let pairwise = in_reader
            .lines()
            .filter_map(process_line)
            .collect::<Result<Vec<_>, _>>()?;
        let n = ident_map.len() as u32;

        let mut similarities = Vec::new();
        similarities.resize(Self::sim_idx(n - 2, n - 1, n) + 1, Similarity::DontCare);
        for (ident1, ident2, sim) in pairwise {
            let mut idx1 = *ident_map.get(&ident1).unwrap();
            let mut idx2 = *ident_map.get(&ident2).unwrap();
            if idx1 == idx2 {
                if sim_map(sim) != Similarity::MustLink {
                    eprintln!(
                        "warning: self-similarity for {} is {} (mapped to {:?})",
                        ident1,
                        sim,
                        sim_map(sim)
                    )
                }
                continue;
            }
            if idx2 < idx1 {
                std::mem::swap(&mut idx1, &mut idx2);
            }
            similarities[Self::sim_idx(idx1, idx2, n)] = sim_map(sim);
        }

        let a = utils::digits(ident_map.len(), 2);

        Ok(Self {
            similarities,
            n,
            a,
            var_manager: Default::default(),
            next_clause: Clause::Eq(0, 1, 0, 0),
        })
    }

    /// Note: the the first index must be smaller than the second
    #[inline]
    fn sim_idx(idx1: u32, idx2: u32, n_idents: u32) -> usize {
        // indexing an upper triangular matrix compactly in a vec
        // https://stackoverflow.com/questions/27086195/linear-index-upper-triangular-matrix
        let idx1 = idx1 as usize;
        let idx2 = idx2 as usize;
        let n_idents = n_idents as usize;
        n_idents * (n_idents - 1) / 2 - (n_idents - idx1) * ((n_idents - idx1) - 1) / 2 + idx2
            - idx1
            - 1
    }
}

impl Iterator for Encoding {
    type Item = dimacs::McnfLine;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.next_clause {
                Clause::Eq(idx1, idx2, k, cidx) => {
                    if idx1 >= self.n - 1 {
                        self.next_clause = Clause::Same(0, 1, 0);
                        continue;
                    }
                    if idx2 >= self.n {
                        self.next_clause = Clause::Eq(idx1 + 1, idx1 + 2, 0, 0);
                        continue;
                    }
                    if k >= self.a {
                        self.next_clause = Clause::Eq(idx1, idx2 + 1, 0, 0);
                        continue;
                    }
                    if cidx >= 4 {
                        self.next_clause = Clause::Eq(idx1, idx2, k + 1, 0);
                        continue;
                    }
                    if matches!(
                        self.similarities[Self::sim_idx(idx1, idx2, self.n)],
                        Similarity::DontCare | Similarity::MustLink
                    ) {
                        // Don't need equality vars for don't cares and must links
                        self.next_clause = Clause::Eq(idx1, idx2 + 1, 0, 0);
                        continue;
                    }
                    self.next_clause = Clause::Eq(idx1, idx2, k, cidx + 1);
                    let b1 = self.var_manager.id(VarId::Binary(idx1, k)).pos_lit();
                    let b2 = self.var_manager.id(VarId::Binary(idx2, k)).pos_lit();
                    let eql = self.var_manager.id(VarId::Eq(idx1, idx2, k)).pos_lit();
                    return Some(dimacs::McnfLine::Hard(match cidx {
                        0 => clause![eql, b1, b2],
                        1 => clause![eql, !b1, !b2],
                        2 => clause![!eql, !b1, b2],
                        3 => clause![!eql, b1, !b2],
                        _ => panic!(),
                    }));
                }
                Clause::Same(idx1, idx2, cidx) => {
                    if idx1 >= self.n - 1 {
                        self.next_clause = Clause::MustLink(0, 1, 0);
                        continue;
                    }
                    if idx2 >= self.n {
                        self.next_clause = Clause::Same(idx1 + 1, idx1 + 2, 0);
                        continue;
                    }
                    if cidx > self.a {
                        self.next_clause = Clause::Same(idx1, idx2 + 1, 0);
                        continue;
                    }
                    if matches!(
                        self.similarities[Self::sim_idx(idx1, idx2, self.n)],
                        Similarity::DontCare | Similarity::MustLink | Similarity::CannotLink
                    ) {
                        // Don't need same cluster vars for don't cares, must links, and cannot links
                        self.next_clause = Clause::Same(idx1, idx2 + 1, 0);
                        continue;
                    }
                    self.next_clause = Clause::Same(idx1, idx2, cidx + 1);
                    let sl = self.var_manager.id(VarId::Same(idx1, idx2)).pos_lit();
                    return Some(dimacs::McnfLine::Hard(match cidx {
                        cidx if cidx < self.a => {
                            let eql = self.var_manager.id(VarId::Eq(idx1, idx2, cidx)).pos_lit();
                            clause![!sl, eql]
                        }
                        _ => {
                            let mut cl: rustsat::types::constraints::Clause = (0..self.a)
                                .map(|k| self.var_manager.id(VarId::Eq(idx1, idx2, k)).neg_lit())
                                .collect();
                            cl.add(sl);
                            cl
                        }
                    }));
                }
                Clause::MustLink(idx1, idx2, cidx) => {
                    if idx1 >= self.n - 1 {
                        self.next_clause = Clause::CannotLink(0, 1);
                        continue;
                    }
                    if idx2 >= self.n {
                        self.next_clause = Clause::MustLink(idx1 + 1, idx1 + 2, 0);
                        continue;
                    }
                    if cidx >= 2 * self.a {
                        self.next_clause = Clause::MustLink(idx1, idx2 + 1, 0);
                        continue;
                    }
                    if !matches!(
                        self.similarities[Self::sim_idx(idx1, idx2, self.n)],
                        Similarity::MustLink
                    ) {
                        // Only need must link clauses for must links
                        self.next_clause = Clause::MustLink(idx1, idx2 + 1, 0);
                        continue;
                    }
                    self.next_clause = Clause::MustLink(idx1, idx2, cidx + 1);
                    let b1 = self.var_manager.id(VarId::Binary(idx1, cidx / 2)).pos_lit();
                    let b2 = self.var_manager.id(VarId::Binary(idx2, cidx / 2)).pos_lit();
                    return Some(dimacs::McnfLine::Hard(if cidx % 2 == 0 {
                        clause![!b1, b2]
                    } else {
                        clause![b1, !b2]
                    }));
                }
                Clause::CannotLink(idx1, idx2) => {
                    if idx1 >= self.n - 1 {
                        self.next_clause = Clause::Similar(0, 1);
                        continue;
                    }
                    if idx2 >= self.n {
                        self.next_clause = Clause::CannotLink(idx1 + 1, idx1 + 2);
                        continue;
                    }
                    if !matches!(
                        self.similarities[Self::sim_idx(idx1, idx2, self.n)],
                        Similarity::CannotLink
                    ) {
                        // Only need cannot link clauses for cannot links
                        self.next_clause = Clause::CannotLink(idx1, idx2 + 1);
                        continue;
                    }
                    self.next_clause = Clause::CannotLink(idx1, idx2 + 1);
                    return Some(dimacs::McnfLine::Hard(
                        (0..self.a)
                            .map(|k| self.var_manager.id(VarId::Eq(idx1, idx2, k)).neg_lit())
                            .collect(),
                    ));
                }
                Clause::Similar(idx1, idx2) => {
                    if idx1 >= self.n - 1 {
                        self.next_clause = Clause::DisSimilar(0, 1);
                        continue;
                    }
                    if idx2 >= self.n {
                        self.next_clause = Clause::Similar(idx1 + 1, idx1 + 2);
                        continue;
                    }
                    self.next_clause = Clause::Similar(idx1, idx2 + 1);
                    if let Similarity::Similar(weight) =
                        self.similarities[Self::sim_idx(idx1, idx2, self.n)]
                    {
                        return Some(dimacs::McnfLine::Soft(
                            clause![self.var_manager.id(VarId::Same(idx1, idx2)).pos_lit()],
                            weight,
                            0,
                        ));
                    }
                }
                Clause::DisSimilar(idx1, idx2) => {
                    if idx1 >= self.n - 1 {
                        return None;
                    }
                    if idx2 >= self.n {
                        self.next_clause = Clause::DisSimilar(idx1 + 1, idx1 + 2);
                        continue;
                    }
                    self.next_clause = Clause::DisSimilar(idx1, idx2 + 1);
                    if let Similarity::DisSimilar(weight) =
                        self.similarities[Self::sim_idx(idx1, idx2, self.n)]
                    {
                        return Some(dimacs::McnfLine::Soft(
                            clause![!self.var_manager.id(VarId::Same(idx1, idx2)).pos_lit()],
                            weight,
                            1,
                        ));
                    }
                }
            }
        }
    }
}

fn ident(input: &str) -> nom::IResult<&str, String> {
    map(
        recognize(many1(alt((alphanumeric1, recognize(char('_')))))),
        String::from,
    )(input)
}

pub fn scaling_map(sim: f64, multiplier: u32) -> isize {
    (sim * (multiplier as f64)).trunc() as isize
}

pub fn saturating_map(sim: isize, dont_care: usize, hard_thr: usize) -> Similarity {
    match sim.unsigned_abs() {
        asim if asim < dont_care => Similarity::DontCare,
        asim if asim > hard_thr => {
            if sim > 0 {
                Similarity::MustLink
            } else {
                Similarity::CannotLink
            }
        }
        _ => {
            if sim > 0 {
                Similarity::Similar(sim as usize)
            } else {
                Similarity::DisSimilar(-sim as usize)
            }
        }
    }
}
