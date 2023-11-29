//! # Multi-Objective Optimization Instance Representations

use std::{io, path::Path};

use crate::{
    encodings::{card, pb},
    types::{
        constraints::{CardConstraint, PBConstraint},
        Assignment, Var, WClsIter, WLitIter,
    },
};

use super::{
    fio::{self, dimacs::McnfLine},
    BasicVarManager, Cnf, ManageVars, Objective, ReindexVars, SatInstance,
};

/// Type representing a multi-objective optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct MultiOptInstance<VM: ManageVars = BasicVarManager> {
    pub(super) constrs: SatInstance<VM>,
    pub(super) objs: Vec<Objective>,
}

impl<VM: ManageVars> MultiOptInstance<VM> {
    /// Creates a new optimization instance with a specific var manager
    pub fn new_with_manager(n_objs: usize, var_manager: VM) -> Self {
        MultiOptInstance {
            constrs: SatInstance::new_with_manager(var_manager),
            objs: {
                let mut tmp = Vec::with_capacity(n_objs);
                tmp.resize(n_objs, Objective::new());
                tmp
            },
        }
    }

    /// Creates a new optimization instance from constraints and objectives
    pub fn compose(mut constraints: SatInstance<VM>, objectives: Vec<Objective>) -> Self {
        objectives.iter().for_each(|o| {
            if let Some(mv) = o.max_var() {
                constraints.var_manager().increase_next_free(mv + 1);
            }
        });
        MultiOptInstance {
            constrs: constraints,
            objs: objectives,
        }
    }

    /// Decomposes the optimization instance to a [`SatInstance`] and [`Objective`]s
    pub fn decompose(mut self) -> (SatInstance<VM>, Vec<Objective>) {
        let omv = self.objs.iter().fold(Var::new(0), |v, o| {
            if let Some(mv) = o.max_var() {
                return std::cmp::max(v, mv);
            }
            v
        });
        self.constrs.var_manager.increase_next_free(omv + 1);
        (self.constrs, self.objs)
    }

    /// Returns the number of objectives in the instance
    pub fn n_objectives(&self) -> usize {
        self.objs.len()
    }

    /// Gets a mutable reference to the hard constraints for modifying them
    pub fn get_constraints(&mut self) -> &mut SatInstance<VM> {
        &mut self.constrs
    }

    /// Gets a mutable reference to the first objective for modifying it.
    /// Make sure `obj_idx` does not exceed the number of objectives in the instance.
    pub fn get_objective(&mut self, obj_idx: usize) -> &mut Objective {
        assert!(obj_idx < self.objs.len());
        &mut self.objs[obj_idx]
    }

    /// Returns an iterator over references to the objectives
    pub fn iter_obj(&self) -> impl Iterator<Item = &Objective> {
        self.objs.iter()
    }

    /// Returns an iterator over mutable references to the objectives
    pub fn iter_obj_mut(&mut self) -> impl Iterator<Item = &mut Objective> {
        self.objs.iter_mut()
    }

    /// Converts the instance to a set of hard and soft clauses
    pub fn as_hard_cls_soft_cls(self) -> (Cnf, Vec<(impl WClsIter, isize)>, VM) {
        let (cnf, mut vm) = self.constrs.as_cnf();
        let omv = self.objs.iter().fold(Var::new(0), |v, o| {
            if let Some(mv) = o.max_var() {
                return std::cmp::max(v, mv);
            }
            v
        });
        vm.increase_next_free(omv + 1);
        let soft_cls = self.objs.into_iter().map(|o| o.as_soft_cls()).collect();
        (cnf, soft_cls, vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals
    pub fn as_hard_cls_soft_lits(self) -> (Cnf, Vec<(impl WLitIter, isize)>, VM) {
        let (mut cnf, mut vm) = self.constrs.as_cnf();
        let omv = self.objs.iter().fold(Var::new(0), |v, o| {
            if let Some(mv) = o.max_var() {
                return std::cmp::max(v, mv);
            }
            v
        });
        vm.increase_next_free(omv);
        let soft_lits = self
            .objs
            .into_iter()
            .map(|o| {
                let (hards, softs) = o.as_soft_lits(&mut vm);
                cnf.extend(hards);
                softs
            })
            .collect();
        (cnf, soft_lits, vm)
    }

    /// Converts the included variable manager to a different type
    pub fn change_var_manager<VM2, VMC>(self, vm_converter: VMC) -> (MultiOptInstance<VM2>, VM)
    where
        VM2: ManageVars + Default,
        VMC: Fn(&VM) -> VM2,
    {
        let (constrs, vm) = self.constrs.change_var_manager(vm_converter);
        (
            MultiOptInstance {
                constrs,
                objs: self.objs,
            },
            vm,
        )
    }

    /// Reindexes all variables in the instance with a reindexing variable manager
    pub fn reindex<R: ReindexVars>(self, mut reindexer: R) -> MultiOptInstance<R> {
        let objs = self
            .objs
            .into_iter()
            .map(|o| o.reindex(&mut reindexer))
            .collect();
        let constrs = self.constrs.reindex(reindexer);
        MultiOptInstance { constrs, objs }
    }

    #[cfg(feature = "rand")]
    /// Randomly shuffles the order of constraints and the objective
    pub fn shuffle(mut self) -> Self {
        self.constrs = self.constrs.shuffle();
        self.objs = self.objs.into_iter().map(|o| o.shuffle()).collect();
        self
    }

    /// Writes the instance to a DIMACS MCNF file at a path
    pub fn to_dimacs_path<P: AsRef<Path>>(self, path: P) -> Result<(), io::Error> {
        let mut writer = fio::open_compressed_uncompressed_write(path)?;
        self.to_dimacs(&mut writer)
    }

    /// Write to DIMACS MCNF
    pub fn to_dimacs<W: io::Write>(self, writer: &mut W) -> Result<(), io::Error> {
        self.to_dimacs_with_encoders(
            card::default_encode_cardinality_constraint,
            pb::default_encode_pb_constraint,
            writer,
        )
    }

    /// Writes the instance to DIMACS MCNF converting non-clausal constraints
    /// with specific encoders.
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
        let soft_cls = self.objs.into_iter().map(|o| o.as_soft_cls()).collect();
        fio::dimacs::write_mcnf_annotated(writer, cnf, soft_cls, vm.max_var())
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
        fio::opb::write_multi_opt::<W, VM>(writer, self, opts)
    }

    /// Calculates the objective values of an assignment. Returns [`None`] if the
    /// assignment is not a solution.
    pub fn cost(&self, assign: &Assignment) -> Option<Vec<isize>> {
        if !self.constrs.is_sat(assign) {
            return None;
        }
        Some(self.objs.iter().map(|o| o.evaluate(assign)).collect())
    }
}

impl<VM: ManageVars + Default> MultiOptInstance<VM> {
    /// Creates a new optimization instance
    pub fn new(n_objs: usize) -> Self {
        MultiOptInstance {
            constrs: SatInstance::new(),
            objs: {
                let mut tmp = Vec::with_capacity(n_objs);
                tmp.resize(n_objs, Objective::new());
                tmp
            },
        }
    }

    /// Parse a DIMACS instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this reader is an extension of the [new
    /// DIMACS WCNF
    /// format](https://maxsat-evaluations.github.io/2022/rules.html#input) to
    /// multiple objectives, which we call DIMACS MCNF. An example of this file
    /// format is the following:
    ///
    /// ```text
    /// c <comment>
    /// h 1 2 3 0
    /// o1 5 1 0
    /// o2 7 2 3 0
    /// ```
    ///
    /// Comments start with `c`, as in other DIMACS formats. Hard clauses start
    /// with an `h`, as in WCNF files. Soft clauses are of the following form
    /// `o<obj idx> <weight> <lit 1> ... <lit n> 0`. The first token must be a
    /// positive number preceded by an 'o', indicating what objective this soft
    /// clause belongs to. After that, the format is identical to a soft clause
    /// in a WCNF file.
    pub fn from_dimacs<R: io::Read>(reader: R) -> Result<Self, fio::ParsingError> {
        Ok(fio::dimacs::parse_mcnf(reader)?)
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`OptInstance::from_dimacs`](super::OptInstance::from_dimacs).
    pub fn from_dimacs_path<P: AsRef<Path>>(path: P) -> Result<Self, fio::ParsingError> {
        match fio::open_compressed_uncompressed_read(path) {
            Err(why) => Err(fio::ParsingError::IO(why)),
            Ok(reader) => MultiOptInstance::from_dimacs(reader),
        }
    }

    /// Parses an OPB instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the OPB format for
    /// pseudo-boolean optimization instances with multiple objectives defined.
    /// For details on the file format see
    /// [here](https://www.cril.univ-artois.fr/PB12/format.pdf).
    pub fn from_opb<R: io::Read>(
        reader: R,
        opts: fio::opb::Options,
    ) -> Result<Self, fio::ParsingError> {
        Ok(fio::opb::parse_multi_opt(reader, opts)?)
    }

    /// Parses an OPB instance from a file path. For more details see
    /// [`MultiOptInstance::from_opb`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    pub fn from_opb_path<P: AsRef<Path>>(
        path: P,
        opts: fio::opb::Options,
    ) -> Result<Self, fio::ParsingError> {
        match fio::open_compressed_uncompressed_read(path) {
            Err(why) => Err(fio::ParsingError::IO(why)),
            Ok(reader) => MultiOptInstance::from_opb(reader, opts),
        }
    }
}

impl<VM: ManageVars + Default> FromIterator<McnfLine> for MultiOptInstance<VM> {
    fn from_iter<T: IntoIterator<Item = McnfLine>>(iter: T) -> Self {
        let mut inst = Self::default();
        for line in iter {
            match line {
                McnfLine::Comment(_) => (),
                McnfLine::Hard(cl) => inst.get_constraints().add_clause(cl),
                McnfLine::Soft(cl, w, oidx) => {
                    if oidx >= inst.objs.len() {
                        inst.objs.resize(oidx + 1, Default::default())
                    }
                    inst.get_objective(oidx).add_soft_clause(w, cl);
                }
            }
        }
        inst
    }
}
