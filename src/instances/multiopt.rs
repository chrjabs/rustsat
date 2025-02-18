//! # Multi-Objective Optimization Instance Representations

use std::{collections::BTreeSet, io, path::Path};

use crate::{
    encodings::{card, pb},
    types::{
        constraints::{CardConstraint, PbConstraint},
        Assignment, Lit, TernaryVal, Var, WClsIter, WLitIter,
    },
    RequiresClausal, RequiresSoftLits,
};

use super::{
    fio::{self, dimacs::McnfLine},
    BasicVarManager, Cnf, ManageVars, Objective, ReindexVars, SatInstance,
};

/// Type representing a multi-objective optimization instance.
/// The constraints are represented as a [`SatInstance`] struct.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
        for o in &objectives {
            if let Some(mv) = o.max_var() {
                constraints.var_manager_mut().increase_next_free(mv + 1);
            }
        }
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

    /// Gets a mutable reference to the first objective for modifying it.
    /// Make sure `obj_idx` does not exceed the number of objectives in the instance.
    #[deprecated(
        since = "0.5.0",
        note = "get_objective has been renamed to objective_mut and will be removed in a future release"
    )]
    #[allow(clippy::missing_panics_doc)]
    pub fn get_objective(&mut self, obj_idx: usize) -> &mut Objective {
        assert!(obj_idx < self.objs.len());
        &mut self.objs[obj_idx]
    }

    /// Gets a mutable reference to the objective with index `obj_idx` for modifying it.
    /// Make sure `obj_idx` does not exceed the number of objectives in the instance.
    ///
    /// # Panics
    ///
    /// If `obj_idx` exceeds the number of objectives in the instance.
    pub fn objective_mut(&mut self, obj_idx: usize) -> &mut Objective {
        assert!(obj_idx < self.objs.len());
        &mut self.objs[obj_idx]
    }

    /// Gets a reference to the objective with index `obj_idx`.
    /// Make sure `obj_idx` does not exceed the number of objectives in the instance.
    ///
    /// # Panics
    ///
    /// If `obj_idx` exceeds the number of objectives in the instance.
    pub fn objective_ref(&self, obj_idx: usize) -> &Objective {
        assert!(obj_idx < self.objs.len());
        &self.objs[obj_idx]
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
    #[deprecated(
        since = "0.5.0",
        note = "as_hard_cls_soft_cls has been renamed to into_hard_cls_soft_cls and will be removed in a future release"
    )]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_hard_cls_soft_cls(self) -> (Cnf, Vec<(impl WClsIter, isize)>, VM) {
        self.into_hard_cls_soft_cls()
    }

    /// Converts the instance to a set of hard and soft clauses
    ///
    /// # Panic
    ///
    /// This might panic if the conversion to [`Cnf`] runs out of memory.
    pub fn into_hard_cls_soft_cls(self) -> (Cnf, Vec<(impl WClsIter, isize)>, VM) {
        let (cnf, mut vm) = self.constrs.into_cnf();
        let omv = self.objs.iter().fold(Var::new(0), |v, o| {
            if let Some(mv) = o.max_var() {
                return std::cmp::max(v, mv);
            }
            v
        });
        vm.increase_next_free(omv + 1);
        let soft_cls = self
            .objs
            .into_iter()
            .map(Objective::into_soft_cls)
            .collect();
        (cnf, soft_cls, vm)
    }

    /// Converts the instance to a set of hard clauses and soft literals
    #[deprecated(
        since = "0.5.0",
        note = "as_hard_cls_soft_lits has been renamed to into_hard_cls_soft_lits and will be removed in a future release"
    )]
    #[allow(clippy::wrong_self_convention)]
    pub fn as_hard_cls_soft_lits(self) -> (Cnf, Vec<(impl WLitIter, isize)>, VM) {
        self.into_hard_cls_soft_lits()
    }

    /// Converts the instance to a set of hard clauses and soft literals
    ///
    /// # Panic
    ///
    /// This might panic if the conversion to [`Cnf`] runs out of memory.
    pub fn into_hard_cls_soft_lits(self) -> (Cnf, Vec<(impl WLitIter, isize)>, VM) {
        let (mut cnf, mut vm) = self.constrs.into_cnf();
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
                let (hards, softs) = o.into_soft_lits(&mut vm);
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

    /// Re-indexes all variables in the instance with a re-indexing variable manager
    pub fn reindex<R: ReindexVars>(self, mut reindexer: R) -> MultiOptInstance<R> {
        let objs = self
            .objs
            .into_iter()
            .map(|o| o.reindex(&mut reindexer))
            .collect();
        let constrs = self.constrs.reindex(reindexer);
        MultiOptInstance { constrs, objs }
    }

    fn extend_var_set(&self, varset: &mut BTreeSet<Var>) {
        self.constrs.extend_var_set(varset);
        for o in &self.objs {
            o.var_set(varset);
        }
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
    pub fn reindex_ordered<R: ReindexVars>(self, mut reindexer: R) -> MultiOptInstance<R> {
        let mut varset = BTreeSet::new();
        self.extend_var_set(&mut varset);
        // reindex variables in order to ensure ordered re-indexing
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
        self.objs = self.objs.into_iter().map(Objective::shuffle).collect();
        self
    }

    /// Writes the instance to a DIMACS MCNF file at a path
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

    /// Write to DIMACS MCNF
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

    /// Writes the instance to DIMACS MCNF converting non-clausal constraints
    /// with specific encoders.
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
        let soft_cls = self.objs.into_iter().map(Objective::into_soft_cls);
        fio::dimacs::write_mcnf_annotated(writer, &cnf, soft_cls, Some(vm.n_used()))
    }

    /// Writes the instance to a DIMACS MCNF file at a path
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

    /// Write to DIMACS MCNF
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
        let iter = self.objs.iter().map(|o| {
            let offset = o.offset();
            (o.iter_soft_cls(), offset)
        });
        Ok(fio::dimacs::write_mcnf_annotated(
            writer,
            &self.constrs.cnf,
            iter,
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
        for obj in &mut self.objs {
            let vm = self.constrs.var_manager_mut();
            let hardened = obj.convert_to_soft_lits(vm);
            self.constrs.cnf.extend(hardened);
        }
        let objs = self.objs.iter().map(|o| {
            let offset = o.offset();
            (o.iter_soft_lits().unwrap(), offset)
        });
        fio::opb::write_multi_opt::<W, VM, _, _>(writer, &self.constrs, objs, opts)
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
        let objs: Result<Vec<_>, RequiresSoftLits> = self
            .objs
            .iter()
            .map(|o| {
                let offset = o.offset();
                Ok((o.iter_soft_lits()?, offset))
            })
            .collect();
        let objs = objs?;
        Ok(fio::opb::write_multi_opt::<W, VM, _, _>(
            writer,
            &self.constrs,
            objs.into_iter(),
            opts,
        )?)
    }

    /// Calculates the objective values of an assignment. Returns [`None`] if the
    /// assignment is not a solution.
    pub fn cost(&self, assign: &Assignment) -> Option<Vec<isize>> {
        if self.constrs.evaluate(assign) != TernaryVal::True {
            return None;
        }
        Some(self.objs.iter().map(|o| o.evaluate(assign)).collect())
    }
}

impl<VM: ManageVars + Default> MultiOptInstance<VM> {
    /// Creates a new optimization instance
    #[must_use]
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
    /// positive number preceded by an `o`, indicating what objective this soft
    /// clause belongs to. After that, the format is identical to a soft clause
    /// in a WCNF file.
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_dimacs<R: io::BufRead>(reader: &mut R) -> anyhow::Result<Self> {
        fio::dimacs::parse_mcnf(reader)
    }

    /// Parses a DIMACS instance from a file path. For more details see
    /// [`OptInstance::from_dimacs`](super::OptInstance::from_dimacs).
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_dimacs_path<P: AsRef<Path>>(path: P) -> anyhow::Result<Self> {
        let mut reader = fio::open_compressed_uncompressed_read(path)?;
        Self::from_dimacs(&mut reader)
    }

    /// Parses an OPB instance from a reader object.
    ///
    /// # File Format
    ///
    /// The file format expected by this parser is the OPB format for
    /// pseudo-boolean optimization instances with multiple objectives defined.
    /// For details on the file format see
    /// [here](https://www.cril.univ-artois.fr/PB12/format.pdf).
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_opb<R: io::BufRead>(
        reader: &mut R,
        opts: fio::opb::Options,
    ) -> anyhow::Result<Self> {
        fio::opb::parse_multi_opt(reader, opts)
    }

    /// Parses an OPB instance from a file path. For more details see
    /// [`MultiOptInstance::from_opb`]. With feature `compression` supports
    /// bzip2 and gzip compression, detected by the file extension.
    ///
    /// # Errors
    ///
    /// Parsing errors from [`nom`] or [`io::Error`].
    pub fn from_opb_path<P: AsRef<Path>>(path: P, opts: fio::opb::Options) -> anyhow::Result<Self> {
        let mut reader = fio::open_compressed_uncompressed_read(path)?;
        Self::from_opb(&mut reader, opts)
    }
}

impl<VM: ManageVars + Default> FromIterator<McnfLine> for MultiOptInstance<VM> {
    fn from_iter<T: IntoIterator<Item = McnfLine>>(iter: T) -> Self {
        let mut inst = Self::default();
        for line in iter {
            match line {
                McnfLine::Comment(_) => (),
                McnfLine::Hard(cl) => inst.constraints_mut().add_clause(cl),
                McnfLine::Soft(cl, w, oidx) => {
                    if oidx >= inst.objs.len() {
                        inst.objs.resize(oidx + 1, Objective::default());
                    }
                    inst.objective_mut(oidx).add_soft_clause(w, cl);
                }
            }
        }
        inst
    }
}
