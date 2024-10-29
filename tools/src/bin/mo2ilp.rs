//! # `mo2ilp`
//!
//! A small tool for converting multi-objective MaxSAT/PBO instances to the custom MO-ILP input formats.

use std::{fmt, io, path::PathBuf};

use anyhow::Context;
use clap::{Parser, ValueEnum};
use itertools::Itertools;
use rustsat::{
    instances::{
        fio::{self, opb::Options as OpbOptions},
        BasicVarManager, ManageVars, MultiOptInstance, Objective, ReindexingVarManager,
    },
    types::{constraints::PbConstraint, Var},
};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The MCNF/MOPB input file. Reads from `stdin` if not given.
    in_path: Option<PathBuf>,
    /// The output path. Writes to `stdout` if not given.
    out_path: Option<PathBuf>,
    /// The input file format
    #[arg(long, value_enum, default_value_t = InputFormat::Infer)]
    input_format: InputFormat,
    /// The output file format
    #[arg(long, value_enum, default_value_t = OutputFormat::Fgt)]
    output_format: OutputFormat,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 1)]
    first_var_idx: u32,
    /// Specify what to do with variables that do not appear in the instance
    #[arg(long, value_enum, default_value_t = UnusedVars::AssignZero)]
    unused_vars: UnusedVars,
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum InputFormat {
    /// Infer the file format from the file extension according to the following rules:
    /// - `.mcnf`: Multi-objective MaxSAT file
    /// - `.opb`, `.pbmo`, `.mopb`: OPB file
    ///
    /// All file extensions can also be appended with `.bz2`, `.xz`, or `.gz` if compression is used.
    Infer,
    /// A DIMACS MCNF file
    Mcnf,
    /// An OPB file with multiple objectives
    Opb,
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum OutputFormat {
    /// Custom input format for [Bauss et al. 2023](https://git.uni-wuppertal.de/bauss/adaptive-improvements-of-multi-objective-branch-and-bound)
    Bauss,
    /// FGT format read by [Forget et al. 2022](https://github.com/NicolasJForget/LinearRelaxationBasedMultiObjectiveBranchAndBound/tree/v2.0)
    Fgt,
}

/// What to do with variables that do not appear in the instance
#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
enum UnusedVars {
    /// Don't do anything
    Nothing,
    /// Remove them, decreasing the index of the remaining variables
    Remove,
    /// Assign them to zero
    AssignZero,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let opb_opts = OpbOptions {
        first_var_idx: args.first_var_idx,
        ..OpbOptions::default()
    };

    let inst = parse_instance(args.in_path, args.input_format, opb_opts)
        .context("failed to parse input instance")?;

    let inst = match args.unused_vars {
        UnusedVars::Nothing => inst,
        UnusedVars::Remove => {
            let (mut constr, objs) = inst
                .reindex_ordered(ReindexingVarManager::default())
                .decompose();
            let next_free = constr.new_var();
            let (constr, _) =
                constr.change_var_manager(|_| BasicVarManager::from_next_free(next_free));
            MultiOptInstance::compose(constr, objs)
        }
        UnusedVars::AssignZero => {
            let varset = inst.var_set();
            let n_vars = inst.constraints_ref().n_vars();
            let mut inst = inst;
            for idx in 0..n_vars {
                let var = Var::new(idx);
                if !varset.contains(&var) {
                    inst.constraints_mut().add_unit(var.neg_lit());
                }
            }
            inst
        }
    };

    if let Some(path) = args.out_path {
        write_instance(
            inst,
            args.output_format,
            &mut fio::open_compressed_uncompressed_write(path)?,
        )?;
    } else {
        write_instance(
            inst,
            args.output_format,
            &mut io::BufWriter::new(io::stdout()),
        )?;
    }
    Ok(())
}

macro_rules! is_one_of {
    ($a:expr, $($b:expr),*) => {
        $( $a == $b || )* false
    }
}

fn parse_instance(
    path: Option<PathBuf>,
    file_format: InputFormat,
    opb_opts: OpbOptions,
) -> anyhow::Result<MultiOptInstance> {
    match file_format {
        InputFormat::Infer => {
            let path = if let Some(path) = path {
                path
            } else {
                anyhow::bail!("cannot infer file format from stdin");
            };
            if let Some(ext) = path.extension() {
                let path_without_compr = path.with_extension("");
                let ext = if is_one_of!(ext, "gz", "bz2", "xz") {
                    // Strip compression extension
                    match path_without_compr.extension() {
                        Some(ext) => ext,
                        None => anyhow::bail!("no file extension after compression extension"),
                    }
                } else {
                    ext
                };
                if is_one_of!(ext, "mcnf") {
                    MultiOptInstance::from_dimacs_path(path)
                } else if is_one_of!(ext, "opb", "mopb", "pbmo") {
                    MultiOptInstance::from_opb_path(path, opb_opts)
                } else {
                    anyhow::bail!("unknown file extension")
                }
            } else {
                anyhow::bail!("no file extension")
            }
        }
        InputFormat::Mcnf => {
            if let Some(path) = path {
                MultiOptInstance::from_dimacs_path(path)
            } else {
                MultiOptInstance::from_dimacs(&mut io::BufReader::new(io::stdin()))
            }
        }
        InputFormat::Opb => {
            if let Some(path) = path {
                MultiOptInstance::from_opb_path(path, opb_opts)
            } else {
                MultiOptInstance::from_opb(&mut io::BufReader::new(io::stdin()), opb_opts)
            }
        }
    }
}

fn write_instance<W: io::Write>(
    inst: MultiOptInstance,
    format: OutputFormat,
    writer: &mut W,
) -> io::Result<()> {
    let (constr, mut objs) = inst.decompose();
    let (mut pbs, mut vm) = constr.into_pbs();
    let omv = objs.iter().fold(Var::new(0), |v, o| {
        if let Some(mv) = o.max_var() {
            return std::cmp::max(v, mv);
        }
        v
    });
    vm.increase_next_free(omv + 1);
    pbs.extend(
        objs.iter_mut()
            .flat_map(|o| o.convert_to_soft_lits(&mut vm))
            .map(PbConstraint::from),
    );
    // add aux variable unit for objective offset
    pbs.push(PbConstraint::new_lb([(vm.new_lit(), 1)], 1));

    // compute non-zeroes
    let non_zero_constrs: usize = pbs.iter().map(PbConstraint::len).sum();
    let non_zero_objs: usize = objs.iter().map(Objective::n_softs).sum();

    match format {
        OutputFormat::Bauss => {
            // #vars #constrs #objs #nonzerosinconstrs #nonzerosincosts
            writeln!(
                writer,
                "{} {} {} {non_zero_constrs} {non_zero_objs}",
                vm.n_used(),
                pbs.len(),
                objs.len(),
            )?;
        }
        OutputFormat::Fgt => {
            // #vars #constrs #objs
            writeln!(writer, "{} {} {}", vm.n_used(), pbs.len(), objs.len(),)?;
        }
    }
    writeln!(writer)?;

    if matches!(format, OutputFormat::Fgt) {
        // objective types
        writeln!(writer, "{}", (0..objs.len()).map(|_| "minsum").format(" "))?;
        writeln!(writer)?;
    }

    // cost matrix
    for obj in objs {
        write_objective(obj, vm.n_used(), writer)?;
    }
    writeln!(writer)?;

    // constraint matrix
    let bounds = pbs
        .into_iter()
        .map(|c| write_constraint(c, vm.n_used(), writer))
        .collect::<io::Result<Vec<_>>>()?;
    writeln!(writer)?;

    // rhs
    for (op, bound) in bounds {
        writeln!(writer, "{op} {bound}")?;
    }

    if matches!(format, OutputFormat::Fgt) {
        writeln!(writer)?;
        writeln!(writer, "{}", (0..vm.n_used()).map(|_| 0).format(" "))?;
        writeln!(writer, "{}", (0..vm.n_used()).map(|_| 1).format(" "))?;
    }

    Ok(())
}

fn write_objective<W: io::Write>(obj: Objective, n_vars: u32, writer: &mut W) -> io::Result<()> {
    let mut coefs = vec![0; n_vars as usize];
    for (lit, coef) in obj.iter_soft_lits().unwrap() {
        let mut coef =
            isize::try_from(coef).expect("cannot handle coefficients larger than `isize::MAX`");
        if lit.is_neg() {
            *coefs.last_mut().unwrap() += coef;
            coef = -coef;
        }
        coefs[lit.var().idx()] += coef;
    }
    *coefs.last_mut().unwrap() += obj.offset();
    writeln!(writer, "{}", coefs.into_iter().format(" "))
}

fn write_constraint<W: io::Write>(
    constr: PbConstraint,
    n_vars: u32,
    writer: &mut W,
) -> io::Result<(Operator, isize)> {
    let mut coefs = vec![0; n_vars as usize];
    let (lits, op, mut bound) = match constr {
        PbConstraint::Ub(constr) => {
            let (lits, b) = constr.decompose();
            (lits, Operator::Lte, b)
        }
        PbConstraint::Lb(constr) => {
            let (lits, b) = constr.decompose();
            (lits, Operator::Gte, b)
        }
        PbConstraint::Eq(constr) => {
            let (lits, b) = constr.decompose();
            (lits, Operator::Eq, b)
        }
    };
    for (lit, coef) in lits {
        let mut coef =
            isize::try_from(coef).expect("cannot handle coefficients larger than `isize::MAX`");
        if lit.is_neg() {
            bound -= coef;
            coef = -coef;
        }
        coefs[lit.var().idx()] += coef;
    }
    writeln!(writer, "{}", coefs.into_iter().format(" "))?;
    Ok((op, bound))
}

#[derive(Clone, Copy)]
enum Operator {
    Gte,
    Lte,
    Eq,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operator::Gte => write!(f, "0"),
            Operator::Lte => write!(f, "1"),
            Operator::Eq => write!(f, "2"),
        }
    }
}
