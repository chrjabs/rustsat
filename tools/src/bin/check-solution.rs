//! # `check-solution`
//!
//! A small tool for checking solutions to SAT and optimization instances.

use std::{io, path::PathBuf};

use clap::{Parser, ValueEnum};
use rustsat::{
    instances::{
        fio::{self, opb::Options as OpbOptions},
        MultiOptInstance, OptInstance, SatInstance,
    },
    types::Assignment,
};

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum)]
pub enum FileFormat {
    /// Infer the file format from the file extension according to the following rules:
    /// - `.cnf`: DIMACS CNF file
    /// - `.wcnf`: Weighted DIMACS CNF (MaxSAT) file
    /// - `.mcnf`: Multi-objective MaxSAT file
    /// - `.opb`: OPB file (without an objective)
    /// - `.mopb` / `.pbmo`: Multi-objective OPB file
    ///
    /// All file extensions can also be appended with `.bz2`, `.xz`, or `.gz` if compression is used.
    Infer,
    /// A DIMACS CNF file
    Cnf,
    /// A DIMACS WCNF file
    Wcnf,
    /// A DIMACS MCNF file
    Mcnf,
    /// An OPB file with zero or more objectives
    Opb,
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The instance to check the solution against
    instance: PathBuf,
    /// The solution specified as one or multiple v-lines. If not specified, will be read from
    /// `stdin`.
    solution: Option<PathBuf>,
    /// The file format of the instance. With infer, the file format is
    /// inferred from the file extension.
    #[arg(long, value_enum, default_value_t = FileFormat::Infer)]
    file_format: FileFormat,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 1)]
    opb_first_var_idx: u32,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let opb_opts = OpbOptions {
        first_var_idx: args.opb_first_var_idx,
        ..OpbOptions::default()
    };
    let (constrs, objs) = parse_instance(args.instance, args.file_format, opb_opts)?.decompose();

    let mut reader = if let Some(solution) = args.solution {
        fio::open_compressed_uncompressed_read(solution)?
    } else {
        Box::new(io::BufReader::new(io::stdin()))
    };

    let mut sol = Assignment::default();
    loop {
        let mut buf = String::new();
        let read = reader.read_line(&mut buf)?;
        if read == 0 {
            break;
        }
        if buf.starts_with('v') {
            sol.extend_from_vline(&buf)?;
        }
    }

    if let Some(constr) = constrs.unsat_constraint(&sol) {
        println!("unsatisfied contraint: {constr}");
        std::process::exit(1);
    }
    print!("objective values: ");
    for i in 0..objs.len() {
        if i < objs.len() - 1 {
            print!("{}, ", objs[i].evaluate(&sol))
        } else {
            print!("{}", objs[i].evaluate(&sol));
        }
    }
    println!();
    Ok(())
}

macro_rules! is_one_of {
    ($a:expr, $($b:expr),*) => {
        $( $a == $b || )* false
    }
}

fn parse_instance(
    inst_path: PathBuf,
    file_format: FileFormat,
    opb_opts: fio::opb::Options,
) -> anyhow::Result<MultiOptInstance> {
    match file_format {
        FileFormat::Infer => {
            if let Some(ext) = inst_path.extension() {
                let path_without_compr = inst_path.with_extension("");
                let ext = if is_one_of!(ext, "gz", "bz2", "xz") {
                    // Strip compression extension
                    match path_without_compr.extension() {
                        Some(ext) => ext,
                        None => anyhow::bail!("no file extension after compression extension"),
                    }
                } else {
                    ext
                };
                let inst = if is_one_of!(ext, "cnf", "dimacs") {
                    let inst = SatInstance::from_dimacs_path(inst_path)?;
                    MultiOptInstance::compose(inst, vec![])
                } else if is_one_of!(ext, "wcnf") {
                    let (inst, obj) = OptInstance::from_dimacs_path(inst_path)?.decompose();
                    MultiOptInstance::compose(inst, vec![obj])
                } else if is_one_of!(ext, "mcnf") {
                    MultiOptInstance::from_dimacs_path(inst_path)?
                } else if is_one_of!(ext, "opb", "mopb", "pbmo") {
                    MultiOptInstance::from_opb_path(inst_path, opb_opts)?
                } else {
                    anyhow::bail!("unknown file extension")
                };
                Ok(inst)
            } else {
                anyhow::bail!("no file extension")
            }
        }
        FileFormat::Cnf => {
            let inst = SatInstance::from_dimacs_path(inst_path)?;
            Ok(MultiOptInstance::compose(inst, vec![]))
        }
        FileFormat::Wcnf => {
            let (inst, obj) = OptInstance::from_dimacs_path(inst_path)?.decompose();
            Ok(MultiOptInstance::compose(inst, vec![obj]))
        }
        FileFormat::Mcnf => MultiOptInstance::from_dimacs_path(inst_path),
        FileFormat::Opb => MultiOptInstance::from_opb_path(inst_path, opb_opts),
    }
}
