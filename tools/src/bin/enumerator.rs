//! # Enumerator
//!
//! A small tool that enumerates all solutions of a DIMACS CNF file.

use std::{fmt, io, path::PathBuf};

use anyhow::Context;
use clap::{Parser, ValueEnum};
use rustsat::{
    instances::{fio, ManageVars, SatInstance},
    solvers::{self, Solve, SolveIncremental},
    types::{Assignment, Var},
};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The path to the input file. If no path is given, will read from `stdin`.
    in_path: Option<PathBuf>,
    /// The file format of the input
    #[arg(long, default_value_t = InputFormat::default())]
    input_format: InputFormat,
    /// The maximum number of solutions to enumerate. Enumerates all by default.
    #[arg(short, long)]
    enumerate_until: Option<usize>,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 1)]
    opb_first_var_idx: u32,
    #[command(flatten)]
    color: concolor_clap::Color,
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
enum InputFormat {
    /// Infer the input file format from the file extension according to the following rules:
    /// - `.cnf`: DIMACS CNF file
    /// - `.opb`: OPB file (without an objective)
    ///
    /// All file extensions can also be appended with `.bz2`, `.xz`, or `.gz` if compression is used.
    #[default]
    Infer,
    /// A DIMACS CNF file
    Cnf,
    /// An OPB file
    Opb,
}

impl fmt::Display for InputFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InputFormat::Infer => write!(f, "infer"),
            InputFormat::Cnf => write!(f, "cnf"),
            InputFormat::Opb => write!(f, "opb"),
        }
    }
}

macro_rules! is_one_of {
    ($a:expr, $($b:expr),*) => {
        $( $a == $b || )* false
    }
}

fn parse_instance(
    path: &Option<PathBuf>,
    file_format: InputFormat,
    opb_opts: fio::opb::Options,
) -> anyhow::Result<SatInstance> {
    match file_format {
        InputFormat::Infer => {
            if let Some(path) = path {
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
                    if is_one_of!(ext, "cnf") {
                        SatInstance::from_dimacs_path(path)
                    } else if is_one_of!(ext, "opb", "pbmo", "mopb") {
                        SatInstance::from_opb_path(path, opb_opts)
                    } else {
                        anyhow::bail!("unknown file extension")
                    }
                } else {
                    anyhow::bail!("no file extension")
                }
            } else {
                anyhow::bail!("cannot infer file format from stdin")
            }
        }
        InputFormat::Cnf => {
            if let Some(path) = path {
                SatInstance::from_dimacs_path(path)
            } else {
                SatInstance::from_dimacs(&mut io::BufReader::new(io::stdin()))
            }
        }
        InputFormat::Opb => {
            if let Some(path) = path {
                SatInstance::from_opb_path(path, opb_opts)
            } else {
                SatInstance::from_opb(&mut io::BufReader::new(io::stdin()), opb_opts)
            }
        }
    }
}

struct Enumerator<S: SolveIncremental> {
    solver: S,
    max_var: Var,
}

impl<S: SolveIncremental> Iterator for Enumerator<S> {
    type Item = Assignment;

    fn next(&mut self) -> Option<Self::Item> {
        match self.solver.solve().expect("error while solving") {
            solvers::SolverResult::Sat => {
                let sol = self
                    .solver
                    .solution(self.max_var)
                    .expect("could not get solution from solver");
                // Add blocking clause to solver
                let bl_cl = sol.clone().into_iter().map(|l| !l).collect();
                self.solver
                    .add_clause(bl_cl)
                    .expect("error adding blocking clause to solver");
                Some(sol)
            }
            solvers::SolverResult::Unsat => None,
            solvers::SolverResult::Interrupted => panic!("solver interrupted without limits"),
        }
    }
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();
    let opb_opts = fio::opb::Options {
        first_var_idx: args.opb_first_var_idx,
        ..fio::opb::Options::default()
    };

    let inst = parse_instance(&args.in_path, args.input_format, opb_opts)?;

    let max_var = inst
        .var_manager_ref()
        .max_var()
        .expect("expected at least one variable in the instance");

    let (cnf, vm) = inst.into_cnf();

    let mut solver = rustsat_tools::Solver::default();
    solver
        .reserve(vm.max_var().expect("no variables in instance"))
        .context("error reserving memory in solver")?;
    solver.add_cnf(cnf)?;

    let enumerator = Enumerator { solver, max_var };

    for (cnt, sol) in enumerator.enumerate() {
        println!("v {}", sol);
        if args.enumerate_until.is_some_and(|max| cnt + 1 >= max) {
            break;
        }
    }
    Ok(())
}
