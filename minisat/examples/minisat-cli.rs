//! # Minisat CLI Tool
//!
//! A simple CLI wrapper around the Minisat solver Rust interface. This is just an example, if you
//! want to use Minisat from the CLI, compile the binary from the Cpp source directly.

use std::{
    io,
    path::{Path, PathBuf},
};

use anyhow::Context;
use clap::Parser;
use rustsat::{
    instances::{fio::opb, ManageVars, SatInstance},
    solvers::{Interrupt, Solve, SolveStats, SolverResult},
};
use rustsat_minisat::{core, simp};

enum FileType {
    Cnf,
    Opb,
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The DIMACS CNF input file. Reads from `stdin` if not given.
    in_path: Option<PathBuf>,
    /// Use the version of Minisat with preprocessing
    #[arg(short, long)]
    simp: bool,
    /// Parse the input as an OPB file by default
    #[arg(short, long)]
    opb: bool,
}

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let inst: SatInstance = if let Some(in_path) = args.in_path {
        match determine_file_type(&in_path, args.opb) {
            FileType::Cnf => SatInstance::from_dimacs_path(in_path)
                .context("error parsing the input file as CNF")?,
            FileType::Opb => SatInstance::from_opb_path(in_path, opb::Options::default())
                .context("error parsing the input file as OPB")?,
        }
    } else if args.opb {
        SatInstance::from_opb(
            &mut io::BufReader::new(io::stdin()),
            opb::Options::default(),
        )
        .context("error parsing input as OPB")?
    } else {
        SatInstance::from_dimacs(&mut io::BufReader::new(io::stdin()))
            .context("error parsing input as CNF")?
    };

    if args.simp {
        solve::<simp::Minisat>(inst)
    } else {
        solve::<core::Minisat>(inst)
    }
}

fn solve<S: Solve + SolveStats + Interrupt + Default>(inst: SatInstance) -> anyhow::Result<()> {
    let mut solver = S::default();

    #[cfg(not(target_family = "windows"))]
    {
        use rustsat::solvers::InterruptSolver;

        // Setup signal handling
        let interrupter = solver.interrupter();
        let mut signals = signal_hook::iterator::Signals::new([
            signal_hook::consts::SIGTERM,
            signal_hook::consts::SIGINT,
            signal_hook::consts::SIGXCPU,
            signal_hook::consts::SIGABRT,
        ])?;
        // Thread for catching incoming signals
        std::thread::spawn(move || {
            for _ in signals.forever() {
                interrupter.interrupt();
            }
        });
    }

    let (cnf, vm) = inst.into_cnf();
    if let Some(max_var) = vm.max_var() {
        solver.reserve(max_var)?;
    }
    solver.add_cnf(cnf)?;
    match solver.solve() {
        Err(err) => {
            println!("s UNKNOWN");
            return Err(err);
        }
        Ok(res) => match res {
            SolverResult::Sat => {
                println!("s SATISFIABLE");
                println!("v {}", solver.full_solution()?);
            }
            SolverResult::Unsat => println!("s UNSATISFIABLE"),
            SolverResult::Interrupted => println!("s UNKNOWN"),
        },
    };
    Ok(())
}

macro_rules! is_one_of {
    ($a:expr, $($b:expr),*) => {
        $( $a == $b || )* false
    }
}

fn determine_file_type(in_path: &Path, opb_default: bool) -> FileType {
    if let Some(ext) = in_path.extension() {
        let path_without_compr = in_path.with_extension("");
        let ext = if is_one_of!(ext, "gz", "bz2") {
            // Strip compression extension
            match path_without_compr.extension() {
                Some(ext) => ext,
                None => return FileType::Cnf, // Fallback default
            }
        } else {
            ext
        };
        if "opb" == ext {
            return FileType::Opb;
        };
        if "cnf" == ext {
            return FileType::Cnf;
        }
    };
    if opb_default {
        FileType::Opb
    } else {
        FileType::Cnf
    } // Fallback default
}
