//! # CaDiCaL CLI Tool
//!
//! A simple CLI wrapper around the CaDiCaL solver Rust interface. This is just an example, if you
//! want to use CaDiCaL from the CLI, compile the binary from the C source directly.

use anyhow::Context;
use rustsat::instances::SatInstance;

enum FileType {
    Cnf,
    Opb,
}

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The DIMACS CNF input file. Reads from `stdin` if not given.
    in_path: Option<std::path::PathBuf>,
    /// Parse the input as an OPB file by default
    #[arg(short, long)]
    opb: bool,
}

fn main() -> anyhow::Result<()> {
    let args = <Args as clap::Parser>::parse();

    let inst: SatInstance = if let Some(in_path) = args.in_path {
        match determine_file_type(&in_path, args.opb) {
            FileType::Cnf => SatInstance::from_dimacs_path(in_path)
                .context("error parsing the input file as CNF")?,
            FileType::Opb => SatInstance::from_opb_path(
                in_path,
                rustsat::instances::fio::opb::Options::default(),
            )
            .context("error parsing the input file as OPB")?,
        }
    } else if args.opb {
        SatInstance::from_opb(
            &mut std::io::BufReader::new(std::io::stdin()),
            rustsat::instances::fio::opb::Options::default(),
        )
        .context("error parsing input as OPB")?
    } else {
        SatInstance::from_dimacs(&mut std::io::BufReader::new(std::io::stdin()))
            .context("error parsing input as CNF")?
    };

    rustsat_kissat::call_instead_of_abort(Some(kissat_abort));
    solve::<rustsat_kissat::Kissat>(inst)
}

extern "C" fn kissat_abort() {
    println!("s UNKNOWN");
    panic!("kissat called abort");
}

fn solve<S>(inst: SatInstance) -> anyhow::Result<()>
where
    S: rustsat::solvers::Solve
        + rustsat::solvers::SolveStats
        + rustsat::solvers::Interrupt
        + Default,
{
    let mut solver = S::default();

    #[cfg(not(target_family = "windows"))]
    {
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
                rustsat::solvers::InterruptSolver::interrupt(&interrupter);
            }
        });
    }

    let (cnf, vm) = inst.into_cnf();
    if let Some(max_var) = rustsat::instances::ManageVars::max_var(&vm) {
        solver.reserve(max_var)?;
    }
    solver.add_cnf(cnf)?;
    match solver.solve() {
        Err(err) => {
            println!("s UNKNOWN");
            return Err(err);
        }
        Ok(res) => match res {
            rustsat::solvers::SolverResult::Sat => {
                println!("s SATISFIABLE");
                println!("v {}", solver.full_solution()?);
            }
            rustsat::solvers::SolverResult::Unsat => println!("s UNSATISFIABLE"),
            rustsat::solvers::SolverResult::Interrupted => println!("s UNKNOWN"),
        },
    };
    Ok(())
}

macro_rules! is_one_of {
    ($a:expr, $($b:expr),*) => {
        $( $a == $b || )* false
    }
}

fn determine_file_type(in_path: &std::path::Path, opb_default: bool) -> FileType {
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
