//! # Enumerator
//!
//! A small tool that enumerates all solutions of a DIMACS CNF file.

use anyhow::Context;
use rustsat::instances::MultiOptInstance;
use rustsat::instances::OptInstance;
use rustsat::instances::SatInstance;

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The path to the input file. If no path is given, will read from `stdin`.
    in_path: Option<std::path::PathBuf>,
    /// The file format of the input
    #[arg(long, default_value_t = InputFormat::default())]
    input_format: InputFormat,
    /// The maximum number of solutions to enumerate. Enumerates all by default.
    #[arg(short, long)]
    enumerate_until: Option<usize>,
    /// Don't print objective values of solutions found
    #[arg(long)]
    no_objective_values: bool,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 1)]
    opb_first_var_idx: u32,
    #[command(flatten)]
    color: concolor_clap::Color,
}

#[derive(Copy, Clone, PartialEq, Eq, clap::ValueEnum, Default)]
enum InputFormat {
    /// Infer the input file format from the file extension according to the following rules:
    /// - `.cnf`: DIMACS CNF file
    /// - `.wcnf`: WCNF file
    /// - `.mcnf`: MCNF file
    /// - `.opb` / `.mopb` / `.pbmo`: OPB file
    ///
    /// All file extensions can also be appended with `.bz2`, `.xz`, or `.gz` if compression is used.
    #[default]
    Infer,
    /// A DIMACS CNF file
    Cnf,
    /// An OPB file
    Opb,
    /// A WCNF file
    Wcnf,
    /// A MCNF file
    Mcnf,
}

impl std::fmt::Display for InputFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InputFormat::Infer => write!(f, "infer"),
            InputFormat::Cnf => write!(f, "cnf"),
            InputFormat::Wcnf => write!(f, "wcnf"),
            InputFormat::Mcnf => write!(f, "mcnf"),
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
    path: &Option<std::path::PathBuf>,
    file_format: InputFormat,
    opb_opts: rustsat::instances::fio::opb::Options,
) -> anyhow::Result<MultiOptInstance> {
    Ok(match file_format {
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
                        MultiOptInstance::compose(SatInstance::from_dimacs_path(path)?, vec![])
                    } else if is_one_of!(ext, "wcnf") {
                        let (constr, obj) = OptInstance::from_dimacs_path(path)?.decompose();
                        MultiOptInstance::compose(constr, vec![obj])
                    } else if is_one_of!(ext, "mcnf") {
                        MultiOptInstance::from_dimacs_path(path)?
                    } else if is_one_of!(ext, "opb", "pbmo", "mopb") {
                        MultiOptInstance::from_opb_path(path, opb_opts)?
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
                MultiOptInstance::compose(SatInstance::from_dimacs_path(path)?, vec![])
            } else {
                MultiOptInstance::compose(
                    SatInstance::from_dimacs(&mut std::io::BufReader::new(std::io::stdin()))?,
                    vec![],
                )
            }
        }
        InputFormat::Wcnf => {
            if let Some(path) = path {
                let (constr, obj) = OptInstance::from_dimacs_path(path)?.decompose();
                MultiOptInstance::compose(constr, vec![obj])
            } else {
                let (constr, obj) =
                    OptInstance::from_dimacs(&mut std::io::BufReader::new(std::io::stdin()))?
                        .decompose();
                MultiOptInstance::compose(constr, vec![obj])
            }
        }
        InputFormat::Mcnf => {
            if let Some(path) = path {
                MultiOptInstance::from_dimacs_path(path)?
            } else {
                MultiOptInstance::from_dimacs(&mut std::io::BufReader::new(std::io::stdin()))?
            }
        }
        InputFormat::Opb => {
            if let Some(path) = path {
                MultiOptInstance::from_opb_path(path, opb_opts)?
            } else {
                MultiOptInstance::from_opb(
                    &mut std::io::BufReader::new(std::io::stdin()),
                    opb_opts,
                )?
            }
        }
    })
}

struct Enumerator<S: rustsat::solvers::SolveIncremental> {
    solver: S,
    max_var: rustsat::types::Var,
}

impl<S: rustsat::solvers::SolveIncremental> Iterator for Enumerator<S> {
    type Item = rustsat::types::Assignment;

    fn next(&mut self) -> Option<Self::Item> {
        match self.solver.solve().expect("error while solving") {
            rustsat::solvers::SolverResult::Sat => {
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
            rustsat::solvers::SolverResult::Unsat => None,
            rustsat::solvers::SolverResult::Interrupted => {
                panic!("solver interrupted without limits")
            }
        }
    }
}

fn main() -> anyhow::Result<()> {
    use rustsat::instances::ManageVars;
    use rustsat::solvers::Solve;

    let args = <Args as clap::Parser>::parse();
    let opb_opts = rustsat::instances::fio::opb::Options {
        first_var_idx: args.opb_first_var_idx,
        ..rustsat::instances::fio::opb::Options::default()
    };

    let (constr, objs) = parse_instance(&args.in_path, args.input_format, opb_opts)?.decompose();

    let max_var = constr
        .var_manager_ref()
        .max_var()
        .expect("expected at least one variable in the instance");

    let (cnf, vm) = constr.into_cnf();

    let mut solver = rustsat_tools::Solver::default();
    solver
        .reserve(vm.max_var().expect("no variables in instance"))
        .context("error reserving memory in solver")?;
    solver.add_cnf(cnf)?;

    let enumerator = Enumerator { solver, max_var };

    for (cnt, sol) in enumerator.enumerate() {
        if !args.no_objective_values && !objs.is_empty() {
            print!("o");
            for obj in &objs {
                print!(" {}", obj.evaluate(&sol));
            }
            println!();
        }
        println!("v {sol}");
        if args.enumerate_until.is_some_and(|max| cnt + 1 >= max) {
            break;
        }
    }
    Ok(())
}
