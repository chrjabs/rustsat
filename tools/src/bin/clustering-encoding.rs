//! # clustering-encoding
//!
//! Constrained correlation clustering encodings following \[1\].
//!
//! ## References
//!
//! - \[1\] Jeremias Berg and Matti Järvisalo: _Cost-optimal constrained
//! correlation clustering via weighted partial Maximum Satisfiability_, AIJ
//! 2017.

use clap::Parser;
use rustsat::instances::fio::dimacs;
use rustsat_tools::encodings::clustering::{saturating_map, scaling_map, Encoding, Error, Variant};
use std::{fs::File, io, path::PathBuf};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The input file. Each line represents an edge between two nodes in the
    /// form `[nodeA] [nodeB] [similarity value]`. Reads from `stdin` if not
    /// given.
    in_path: Option<PathBuf>,
    /// The M/WCNF output path. Writes to `stdout` if not given.
    out_path: Option<PathBuf>,
    /// The encoding variant
    #[arg(long, default_value_t = Variant::default())]
    variant: Variant,
    /// Instead of outputting a multi-objective MCNF file, output the
    /// single-objective MaxSAT encoding.
    #[arg(long)]
    single_objective: bool,
    /// The fixed point multiplier
    #[arg(long, default_value_t = 1000)]
    multiplier: u32,
    /// An offset on the similarity values (applied after the multiplier)
    #[arg(long, default_value_t = 500)]
    offset: isize,
    /// Similarities of absolute value below this value (after the multiplier
    /// and offset) will be ignored
    #[arg(long, default_value_t = 1)]
    dont_care: usize,
    /// Similarities of absolute value above this value (after the multiplier
    /// and offset) will be regarded as hard constraints
    #[arg(long, default_value_t = 499)]
    hard_threshold: usize,
}

fn main() -> Result<(), Error> {
    let args = Args::parse();

    let mcnf_to_wcnf = |line: dimacs::McnfLine| match line {
        dimacs::McnfLine::Comment(c) => dimacs::WcnfLine::Comment(c),
        dimacs::McnfLine::Hard(cl) => dimacs::WcnfLine::Hard(cl),
        dimacs::McnfLine::Soft(cl, w, _) => dimacs::WcnfLine::Soft(cl, w),
    };

    if let Some(in_path) = args.in_path {
        let encoding = Encoding::new(
            io::BufReader::new(File::open(in_path)?),
            args.variant,
            |sim| {
                saturating_map(
                    scaling_map(sim, args.multiplier) - args.offset,
                    args.dont_care,
                    args.hard_threshold,
                )
            },
        )?;
        if let Some(out_path) = args.out_path {
            let mut file = File::open(out_path)?;
            if args.single_objective {
                dimacs::write_wcnf(&mut file, encoding.map(mcnf_to_wcnf))?;
            } else {
                dimacs::write_mcnf(&mut file, encoding)?;
            }
        } else {
            if args.single_objective {
                dimacs::write_wcnf(&mut io::stdout(), encoding.map(mcnf_to_wcnf))?;
            } else {
                dimacs::write_mcnf(&mut io::stdout(), encoding)?;
            }
        }
    } else {
        let encoding = Encoding::new(io::BufReader::new(io::stdin()), args.variant, |sim| {
            saturating_map(
                scaling_map(sim, args.multiplier) - args.offset,
                args.dont_care,
                args.hard_threshold,
            )
        })?;
        if let Some(out_path) = args.out_path {
            let mut file = File::open(out_path)?;
            if args.single_objective {
                dimacs::write_wcnf(&mut file, encoding.map(mcnf_to_wcnf))?;
            } else {
                dimacs::write_mcnf(&mut file, encoding)?;
            }
        } else {
            if args.single_objective {
                dimacs::write_wcnf(&mut io::stdout(), encoding.map(mcnf_to_wcnf))?;
            } else {
                dimacs::write_mcnf(&mut io::stdout(), encoding)?;
            }
        }
    };

    Ok(())
}
