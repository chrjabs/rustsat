//! # encodings
//!
//! A collection of (multi-objective) MaxSAT encodings.
//!
//! `clustering`: Constrained correlation clustering encodings following \[1\].
//! `knapsack`: Multi-criteria 0-1 knapsack.
//!
//! ## References
//!
//! - \[1\] Jeremias Berg and Matti Järvisalo: _Cost-optimal constrained
//! correlation clustering via weighted partial Maximum Satisfiability_, AIJ
//! 2017.

use clap::{Args, Parser, Subcommand};
use rustsat::{encodings::pb, instances::fio::dimacs};
use rustsat_tools::encodings::{
    clustering::{self, saturating_map, scaling_map, Encoding, Variant},
    knapsack,
};
use std::{fs::File, io, path::PathBuf};

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct CliArgs {
    #[command(subcommand)]
    cmd: Command,
}

#[derive(Subcommand)]
enum Command {
    Clustering(ClusteringArgs),
    Knapsack(KnapsackArgs),
}

#[derive(Args)]
struct ClusteringArgs {
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

#[derive(Args)]
struct KnapsackArgs {
    /// The M/WCNF output path. Writes to `stdout` if not given.
    out_path: Option<PathBuf>,
    /// The number of items to select from
    #[arg(long, default_value_t = 20)]
    n_items: usize,
    /// The number of objectives to generate
    #[arg(long, default_value_t = 2)]
    n_objectives: usize,
    /// The minimum item weight
    #[arg(long, default_value_t = 1)]
    min_weight: usize,
    /// The maximum item weight
    #[arg(long, default_value_t = 40)]
    max_weight: usize,
    /// The minimum item value
    #[arg(long, default_value_t = 1)]
    min_value: usize,
    /// The maximum item value
    #[arg(long, default_value_t = 40)]
    max_value: usize,
    /// The fraction of the weight to set the capacity to
    #[arg(long, default_value_t = 2)]
    cap_fraction: usize,
    /// The random seed to use
    #[arg(long, default_value_t = 42)]
    seed: u64,
}

fn clustering(args: ClusteringArgs) -> anyhow::Result<()> {
    let mcnf_to_wcnf = |line: dimacs::McnfLine| match line {
        dimacs::McnfLine::Comment(c) => dimacs::WcnfLine::Comment(c),
        dimacs::McnfLine::Hard(cl) => dimacs::WcnfLine::Hard(cl),
        dimacs::McnfLine::Soft(cl, w, _) => dimacs::WcnfLine::Soft(cl, w),
    };

    if let Some(in_path) = args.in_path {
        let encoding = clustering::Encoding::new(
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
        } else if args.single_objective {
            dimacs::write_wcnf(&mut io::stdout(), encoding.map(mcnf_to_wcnf))?;
        } else {
            dimacs::write_mcnf(&mut io::stdout(), encoding)?;
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
        } else if args.single_objective {
            dimacs::write_wcnf(&mut io::stdout(), encoding.map(mcnf_to_wcnf))?;
        } else {
            dimacs::write_mcnf(&mut io::stdout(), encoding)?;
        }
    };

    Ok(())
}

fn knapsack(args: KnapsackArgs) -> anyhow::Result<()> {
    let encoding = knapsack::Encoding::new::<pb::DynamicPolyWatchdog>(knapsack::Knapsack::random(
        args.n_items,
        args.n_objectives,
        args.min_value..args.max_value,
        args.min_weight..args.max_weight,
        knapsack::Capacity::FractionTotalWeight(args.cap_fraction),
        args.seed,
    ));
    if let Some(out_path) = args.out_path {
        let mut file = File::open(out_path)?;
        dimacs::write_mcnf(&mut file, encoding)?;
    } else {
        dimacs::write_mcnf(&mut io::stdout(), encoding)?;
    }
    Ok(())
}

fn main() -> anyhow::Result<()> {
    let args = CliArgs::parse();

    match args.cmd {
        Command::Clustering(args) => clustering(args),
        Command::Knapsack(args) => knapsack(args),
    }
}
