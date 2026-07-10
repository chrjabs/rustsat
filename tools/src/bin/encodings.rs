//! # `encodings`
//!
//! A collection of (multi-objective) MaxSAT/PBO encodings.
//!
//! ## CNF/MaxSAT Encodings
//!
//! - `clustering`: Constrained correlation clustering encodings following \[1\].
//! - `knapsack`: Multi-criteria 0-1 knapsack.
//!
//! ## PBO Encodings
//!
//! - `knapsack`: Multi-criteria 0-1 knapsack.
//! - `assignment`: Multi-criteria assignment problem.
//! - `facility-location`: Multi-criteria 0/1 uncapacitated facility location problem.
//!
//! ## References
//!
//! - \[1\] Jeremias Berg and Matti Järvisalo: _Cost-optimal constrained
//!   correlation clustering via weighted partial Maximum Satisfiability_, AIJ
//!   2017.

use rustsat::instances::fio;
use rustsat::types::Lit;
use rustsat_tools::encodings::assignment;
use rustsat_tools::encodings::cnf;
use rustsat_tools::encodings::facilitylocation;
use rustsat_tools::encodings::knapsack;
use rustsat_tools::encodings::pb;

#[derive(clap::Parser)]
#[command(author, version, about, long_about = None)]
struct CliArgs {
    /// The output path. Writes to `stdout` if not given.
    out_path: Option<std::path::PathBuf>,
    #[command(subcommand)]
    fmt: Format,
}

#[derive(clap::Subcommand)]
enum Format {
    /// Generate a CNF encoding
    Cnf(CnfArgs),
    /// Generate a PB encoding
    Pb(PbArgs),
}

#[derive(clap::Args)]
struct CnfArgs {
    #[command(subcommand)]
    enc: CnfEncoding,
    #[arg(long, short = 's')]
    single_objective: bool,
}

#[derive(clap::Subcommand)]
enum CnfEncoding {
    /// Generate a clustering encoding
    Clustering(ClusteringArgs),
    /// Generate a knapsack encoding
    Knapsack(KnapsackArgs),
}

#[derive(clap::Args)]
struct PbArgs {
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 1)]
    first_var_idx: u32,
    /// Avoid negated literals in the OPB file by transforming constraints
    #[arg(long)]
    avoid_negated_lits: bool,
    #[command(subcommand)]
    enc: PbEncoding,
}

#[derive(clap::Subcommand)]
enum PbEncoding {
    /// Generate a knapsack encoding
    Knapsack(KnapsackArgs),
    /// Generate an assignment problem encoding
    Assignment(AssignmentArgs),
    /// Generate a facility location problem encoding
    FacilityLocation(FacilityLocationArgs),
}

#[derive(clap::Args)]
struct ClusteringArgs {
    /// The input file. Each line represents an edge between two nodes in the
    /// form `[nodeA] [nodeB] [similarity value]`. Reads from `stdin` if not
    /// given.
    in_path: Option<std::path::PathBuf>,
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

#[derive(clap::Args)]
struct KnapsackArgs {
    #[command(subcommand)]
    variant: KnapsackCommand,
}

#[derive(clap::Subcommand)]
enum KnapsackCommand {
    /// Encode a given input instance
    Input(InputKnapsackArgs),
    /// Generate a random instance
    Random(RandomKnapsackArgs),
}

#[derive(clap::Args)]
struct InputKnapsackArgs {
    /// The input file
    in_path: Option<std::path::PathBuf>,
    #[arg(long, default_value_t = KnapsackInputFormat::default())]
    in_format: KnapsackInputFormat,
}

#[derive(Default, clap::ValueEnum, Clone, Copy, PartialEq, Eq)]
enum KnapsackInputFormat {
    /// Input files as provided by [MOO-Library](http://home.ku.edu.tr/~moolibrary/)
    #[default]
    MooLibrary,
    /// Input files as provided by [vOptLib](https://github.com/vOptSolver/vOptLib/tree/master/UKP)
    VOptLib,
}

#[derive(clap::Args)]
struct AssignmentArgs {
    /// The input file in the format as provided by [MOO-Library](http://home.ku.edu.tr/~moolibrary/)
    in_path: Option<std::path::PathBuf>,
}

#[derive(clap::Args)]
struct FacilityLocationArgs {
    /// The input file in the format as provided by [vOptLib](https://github.com/vOptSolver/vOptLib/tree/master/UFLP)
    in_path: Option<std::path::PathBuf>,
}

impl std::fmt::Display for KnapsackInputFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KnapsackInputFormat::MooLibrary => write!(f, "moo-library"),
            KnapsackInputFormat::VOptLib => write!(f, "v-opt-lib"),
        }
    }
}

impl From<KnapsackInputFormat> for knapsack::FileFormat {
    fn from(val: KnapsackInputFormat) -> Self {
        match val {
            KnapsackInputFormat::MooLibrary => knapsack::FileFormat::MooLibrary,
            KnapsackInputFormat::VOptLib => knapsack::FileFormat::VOptLib,
        }
    }
}

#[derive(clap::Args)]
struct RandomKnapsackArgs {
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

fn clustering(args: ClusteringArgs) -> anyhow::Result<impl Iterator<Item = fio::dimacs::McnfLine>> {
    if let Some(in_path) = args.in_path {
        cnf::clustering::Encoding::new(
            std::io::BufReader::new(std::fs::File::open(in_path)?),
            |sim| {
                cnf::clustering::saturating_map(
                    cnf::clustering::scaling_map(sim, args.multiplier) - args.offset,
                    args.dont_care,
                    args.hard_threshold,
                )
            },
        )
    } else {
        cnf::clustering::Encoding::new(std::io::BufReader::new(std::io::stdin()), |sim| {
            cnf::clustering::saturating_map(
                cnf::clustering::scaling_map(sim, args.multiplier) - args.offset,
                args.dont_care,
                args.hard_threshold,
            )
        })
    }
}

fn random_knapsack(args: &RandomKnapsackArgs) -> knapsack::Knapsack {
    knapsack::Knapsack::random(
        args.n_items,
        args.n_objectives,
        args.min_value..args.max_value,
        args.min_weight..args.max_weight,
        knapsack::Capacity::FractionTotalWeight(args.cap_fraction),
        args.seed,
    )
}

fn input_knapsack(args: &InputKnapsackArgs) -> anyhow::Result<knapsack::Knapsack> {
    if let Some(path) = &args.in_path {
        let reader = std::io::BufReader::new(std::fs::File::open(path)?);
        knapsack::Knapsack::from_file(reader, args.in_format.into())
    } else {
        knapsack::Knapsack::from_file(
            std::io::BufReader::new(std::io::stdin()),
            args.in_format.into(),
        )
    }
}

fn cnf_knapsack(inst: knapsack::Knapsack) -> impl Iterator<Item = fio::dimacs::McnfLine> {
    cnf::knapsack::Encoding::new::<rustsat::encodings::pb::DynamicPolyWatchdog>(inst)
}

fn pb_knapsack(
    inst: knapsack::Knapsack,
) -> impl Iterator<Item = fio::opb::FileLine<<Vec<(Lit, usize)> as IntoIterator>::IntoIter>> {
    pb::knapsack::Encoding::new(inst)
}

fn input_assignment(args: &AssignmentArgs) -> anyhow::Result<assignment::Assignment> {
    if let Some(path) = &args.in_path {
        let reader = std::io::BufReader::new(std::fs::File::open(path)?);
        assignment::Assignment::from_file(reader)
    } else {
        assignment::Assignment::from_file(std::io::BufReader::new(std::io::stdin()))
    }
}

fn pb_assignment(
    inst: assignment::Assignment,
) -> impl Iterator<Item = fio::opb::FileLine<<Vec<(Lit, usize)> as IntoIterator>::IntoIter>> {
    pb::assignment::Encoding::new(inst)
}

fn input_facility_location(
    args: &FacilityLocationArgs,
) -> anyhow::Result<facilitylocation::FacilityLocation> {
    if let Some(path) = &args.in_path {
        let reader = std::io::BufReader::new(std::fs::File::open(path)?);
        facilitylocation::FacilityLocation::from_file(reader)
    } else {
        facilitylocation::FacilityLocation::from_file(std::io::BufReader::new(std::io::stdin()))
    }
}

fn pb_facility_location(
    inst: facilitylocation::FacilityLocation,
) -> impl Iterator<Item = fio::opb::FileLine<<Vec<(Lit, usize)> as IntoIterator>::IntoIter>> {
    pb::facilitylocation::Encoding::new(inst)
}

fn write_cnf(
    encoding: impl Iterator<Item = fio::dimacs::McnfLine>,
    path: Option<std::path::PathBuf>,
    single_objective: bool,
) -> anyhow::Result<()> {
    let mcnf_to_wcnf = |line: fio::dimacs::McnfLine| match line {
        fio::dimacs::McnfLine::Comment(c) => fio::dimacs::WcnfLine::Comment(c),
        fio::dimacs::McnfLine::Hard(cl) => fio::dimacs::WcnfLine::Hard(cl),
        fio::dimacs::McnfLine::Soft(cl, w, _) => fio::dimacs::WcnfLine::Soft(cl, w),
    };

    if let Some(out_path) = path {
        let mut file = std::io::BufWriter::new(std::fs::File::create(out_path)?);
        if single_objective {
            fio::dimacs::write_wcnf(&mut file, encoding.map(mcnf_to_wcnf))?;
        } else {
            fio::dimacs::write_mcnf(&mut file, encoding)?;
        }
    } else if single_objective {
        fio::dimacs::write_wcnf(&mut std::io::stdout(), encoding.map(mcnf_to_wcnf))?;
    } else {
        fio::dimacs::write_mcnf(&mut std::io::stdout(), encoding)?;
    }
    Ok(())
}

fn write_pb<LI: rustsat::types::WLitIter>(
    encoding: impl Iterator<Item = fio::opb::FileLine<LI>>,
    path: Option<std::path::PathBuf>,
    opts: fio::opb::Options,
) -> anyhow::Result<()> {
    if let Some(out_path) = path {
        let mut file = std::io::BufWriter::new(std::fs::File::create(out_path)?);
        fio::opb::write_opb_lines(&mut file, encoding, opts)?;
    } else {
        fio::opb::write_opb_lines(&mut std::io::stdout(), encoding, opts)?;
    }
    Ok(())
}

type BoxedDimacsIter = Box<dyn Iterator<Item = fio::dimacs::McnfLine>>;
type BoxedOpbIter =
    Box<dyn Iterator<Item = fio::opb::FileLine<<Vec<(Lit, usize)> as IntoIterator>::IntoIter>>>;

fn main() -> anyhow::Result<()> {
    let args = <CliArgs as clap::Parser>::parse();

    let out_path = args.out_path;
    match args.fmt {
        Format::Cnf(args) => {
            let enc: BoxedDimacsIter = match args.enc {
                CnfEncoding::Clustering(args) => Box::new(clustering(args)?),
                CnfEncoding::Knapsack(args) => {
                    let inst = match args.variant {
                        KnapsackCommand::Input(args) => input_knapsack(&args)?,
                        KnapsackCommand::Random(args) => random_knapsack(&args),
                    };
                    Box::new(cnf_knapsack(inst))
                }
            };
            write_cnf(enc, out_path, args.single_objective)
        }
        Format::Pb(args) => {
            let opts = fio::opb::Options {
                first_var_idx: args.first_var_idx,
                no_negated_lits: args.avoid_negated_lits,
            };
            let enc: BoxedOpbIter = match args.enc {
                PbEncoding::Knapsack(args) => {
                    let inst = match args.variant {
                        KnapsackCommand::Input(args) => input_knapsack(&args)?,
                        KnapsackCommand::Random(args) => random_knapsack(&args),
                    };
                    Box::new(pb_knapsack(inst))
                }
                PbEncoding::Assignment(args) => {
                    let inst = input_assignment(&args)?;
                    Box::new(pb_assignment(inst))
                }
                PbEncoding::FacilityLocation(args) => {
                    let inst = input_facility_location(&args)?;
                    Box::new(pb_facility_location(inst))
                }
            };
            write_pb(enc, out_path, opts)
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn verify_cli_args() {
        <super::CliArgs as clap::CommandFactory>::command().debug_assert()
    }
}
