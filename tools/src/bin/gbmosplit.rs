//! # `gbmosplit`
//!
//! Detect generalized boolean multilevel optimization instances from MaxSAT
//! instances and split them into multi-objective instances. Compared to \[1\],
//! in order to have truly separated objectives, we require a stricter criterion
//! for GBMO: `left_sum < min_right_diff` (instead of `<=`).
//!
//! ## References
//!
//! - \[1\] Tobias Paxian, Pascal Raiola and Bernd Becker: _On Preprocessing for Weighted MaxSAT_, VMCAI 2021.
//! - \[2\] Josep Argelich, Ines Lynce and Joao Marques-Silva: _On Solving Boolean Multilevel Optimization Problems, IJCAI 2009.

use clap::{Parser, ValueEnum};
use rustsat::{
    instances::{fio, ManageVars, MultiOptInstance, Objective, OptInstance},
    types::Clause,
};
use std::{
    collections::BTreeSet,
    fmt,
    io::{self, IsTerminal, Write},
    path::PathBuf,
};
use termcolor::{Buffer, BufferWriter, Color, ColorSpec, WriteColor};

struct Cli {
    in_path: Option<PathBuf>,
    out_path: Option<PathBuf>,
    input_format: InputFormat,
    output_format: OutputFormat,
    split_alg: SplitAlg,
    max_combs: usize,
    always_dump: bool,
    opb_opts: fio::opb::Options,
    stdout: BufferWriter,
    stderr: BufferWriter,
}

impl Cli {
    fn init() -> Self {
        let args = Args::parse();
        Self {
            in_path: args.in_path,
            out_path: args.out_path,
            input_format: args.input_format,
            output_format: args.output_format,
            split_alg: args.split_alg,
            max_combs: args.max_combs,
            always_dump: args.always_dump,
            opb_opts: fio::opb::Options {
                first_var_idx: args.opb_first_var_idx,
                ..fio::opb::Options::default()
            },
            stdout: BufferWriter::stdout(match args.color.color {
                concolor_clap::ColorChoice::Always => termcolor::ColorChoice::Always,
                concolor_clap::ColorChoice::Never => termcolor::ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if io::stdout().is_terminal() {
                        termcolor::ColorChoice::Auto
                    } else {
                        termcolor::ColorChoice::Never
                    }
                }
            }),
            stderr: BufferWriter::stderr(match args.color.color {
                concolor_clap::ColorChoice::Always => termcolor::ColorChoice::Always,
                concolor_clap::ColorChoice::Never => termcolor::ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if io::stderr().is_terminal() {
                        termcolor::ColorChoice::Auto
                    } else {
                        termcolor::ColorChoice::Never
                    }
                }
            }),
        }
    }

    fn warning(&self, msg: &str) {
        let mut buffer = self.stderr.buffer();
        buffer
            .set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Yellow)))
            .unwrap();
        write!(&mut buffer, "warning").unwrap();
        buffer.reset().unwrap();
        buffer.set_color(ColorSpec::new().set_bold(true)).unwrap();
        write!(&mut buffer, ": ").unwrap();
        buffer.reset().unwrap();
        writeln!(&mut buffer, "{}", msg).unwrap();
        self.stdout.print(&buffer).unwrap();
    }

    fn error(&self, err: &anyhow::Error) {
        let mut buffer = self.stderr.buffer();
        buffer
            .set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Red)))
            .unwrap();
        write!(&mut buffer, "error").unwrap();
        buffer.reset().unwrap();
        buffer.set_color(ColorSpec::new().set_bold(true)).unwrap();
        write!(&mut buffer, ": ").unwrap();
        buffer.reset().unwrap();
        writeln!(&mut buffer, "{}", err).unwrap();
        self.stdout.print(&buffer).unwrap();
    }

    fn info(&self, msg: &str) {
        let mut buffer = self.stdout.buffer();
        buffer
            .set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))
            .unwrap();
        write!(&mut buffer, "info").unwrap();
        buffer.reset().unwrap();
        buffer.set_color(ColorSpec::new().set_bold(true)).unwrap();
        write!(&mut buffer, ": ").unwrap();
        buffer.reset().unwrap();
        writeln!(&mut buffer, "{}", msg).unwrap();
        self.stdout.print(&buffer).unwrap();
    }

    fn print_split_stats(&self, split_stats: SplitStats) {
        let mut buffer = self.stdout.buffer();
        Self::start_block(&mut buffer);
        buffer
            .set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Blue)))
            .unwrap();
        write!(&mut buffer, "Split Stats").unwrap();
        buffer.reset().unwrap();
        buffer.set_color(ColorSpec::new().set_bold(true)).unwrap();
        write!(&mut buffer, ": ").unwrap();
        buffer.reset().unwrap();
        writeln!(
            &mut buffer,
            "split objective into {} separate objectives",
            split_stats.obj_stats.len()
        )
        .unwrap();
        split_stats
            .obj_stats
            .into_iter()
            .enumerate()
            .for_each(|(idx, os)| Self::print_obj_stats(&mut buffer, idx + 1, os));
        Self::end_block(&mut buffer);
        self.stdout.print(&buffer).unwrap();
    }

    fn print_obj_stats(buffer: &mut Buffer, idx: usize, stats: ObjStats) {
        Self::start_block(buffer);
        buffer
            .set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))
            .unwrap();
        write!(buffer, "Objective").unwrap();
        buffer.reset().unwrap();
        writeln!(buffer, " #{}", idx).unwrap();
        Self::print_parameter(buffer, "n-softs", stats.n_softs);
        Self::print_parameter(buffer, "weight-sum", stats.weight_sum);
        Self::print_parameter(buffer, "min-weight", stats.min_weight);
        Self::print_parameter(buffer, "max-weight", stats.max_weight);
        Self::print_parameter(buffer, "multiplier", stats.multiplier);
        Self::end_block(buffer);
    }

    fn print_parameter<V: fmt::Display>(buffer: &mut Buffer, name: &str, val: V) {
        buffer
            .set_color(ColorSpec::new().set_fg(Some(Color::Cyan)))
            .unwrap();
        write!(buffer, "{}", name).unwrap();
        buffer.reset().unwrap();
        writeln!(buffer, ": {}", val).unwrap();
    }

    fn start_block(buffer: &mut Buffer) {
        buffer.set_color(ColorSpec::new().set_dimmed(true)).unwrap();
        write!(buffer, ">>>>>").unwrap();
        buffer.reset().unwrap();
        writeln!(buffer).unwrap();
    }

    fn end_block(buffer: &mut Buffer) {
        buffer.set_color(ColorSpec::new().set_dimmed(true)).unwrap();
        write!(buffer, "<<<<<").unwrap();
        buffer.reset().unwrap();
        writeln!(buffer).unwrap();
    }
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The path to the input file. If no path is given, will read from `stdin`.
    in_path: Option<PathBuf>,
    /// The optional output path. If no path is given, will write to `stdout`.
    out_path: Option<PathBuf>,
    /// The splitting algorithm to use
    #[arg(long, default_value_t = SplitAlg::default())]
    split_alg: SplitAlg,
    /// The maximum number of weight combinations to check when thoroughly checking GBMO
    #[arg(long, default_value_t = 100000)]
    max_combs: usize,
    /// The file format of the input
    #[arg(long, default_value_t = InputFormat::default())]
    input_format: InputFormat,
    /// The file format to write
    #[arg(long, default_value_t = OutputFormat::default())]
    output_format: OutputFormat,
    /// Always dump a multi-objective file, even if the instance couldn't be split
    #[arg(long, short = 'd')]
    always_dump: bool,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 1)]
    opb_first_var_idx: u32,
    #[command(flatten)]
    color: concolor_clap::Color,
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
enum InputFormat {
    /// Infer the input file format from the file extension according to the following rules:
    /// - `.wcnf`: Weighted DIMACS CNF (MaxSAT) file
    /// - `.opb`: OPB file (without an objective)
    ///
    /// All file extensions can also be appended with `.bz2`, `.xz`, or `.gz` if compression is used.
    #[default]
    Infer,
    /// A DIMACS WCNF file
    Wcnf,
    /// An OPB file
    Opb,
}

impl fmt::Display for InputFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InputFormat::Infer => write!(f, "infer"),
            InputFormat::Wcnf => write!(f, "wcnf"),
            InputFormat::Opb => write!(f, "opb"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Default)]
enum OutputFormat {
    /// Same as the input format
    #[default]
    AsInput,
    /// DIMACS WCNF
    Mcnf,
    /// OPB
    Opb,
}

impl fmt::Display for OutputFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OutputFormat::AsInput => write!(f, "as-input"),
            OutputFormat::Mcnf => write!(f, "mcnf"),
            OutputFormat::Opb => write!(f, "opb"),
        }
    }
}

impl OutputFormat {
    fn infer(self, write_format: WriteFormat) -> WriteFormat {
        match self {
            OutputFormat::AsInput => write_format,
            OutputFormat::Mcnf => WriteFormat::Mcnf,
            OutputFormat::Opb => WriteFormat::Opb,
        }
    }
}

#[derive(Copy, Clone)]
enum WriteFormat {
    Mcnf,
    Opb,
}

#[derive(ValueEnum, Default, Clone, Copy, PartialEq, Eq)]
enum SplitAlg {
    /// Only detect non-generalized boolean multilevel optimization. (This
    /// detects lexicographic optimization of unweighted MO instances.)
    Bmo,
    /// Detect generalized boolean multilevel optimization, but only with the
    /// GCD method. (This detects lexicographic optimization of weighted MO
    /// instances.)
    Gcd,
    /// Full generalized boolean multilevel optimization detection. (With this
    /// detection, weights of higher ranked objectives can potentially not be
    /// divided/normalized.)
    #[default]
    Gbmo,
}

impl fmt::Display for SplitAlg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SplitAlg::Bmo => write!(f, "bmo"),
            SplitAlg::Gcd => write!(f, "gcd"),
            SplitAlg::Gbmo => write!(f, "gbmo"),
        }
    }
}

struct SplitStats {
    obj_stats: Vec<ObjStats>,
}

struct ObjStats {
    n_softs: usize,
    weight_sum: usize,
    min_weight: usize,
    max_weight: usize,
    multiplier: usize,
}

fn split<VM: ManageVars>(
    so_inst: OptInstance<VM>,
    cli: &Cli,
) -> (MultiOptInstance<VM>, SplitStats) {
    let (constr, obj) = so_inst.decompose();

    if !obj.weighted() {
        cli.warning("objective is unweighted, can't split");
        let obj_stats = ObjStats {
            n_softs: obj.n_softs(),
            weight_sum: obj.weight_sum(),
            min_weight: obj.min_weight(),
            max_weight: obj.max_weight(),
            multiplier: 1,
        };
        return (
            MultiOptInstance::compose(constr, vec![obj]),
            SplitStats {
                obj_stats: vec![obj_stats],
            },
        );
    }

    let (softs, offset) = obj.into_soft_cls();

    if offset != 0 {
        cli.warning(&format!(
            "objective offset is not zero ({}), will be added to the lowest ranking objective",
            offset
        ));
    }

    let mut sorted_clauses: Vec<_> = softs.into_iter().collect();
    sorted_clauses.sort_by(|wc1, wc2| wc1.1.cmp(&wc2.1));

    let (mut objs, split_stats) = match cli.split_alg {
        SplitAlg::Bmo => split_bmo(sorted_clauses),
        SplitAlg::Gcd => split_gbmo(sorted_clauses, cli),
        SplitAlg::Gbmo => split_gbmo(sorted_clauses, cli),
    };

    // add offset of original objective to last objective
    objs.last_mut().unwrap().set_offset(offset);

    (MultiOptInstance::compose(constr, objs), split_stats)
}

fn perform_split(
    sorted_clauses: Vec<(Clause, usize)>,
    split_ends: Vec<usize>,
) -> (Vec<Objective>, SplitStats) {
    // split objectives and collect stats
    let mut objs = vec![];
    let mut split_start = 0;
    let mut split_stats = SplitStats { obj_stats: vec![] };
    for split_end in split_ends {
        let softs = &sorted_clauses[split_start..split_end + 1];
        let w_gcd = softs
            .iter()
            .fold(softs[0].1, |w_gcd, (_, w)| gcd(w_gcd, *w));
        let obj = Objective::from_iter(softs.iter().cloned().map(|(c, w)| (c, w / w_gcd)));
        split_stats.obj_stats.push(ObjStats {
            n_softs: obj.n_softs(),
            weight_sum: obj.weight_sum(),
            min_weight: obj.min_weight(),
            max_weight: obj.max_weight(),
            multiplier: w_gcd,
        });
        objs.push(obj);
        split_start = split_end + 1;
    }
    let softs = &sorted_clauses[split_start..];
    let w_gcd = softs
        .iter()
        .fold(softs[0].1, |w_gcd, (_, w)| gcd(w_gcd, *w));
    let obj = Objective::from_iter(softs.iter().cloned().map(|(c, w)| (c, w / w_gcd)));
    split_stats.obj_stats.push(ObjStats {
        n_softs: obj.n_softs(),
        weight_sum: obj.weight_sum(),
        min_weight: obj.min_weight(),
        max_weight: obj.max_weight(),
        multiplier: w_gcd,
    });
    objs.push(obj);
    (objs, split_stats)
}

fn split_bmo(sorted_clauses: Vec<(Clause, usize)>) -> (Vec<Objective>, SplitStats) {
    let mut multipliers = vec![sorted_clauses.first().unwrap().1];
    let mut split_ends = vec![];
    let mut sum = 0;
    for (idx, (_, w)) in sorted_clauses.iter().enumerate() {
        if w > multipliers.last().unwrap() {
            if *w <= sum {
                // instance not BMO, return original instance
                split_ends.clear();
                break;
            } else {
                multipliers.push(*w);
                split_ends.push(idx - 1);
            }
        }
        sum += *w;
    }
    perform_split(sorted_clauses, split_ends)
}

fn gcd(mut a: usize, mut b: usize) -> usize {
    // Euclid's algorithm
    while b != 0 {
        a %= b;
        std::mem::swap(&mut a, &mut b);
    }
    a
}

fn get_sums_pot_splits_gcds(
    sorted_clauses: &[(Clause, usize)],
) -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut sums = vec![];
    let mut pot_split_ends = vec![];
    let mut sum = 0;
    // find sums and potential splits
    for idx in 0..sorted_clauses.len() {
        sum += sorted_clauses[idx].1;
        sums.push(sum);
        if idx < sorted_clauses.len() - 1 && sorted_clauses[idx + 1].1 > sum {
            pot_split_ends.push(idx);
        }
    }
    // calculate gcds backwards
    let mut gcds = vec![sorted_clauses.last().unwrap().1];
    for (_, w) in sorted_clauses.iter().rev().skip(1) {
        gcds.push(gcd(*gcds.last().unwrap(), *w));
    }
    (sums, pot_split_ends, gcds.into_iter().rev().collect())
}

fn check_split_thorough_gbmo(
    right_partition: &[(Clause, usize)],
    left_sum: usize,
    cli: &Cli,
) -> bool {
    // first check immediate weight distances (fail fast)
    for idx in 0..right_partition.len() - 1 {
        let dist = right_partition[idx + 1].1 - right_partition[idx].1;
        if dist != 0 && dist < left_sum {
            return false;
        }
    }
    // Check all weight combinations (disclaimer: exponential runtime).
    let right_sum = right_partition.iter().fold(0, |s, (_, w)| s + w);
    let mut all_weight_combs: BTreeSet<usize> = BTreeSet::new();
    for (_, w) in right_partition {
        let w = *w;
        // add w to all previous weight combs and compare to adjacent weight combs.
        // copy existing weight combs to iterate over while modifying set.
        for weight_comb in all_weight_combs.iter().copied().collect::<Vec<_>>() {
            let new_comb = weight_comb + w;
            if !all_weight_combs.insert(new_comb) {
                // weight combination already in set
                continue;
            }
            let next_lower = all_weight_combs.range(0..new_comb).last().unwrap();
            if new_comb - *next_lower <= left_sum {
                // lower difference between new comb and next lower known comb
                return false;
            }
            if let Some(next_higher) = all_weight_combs.range(new_comb + 1..right_sum + 1).next() {
                if next_higher - new_comb <= left_sum {
                    // lower difference between new comb and next higher known comb
                    return false;
                }
            }
            if all_weight_combs.len() > cli.max_combs {
                cli.warning(&format!(
                    "thorough GBMO check terminated after {} checked weight combinations",
                    all_weight_combs.len()
                ));
                return false;
            }
        }
        if !all_weight_combs.insert(w) {
            // weight combination already in set
            continue;
        }
        if let Some(next_lower) = all_weight_combs.range(0..w).last() {
            if w - *next_lower <= left_sum {
                // lower difference between w and next lower known comb
                return false;
            }
        }
        if let Some(next_higher) = all_weight_combs.range(w + 1..right_sum).next() {
            if next_higher - w <= left_sum {
                // lower difference between w and next higher known comb
                return false;
            }
        }
        if all_weight_combs.len() > cli.max_combs {
            cli.warning(&format!(
                "thorough GBMO check terminated after {} checked weight combinations",
                all_weight_combs.len()
            ));
            return false;
        }
    }
    true
}

fn split_gbmo(sorted_clauses: Vec<(Clause, usize)>, cli: &Cli) -> (Vec<Objective>, SplitStats) {
    let (sums, pot_split_ends, gcds) = get_sums_pot_splits_gcds(&sorted_clauses);
    let mut split_ends = vec![];
    for split_end in pot_split_ends {
        // checking strictly for truly separate objectives
        if sums[split_end] < gcds[split_end + 1]
            || (cli.split_alg == SplitAlg::Gbmo
                && check_split_thorough_gbmo(
                    &sorted_clauses[split_end + 1..],
                    sums[split_end],
                    cli,
                ))
        {
            split_ends.push(split_end);
        }
    }
    perform_split(sorted_clauses, split_ends)
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
) -> anyhow::Result<(OptInstance, WriteFormat)> {
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
                    if is_one_of!(ext, "wcnf") {
                        OptInstance::from_dimacs_path(path).map(|inst| (inst, WriteFormat::Mcnf))
                    } else if is_one_of!(ext, "opb") {
                        OptInstance::from_opb_path(path, opb_opts)
                            .map(|inst| (inst, WriteFormat::Opb))
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
        InputFormat::Wcnf => {
            if let Some(path) = path {
                OptInstance::from_dimacs_path(path).map(|inst| (inst, WriteFormat::Mcnf))
            } else {
                OptInstance::from_dimacs(&mut io::BufReader::new(io::stdin()))
                    .map(|inst| (inst, WriteFormat::Mcnf))
            }
        }
        InputFormat::Opb => {
            if let Some(path) = path {
                OptInstance::from_opb_path(path, opb_opts).map(|inst| (inst, WriteFormat::Opb))
            } else {
                OptInstance::from_opb(&mut io::BufReader::new(io::stdin()), opb_opts)
                    .map(|inst| (inst, WriteFormat::Opb))
            }
        }
    }
}

macro_rules! handle_error {
    ($res:expr, $cli:expr) => {{
        match $res {
            Ok(val) => val,
            Err(err) => {
                $cli.error(&err);
                anyhow::bail!(err)
            }
        }
    }};
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::init();

    if let Some(path) = &cli.in_path {
        cli.info(&format!("finding splits in {}", path.display()));
    }

    let (so_inst, write_format) = handle_error!(
        parse_instance(&cli.in_path, cli.input_format, cli.opb_opts),
        cli
    );

    let (mut mo_inst, split_stats) = split(so_inst, &cli);

    if cli.out_path.is_some() {
        cli.print_split_stats(split_stats);
    }

    let found_split = mo_inst.n_objectives() > 1;

    let write_format = cli.output_format.infer(write_format);

    if found_split || cli.always_dump {
        match write_format {
            WriteFormat::Mcnf => {
                mo_inst.constraints_mut().convert_to_cnf();
                if let Some(path) = &cli.out_path {
                    cli.info(&format!("writing mcnf to {}", path.display()));
                    handle_error!(mo_inst.write_dimacs_path(path), cli);
                } else {
                    handle_error!(
                        mo_inst.write_dimacs(&mut io::BufWriter::new(io::stdout())),
                        cli
                    );
                }
            }
            WriteFormat::Opb => {
                let (mut constrs, mut objs) = mo_inst.decompose();
                for obj in &mut objs {
                    obj.convert_to_soft_lits(constrs.var_manager_mut());
                }
                let mo_inst = MultiOptInstance::compose(constrs, objs);
                if let Some(path) = &cli.out_path {
                    cli.info(&format!("writing opb to {}", path.display()));
                    handle_error!(mo_inst.write_opb_path(path, cli.opb_opts), cli);
                } else {
                    handle_error!(
                        mo_inst.write_opb(&mut io::BufWriter::new(io::stdout()), cli.opb_opts),
                        cli
                    );
                }
            }
        }
    }

    if found_split {
        std::process::exit(0);
    }
    std::process::exit(1);
}

#[cfg(test)]
mod tests {
    use rustsat::{clause, lit};

    #[test]
    fn split_bmo() {
        let sorted_clauses = vec![
            (clause![lit![0]], 1),
            (clause![lit![1]], 1),
            (clause![lit![2]], 3),
            (clause![lit![3]], 3),
        ];
        let (objs, split_stats) = super::split_bmo(sorted_clauses);
        assert_eq!(objs.len(), 2);
        assert_eq!(split_stats.obj_stats.len(), 2);
        assert_eq!(split_stats.obj_stats[0].n_softs, 2);
        assert_eq!(split_stats.obj_stats[1].n_softs, 2);
        assert_eq!(split_stats.obj_stats[0].weight_sum, 2);
        assert_eq!(split_stats.obj_stats[1].weight_sum, 2);
        assert_eq!(split_stats.obj_stats[0].min_weight, 1);
        assert_eq!(split_stats.obj_stats[1].min_weight, 1);
        assert_eq!(split_stats.obj_stats[0].max_weight, 1);
        assert_eq!(split_stats.obj_stats[1].max_weight, 1);
        assert_eq!(split_stats.obj_stats[0].multiplier, 1);
        assert_eq!(split_stats.obj_stats[1].multiplier, 3);
    }

    #[test]
    fn gbmo_pre_calc() {
        let sorted_clauses = vec![
            (clause![lit![0]], 1),
            (clause![lit![1]], 1),
            (clause![lit![2]], 3),
            (clause![lit![3]], 3),
        ];
        let (sums, pot_split_ends, gcds) = super::get_sums_pot_splits_gcds(&sorted_clauses);
        assert_eq!(sums, vec![1, 2, 5, 8]);
        assert_eq!(pot_split_ends, vec![1]);
        assert_eq!(gcds, vec![1, 1, 3, 3]);
    }
}
