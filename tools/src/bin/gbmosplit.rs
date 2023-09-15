//! # gbmosplit
//!
//! Detect generalized boolean multilevel optimization instances from MaxSAT
//! instances and split them into multi-objective instances. Compared to \[1\],
//! in order to have truly separated objectives, we require a stricter criterion
//! for GBMO: left_sum < min_right_diff (instead of <=).
//!
//! ## References
//!
//! - \[1\] Tobias Paxian, Pascal Raiola and Bernd Becker: _On Preprocessing for Weighted MaxSAT_, VMCAI 2021.
//! - \[2\] Josep Argelich, Ines Lynce and Joao Marques-Silva: _On Solving Boolean Multilevel Optimization Problems, IJCAI 2009.

use clap::{Parser, ValueEnum};
use rustsat::{
    instances::{ManageVars, MultiOptInstance, Objective, OptInstance},
    types::Clause,
};
use std::{collections::BTreeSet, fmt, io::Write, path::PathBuf};
use termcolor::{Buffer, BufferWriter, Color, ColorSpec, WriteColor};

struct Cli {
    in_path: PathBuf,
    out_path: Option<PathBuf>,
    split_alg: SplitAlg,
    max_combs: usize,
    always_dump: bool,
    stdout: BufferWriter,
    stderr: BufferWriter,
}

impl Cli {
    fn init() -> Self {
        let args = Args::parse();
        Self {
            in_path: args.in_path,
            out_path: args.out_path,
            split_alg: args.split_alg,
            max_combs: args.max_combs,
            always_dump: args.always_dump,
            stdout: BufferWriter::stdout(match args.color.color {
                concolor_clap::ColorChoice::Always => termcolor::ColorChoice::Always,
                concolor_clap::ColorChoice::Never => termcolor::ColorChoice::Never,
                concolor_clap::ColorChoice::Auto => {
                    if atty::is(atty::Stream::Stdout) {
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
                    if atty::is(atty::Stream::Stderr) {
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

    fn error(&self, msg: &str) {
        let mut buffer = self.stderr.buffer();
        buffer
            .set_color(ColorSpec::new().set_bold(true).set_fg(Some(Color::Red)))
            .unwrap();
        write!(&mut buffer, "error").unwrap();
        buffer.reset().unwrap();
        buffer.set_color(ColorSpec::new().set_bold(true)).unwrap();
        write!(&mut buffer, ": ").unwrap();
        buffer.reset().unwrap();
        writeln!(&mut buffer, "{}", msg).unwrap();
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
    /// The DIMACS WCNF input file
    in_path: PathBuf,
    /// The optional DIMACS MCNF output path. If no path is given only detection
    /// results will be printed.
    out_path: Option<PathBuf>,
    /// The splitting algorithm to use
    #[arg(long, default_value_t = SplitAlg::Gbmo)]
    split_alg: SplitAlg,
    /// The maximum number of weight combinations to check when thoroughly checking GBMO
    #[arg(long, default_value_t = 100000)]
    max_combs: usize,
    /// Always dump an MCNF file, even if the instance couldn't be split
    #[arg(long)]
    always_dump: bool,
    #[command(flatten)]
    color: concolor_clap::Color,
}

#[derive(ValueEnum, Default, Clone, Copy, PartialEq, Eq)]
enum SplitAlg {
    /// Only detect non-generalized boolean multilevel optimization. (This
    /// detects lexicographic optimization of unweighted MO instances.)
    Bmo,
    /// Detect generalized boolean multilevel optimization, but only with the
    /// gcd method. (This detects lexicographic optimization of weighted MO
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
        cli.info("objective is unweighted, can't split");
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

    let (softs, offset) = obj.as_soft_cls();

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
    sorted_clauses: &Vec<(Clause, usize)>,
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

fn main() {
    let cli = Cli::init();

    cli.info(&format!("finding splits in {}", cli.in_path.display()));

    let so_inst: OptInstance = OptInstance::from_dimacs_path(&cli.in_path).unwrap_or_else(|e| {
        cli.error(&format!("could not read input file: {}", e));
        panic!()
    });

    let (mo_inst, split_stats) = split(so_inst, &cli);

    cli.print_split_stats(split_stats);

    let found_split = mo_inst.n_objectives() > 1;

    if let Some(out_path) = &cli.out_path {
        if found_split || cli.always_dump {
            mo_inst.to_dimacs_path(out_path).unwrap_or_else(|e| {
                cli.error(&format!("io error writing the output file: {}", e));
                panic!()
            });
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
