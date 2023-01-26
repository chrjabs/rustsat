//! # wcnf2opb
//!
//! A small tool for converting DIMACS WCNF files to OPB.

use clap::Parser;
use rustsat::instances::{fio::opb::Options as OpbOptions, OptInstance};
use std::path::PathBuf;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The DIMACS WCNF input file
    in_path: PathBuf,
    /// The OPB output path
    out_path: PathBuf,
    /// Avoid negated literals in the OPB file by transforming constraints
    #[arg(long)]
    avoid_negated_lits: bool,
}

fn main() {
    let args = Args::parse();
    let mut opb_opts = OpbOptions::default();
    opb_opts.no_negated_lits = args.avoid_negated_lits;

    let inst: OptInstance =
        OptInstance::from_dimacs_path(args.in_path).expect("error parsing the input file");

    inst.to_opb_path(args.out_path, opb_opts)
        .expect("io error writing the output file");
}
