//! # opb2cnf
//!
//! A small tool for converting OPB files to DIMACS CNF.

use clap::Parser;
use rustsat::instances::{fio::opb::Options as OpbOptions, SatInstance};
use std::path::PathBuf;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The OPB input file
    in_path: PathBuf,
    /// The DIMACS CNF output path
    out_path: PathBuf,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 0)]
    first_var_idx: usize,
}

fn main() {
    let args = Args::parse();
    let mut opb_opts = OpbOptions::default();
    opb_opts.first_var_idx = args.first_var_idx;

    let inst: SatInstance =
        SatInstance::from_opb_path(args.in_path, opb_opts).expect("error parsing the input file");

    println!("{} clauses", inst.n_clauses());
    println!("{} cards", inst.n_cards());
    println!("{} pbs", inst.n_pbs());

    inst.to_dimacs_path(args.out_path)
        .expect("io error writing the output file");
}
