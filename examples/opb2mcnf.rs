//! # opb2mcnf
//!
//! A small tool for converting OPB files to DIMACS MCNF.

use clap::Parser;
use rustsat::instances::{fio::opb::Options as OpbOptions, MultiOptInstance};
use std::path::PathBuf;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The OPB input file
    in_path: PathBuf,
    /// The DIMACS MCNF output path
    out_path: PathBuf,
    /// The index in the OPB file to treat as the lowest variable
    #[arg(long, default_value_t = 0)]
    first_var_index: usize,
}

fn main() {
    let args = Args::parse();
    let mut opb_opts = OpbOptions::default();
    opb_opts.first_var_idx = 0;

    let inst: MultiOptInstance = MultiOptInstance::from_opb_path(args.in_path, opb_opts)
        .expect("error parsing the input file");

    inst.to_dimacs_path(args.out_path)
        .expect("io error writing the output file");
}
