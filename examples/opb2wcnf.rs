//! # opb2wcnf
//!
//! A small tool for converting OPB files to DIMACS WCNF.
//!
//! Useage: opb2wcnf [opb file] [dimacs wcnf output path]

use rustsat::instances::OptInstance;

macro_rules! print_usage {
    () => {{
        eprintln!("Usage: opb2wcnf [opb file] [dimacs wcnf output path]");
        panic!()
    }};
}

fn main() {
    let in_path = std::env::args().nth(1).unwrap_or_else(|| print_usage!());
    let out_path = std::env::args().nth(2).unwrap_or_else(|| print_usage!());

    let inst: OptInstance =
        OptInstance::from_opb_path(in_path).expect("error parsing the input file");

    inst.to_dimacs_path(out_path)
        .expect("io error writing the output file");
}
