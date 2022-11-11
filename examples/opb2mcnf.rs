//! # opb2mcnf
//!
//! A small tool for converting OPB files to DIMACS MCNF.
//!
//! Useage: opb2wcnf [opb file] [dimacs mcnf output path]

use rustsat::instances::MultiOptInstance;

macro_rules! print_usage {
    () => {{
        eprintln!("Usage: opb2mcnf [opb file] [dimacs mcnf output path]");
        panic!()
    }};
}

fn main() {
    let in_path = std::env::args().nth(1).unwrap_or_else(|| print_usage!());
    let out_path = std::env::args().nth(2).unwrap_or_else(|| print_usage!());

    let inst: MultiOptInstance =
        MultiOptInstance::from_opb_path(in_path).expect("error parsing the input file");

    inst.to_dimacs_path(out_path)
        .expect("io error writing the output file");
}
