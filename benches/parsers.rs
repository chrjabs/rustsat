use gungraun::{library_benchmark, library_benchmark_group, main};

static CNF: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/data/AProVE11-12.cnf"));

#[library_benchmark]
fn parse_cnf() {
    let reader = std::io::Cursor::new(CNF);
    let _: rustsat::instances::SatInstance =
        rustsat::instances::SatInstance::from_dimacs(reader).unwrap();
}

static WCNF: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/data/pre-processing_c_inference_50_54_fq15.wcnf"
));

#[library_benchmark]
fn parse_wcnf() {
    let reader = std::io::Cursor::new(WCNF);
    let _: rustsat::instances::OptInstance =
        rustsat::instances::OptInstance::from_dimacs(reader).unwrap();
}

static WCNF_UNIT_SOFT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/data/auctions_wt-cat_sched_60_70_0003.txt.wcnf"
));

#[library_benchmark]
fn parse_wcnf_unit_soft() {
    let reader = std::io::Cursor::new(WCNF_UNIT_SOFT);
    let _: rustsat::instances::OptInstance =
        rustsat::instances::OptInstance::from_dimacs(reader).unwrap();
}

static MCNF: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/data/ftp.mcnf"));

#[library_benchmark]
fn parse_mcnf() {
    let reader = std::io::Cursor::new(MCNF);
    let _: rustsat::instances::MultiOptInstance =
        rustsat::instances::MultiOptInstance::from_dimacs(reader).unwrap();
}

library_benchmark_group!(name = benches; benchmarks = parse_cnf, parse_wcnf, parse_wcnf_unit_soft, parse_mcnf);
main!(library_benchmark_groups = benches);
