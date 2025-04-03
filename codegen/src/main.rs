use std::io::Write;

use minijinja::{context, Environment};

fn main() {
    // Check if current directory has a Cargo.toml with [workspace]
    let cargo_toml_path = std::env::current_dir().unwrap().join("Cargo.toml");
    let cargo_toml_content =
        std::fs::read_to_string(cargo_toml_path).expect("Failed to read Cargo.toml");
    if !cargo_toml_content.contains("[workspace]") {
        panic!(
            "Cargo.toml does not contain [workspace] (you must run codegen from the workspace root)"
        );
    }

    let templates = template_env();

    let am1_encs = [
        Am1 {
            name: "Pairwise",
            id: "pairwise",
            wrapped: false,
            n_vars: 4,
            n_clauses: 6,
        },
        Am1 {
            name: "Ladder",
            id: "ladder",
            wrapped: false,
            n_vars: 7,
            n_clauses: 8,
        },
        Am1 {
            name: "Bitwise",
            id: "bitwise",
            wrapped: false,
            n_vars: 6,
            n_clauses: 8,
        },
        Am1 {
            name: "Commander",
            id: "commander",
            wrapped: true,
            n_vars: 5,
            n_clauses: 10,
        },
        Am1 {
            name: "Bimander",
            id: "bimander",
            wrapped: true,
            n_vars: 5,
            n_clauses: 10,
        },
    ];
    let path = "capi/src/encodings/am1.rs";
    capi_am1(path, &am1_encs, &templates).expect("failed to write am1 bindings");
    rustfmt(path);

    let card_encs = [Card {
        name: "Totalizer",
        id: "tot",
        ub: true,
        lb: true,
        n_vars: 12,
        n_clauses: 28,
    }];
    let path = "capi/src/encodings/card.rs";
    capi_card(path, &card_encs, &templates).expect("failed to write card bindings");
    rustfmt(path);

    let pb_encs = [
        Pb {
            name: "GeneralizedTotalizer",
            id: "gte",
            ub: true,
            lb: false,
            extend: true,
            n_vars: 24,
            n_vars_reserve: 24,
            n_clauses: 25,
            skip_reserve: false,
        },
        Pb {
            name: "BinaryAdder",
            id: "bin_adder",
            ub: true,
            lb: true,
            extend: true,
            n_vars: 20,
            n_vars_reserve: 20,
            n_clauses: 53,
            skip_reserve: true,
        },
        Pb {
            name: "DynamicPolyWatchdog",
            id: "dpw",
            ub: true,
            lb: false,
            extend: false,
            n_vars: 19,
            n_vars_reserve: 23,
            n_clauses: 21,
            skip_reserve: false,
        },
    ];
    let path = "capi/src/encodings/pb.rs";
    capi_pb(path, &pb_encs, &templates).expect("failed to write pb bindings");
    rustfmt(path);

    capi_header();
}

fn template_env() -> Environment<'static> {
    let mut env = Environment::new();
    env.set_loader(minijinja::path_loader("codegen/templates"));
    env
}

fn file(path: &str) -> impl std::io::Write {
    std::io::BufWriter::new(std::fs::File::create(path).expect("could not open file"))
}

/// Runs `rustfmt` on a generated file
fn rustfmt(path: &str) {
    // Run rustfmt on the generated file
    let status = std::process::Command::new("rustfmt")
        .arg(path)
        .status()
        .expect("Failed to execute rustfmt");

    if !status.success() {
        eprintln!("rustfmt failed on file {path} with exit code: {status}");
    }
}

#[derive(serde::Serialize)]
struct Am1<'a> {
    name: &'a str,
    id: &'a str,
    wrapped: bool,
    n_vars: u32,
    n_clauses: usize,
}

fn capi_am1(path: &str, encs: &[Am1], templates: &Environment<'static>) -> std::io::Result<()> {
    let mut writer = file(path);
    let tmpl = templates
        .get_template("capi-am1.rs.j2")
        .expect("missing template");
    writeln!(
        writer,
        "{}",
        tmpl.render(context!(encodings => encs))
            .expect("missing template context")
    )
}

#[derive(serde::Serialize)]
struct Card<'a> {
    name: &'a str,
    id: &'a str,
    ub: bool,
    lb: bool,
    n_vars: u32,
    n_clauses: usize,
}

fn capi_card(path: &str, encs: &[Card], templates: &Environment<'static>) -> std::io::Result<()> {
    let mut writer = file(path);
    let tmpl = templates
        .get_template("capi-card.rs.j2")
        .expect("missing template");
    let ub = encs.iter().any(|card| card.ub);
    let lb = encs.iter().any(|card| card.lb);
    writeln!(
        writer,
        "{}",
        tmpl.render(context!(encodings => encs, ub, lb))
            .expect("missing template context")
    )
}

#[derive(serde::Serialize)]
struct Pb<'a> {
    name: &'a str,
    id: &'a str,
    ub: bool,
    lb: bool,
    extend: bool,
    n_vars: u32,
    n_vars_reserve: u32,
    n_clauses: usize,
    skip_reserve: bool,
}

fn capi_pb(path: &str, encs: &[Pb], templates: &Environment<'static>) -> std::io::Result<()> {
    let mut writer = file(path);
    let tmpl = templates
        .get_template("capi-pb.rs.j2")
        .expect("missing template");
    let ub = encs.iter().any(|card| card.ub);
    let lb = encs.iter().any(|card| card.lb);
    writeln!(
        writer,
        "{}",
        tmpl.render(context!(encodings => encs, ub, lb))
            .expect("missing template context")
    )
}

/// Generates the C-API header
fn capi_header() {
    cbindgen::Builder::new()
        .with_config(
            cbindgen::Config::from_file("capi/cbindgen.toml")
                .expect("could not read cbindgen.toml"),
        )
        .with_crate("capi")
        .with_after_include(format!(
            r#"#define RUSTSAT_VERSION {version}
#define RUSTSAT_VERSION_MAJOR {major}
#define RUSTSAT_VERSION_MINOR {minor}
#define RUSTSAT_VERSION_PATCH {patch}"#,
            version = env!("CARGO_PKG_VERSION"),
            major = env!("CARGO_PKG_VERSION_MAJOR"),
            minor = env!("CARGO_PKG_VERSION_MINOR"),
            patch = env!("CARGO_PKG_VERSION_PATCH"),
        ))
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file("capi/rustsat.h");
}
