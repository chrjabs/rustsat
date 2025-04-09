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
    capi_enc_bindings(path, "capi-am1.rs.j2", &am1_encs, &templates)
        .expect("failed to write am1 bindings");
    rustfmt(path);
    capi_tests("am1", &am1_encs, &templates).expect("failed to write am1 tests");

    let card_encs = [Card {
        name: "Totalizer",
        id: "tot",
        ub: true,
        lb: true,
        n_vars: 12,
        n_clauses: 28,
    }];
    let path = "capi/src/encodings/card.rs";
    capi_enc_bindings(path, "capi-card.rs.j2", &card_encs, &templates)
        .expect("failed to write card bindings");
    rustfmt(path);
    capi_tests("card", &card_encs, &templates).expect("failed to write card tests");

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
    capi_enc_bindings(path, "capi-pb.rs.j2", &pb_encs, &templates)
        .expect("failed to write pb bindings");
    rustfmt(path);
    capi_tests("pb", &pb_encs, &templates).expect("failed to write pb tests");

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
    let status = std::process::Command::new("rustfmt")
        .arg(path)
        .status()
        .expect("Failed to execute rustfmt");

    if !status.success() {
        eprintln!("rustfmt failed on file {path} with exit code: {status}");
    }
}

/// Runs `clang-format` on a generated file
fn clang_format(path: &str) {
    let status = std::process::Command::new("clang-format")
        .args(["-i", path])
        .status()
        .expect("Failed to execute clang-format");

    if !status.success() {
        eprintln!("clang-format failed on file {path} with exit code: {status}");
    }
}

fn capi_enc_bindings<E: Enc>(
    path: &str,
    template: &str,
    encs: &[E],
    templates: &Environment<'static>,
) -> std::io::Result<()> {
    let mut writer = file(path);
    let tmpl = templates.get_template(template).expect("missing template");
    let ub = encs.iter().any(|enc| enc.ub());
    let lb = encs.iter().any(|enc| enc.lb());
    writeln!(
        writer,
        "{}",
        tmpl.render(context!(encodings => encs, ub => ub, lb => lb))
            .expect("missing template context")
    )
}

fn capi_tests<E: Enc>(
    id: &str,
    encs: &[E],
    templates: &Environment<'static>,
) -> std::io::Result<()> {
    for entry in std::fs::read_dir("codegen/templates/").expect("failed to iteratre over template")
    {
        let entry = entry.unwrap();
        let file_type = entry.file_type().unwrap();
        if file_type.is_file() {
            let filename = entry.file_name();
            let filename = filename.to_str().unwrap();
            if let Some(name) = filename.strip_prefix(&format!("capi-{id}-test-")) {
                let name = name.trim_end_matches(".j2");
                let tmpl = templates.get_template(filename).expect("missing template");
                for enc in encs {
                    if enc.skip(name) {
                        continue;
                    }
                    let path = format!("capi/tests/{}-{name}", enc.id());
                    let mut writer = file(&path);
                    writeln!(
                        writer,
                        "{}",
                        tmpl.render(context!(enc => enc))
                            .expect("missing template context")
                    )?;
                    drop(writer);
                    clang_format(&path);
                }
            }
        }
    }
    Ok(())
}

trait Enc: serde::Serialize {
    fn id(&self) -> &str;
    fn ub(&self) -> bool {
        false
    }
    fn lb(&self) -> bool {
        false
    }
    fn skip(&self, _key: &str) -> bool {
        false
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

impl Enc for Am1<'_> {
    fn id(&self) -> &str {
        self.id
    }
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

impl Enc for Card<'_> {
    fn id(&self) -> &str {
        self.id
    }
    fn ub(&self) -> bool {
        self.ub
    }
    fn lb(&self) -> bool {
        self.lb
    }
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

impl Enc for Pb<'_> {
    fn id(&self) -> &str {
        self.id
    }
    fn ub(&self) -> bool {
        self.ub
    }
    fn lb(&self) -> bool {
        self.lb
    }
    fn skip(&self, key: &str) -> bool {
        if key == "reserve.c" {
            return self.skip_reserve;
        }
        false
    }
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
