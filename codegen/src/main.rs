use std::io::{BufRead, Write};

use minijinja::{context, Environment};
use similar::{ChangeTag, TextDiff};
use tempfile::NamedTempFile;

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

    let do_check = std::env::args().any(|arg| arg == "--check");
    let mut has_changes = false;

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
    let generated = rustfmt(capi_enc_bindings("capi-am1.rs.j2", &am1_encs, &templates));
    if do_check {
        has_changes |= diff(path, &generated);
    } else {
        write!(file(path), "{generated}").unwrap();
    }
    has_changes |= capi_tests("am1", &am1_encs, &templates, do_check);

    for enc in &am1_encs {
        let path = format!("fuzz/fuzz_targets/{}.rs", enc.id);
        let generated = rustfmt(fuzz_enc("fuzz-am1.rs.j2", enc, &templates));
        if do_check {
            has_changes |= diff(&path, &generated);
        } else {
            write!(file(&path), "{generated}").unwrap();
        }
    }

    let card_encs = [Card {
        name: "Totalizer",
        id: "tot",
        ub: true,
        lb: true,
        n_vars: 12,
        n_clauses: 28,
    }];
    let path = "capi/src/encodings/card.rs";
    let generated = rustfmt(capi_enc_bindings("capi-card.rs.j2", &card_encs, &templates));
    if do_check {
        has_changes |= diff(path, &generated);
    } else {
        write!(file(path), "{generated}").unwrap();
    }
    has_changes |= capi_tests("card", &card_encs, &templates, do_check);

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
            n_vars_reserve: 19,
            n_clauses: 21,
            skip_reserve: false,
        },
    ];
    let path = "capi/src/encodings/pb.rs";
    let generated = rustfmt(capi_enc_bindings("capi-pb.rs.j2", &pb_encs, &templates));
    if do_check {
        has_changes |= diff(path, &generated);
    } else {
        write!(file(path), "{generated}").unwrap();
    }
    has_changes |= capi_tests("pb", &pb_encs, &templates, do_check);

    has_changes |= capi_header(do_check);

    let path = "fuzz/Cargo.toml";
    let generated = fuzz_toml(path, "fuzz-cargo.toml.j2", &am1_encs, &templates);
    if do_check {
        has_changes |= diff(path, &generated);
    } else {
        write!(file(path), "{generated}").unwrap();
    }

    if has_changes && do_check {
        std::process::exit(1);
    }
}

fn template_env() -> Environment<'static> {
    let mut env = Environment::new();
    env.set_loader(minijinja::path_loader("codegen/templates"));
    env
}

fn file(path: &str) -> impl std::io::Write {
    std::io::BufWriter::new(std::fs::File::create(path).expect("could not open file"))
}

/// Runs `rustfmt` on a generated string
fn rustfmt(generated: String) -> String {
    let mut fmt = std::process::Command::new("rustfmt")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("Failed to spawn rustfmt");

    fmt.stdin
        .take()
        .expect("Failed to get stdin")
        .write_all(generated.as_bytes())
        .expect("Failed to write to rustfmt stdin");

    let formatted_output = fmt.wait_with_output().expect("Failed to wait for rustfmt");
    if !formatted_output.status.success() {
        eprintln!("rustfmt failed with exit code: {}", formatted_output.status);
        std::process::exit(1);
    }

    String::from_utf8(formatted_output.stdout).unwrap()
}

/// Runs `clang-format` on a generated string
fn clang_format(generated: String) -> String {
    let mut fmt = std::process::Command::new("clang-format")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("Failed to spawn clang-format");

    fmt.stdin
        .take()
        .expect("Failed to get stdin")
        .write_all(generated.as_bytes())
        .expect("Failed to write to clang-format stdin");

    let formatted_output = fmt
        .wait_with_output()
        .expect("Failed to wait for clang-format");
    if !formatted_output.status.success() {
        eprintln!(
            "clang-format failed with exit code: {}",
            formatted_output.status
        );
        std::process::exit(1);
    }

    String::from_utf8(formatted_output.stdout).unwrap()
}

fn diff(path: &str, generated: &str) -> bool {
    let Ok(old) = std::fs::read(path) else {
        eprintln!("Would create {path}");
        return true;
    };
    let old = std::str::from_utf8(&old).unwrap();
    if old == generated {
        return false;
    }
    let diff = TextDiff::from_lines(old, generated);
    eprintln!("Diff for {path}:");
    for change in diff.iter_all_changes() {
        let sign = match change.tag() {
            ChangeTag::Delete => "-",
            ChangeTag::Insert => "+",
            ChangeTag::Equal => " ",
        };
        eprint!("{}{}", sign, change);
    }
    true
}

fn capi_enc_bindings<E: Enc>(
    template: &str,
    encs: &[E],
    templates: &Environment<'static>,
) -> String {
    let tmpl = templates.get_template(template).expect("missing template");
    let ub = encs.iter().any(|enc| enc.ub());
    let lb = encs.iter().any(|enc| enc.lb());
    tmpl.render(context!(encodings => encs, ub => ub, lb => lb))
        .expect("missing template context")
}

fn capi_tests<E: Enc>(
    id: &str,
    encs: &[E],
    templates: &Environment<'static>,
    do_check: bool,
) -> bool {
    let mut has_changes = false;
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
                    let generated = clang_format(
                        tmpl.render(context!(enc => enc))
                            .expect("missing template context"),
                    );
                    if do_check {
                        has_changes |= diff(&path, &generated);
                    } else {
                        write!(file(&path), "{generated}").unwrap();
                    }
                }
            }
        }
    }
    has_changes
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
fn capi_header(do_check: bool) -> bool {
    let mut temp_path = None;
    let path = if do_check {
        let path = NamedTempFile::new().unwrap().into_temp_path();
        std::fs::copy("capi/rustsat.h", &path).unwrap();
        temp_path = Some(path);
        temp_path.as_ref().unwrap().to_str().unwrap()
    } else {
        "capi/rustsat.h"
    };
    let changed = cbindgen::Builder::new()
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
        .write_to_file(path);
    if changed {
        let generated = std::fs::read(path).unwrap();
        let generated = std::str::from_utf8(&generated).unwrap();
        diff("capi/rustsat.h", generated);
    }
    drop(temp_path);
    changed
}

fn fuzz_enc<E: Enc>(template: &str, enc: &E, templates: &Environment<'static>) -> String {
    let tmpl = templates.get_template(template).expect("missing template");
    tmpl.render(context!(enc => enc))
        .expect("missing template context")
}

fn fuzz_toml<E: Enc>(
    path: &str,
    template: &str,
    encs: &[E],
    templates: &Environment<'static>,
) -> String {
    let mut rendered = String::new();
    for line in
        std::io::BufReader::new(std::fs::File::open(path).expect("could not open file")).lines()
    {
        let line = line.unwrap();
        rendered.push_str(&line);
        rendered.push('\n');
        if line == "# === CODEGEN ===" {
            break;
        }
    }
    let tmpl = templates.get_template(template).expect("missing template");
    rendered.push_str(
        &tmpl
            .render(context!(encodings => encs))
            .expect("missing template context"),
    );
    rendered
}
