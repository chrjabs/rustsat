#![warn(clippy::pedantic)]

use glob::glob;
use std::{
    env,
    fs::{self, File},
    io::Write,
    path::{Path, PathBuf},
    process::Command,
    str,
};

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Version {
    // Note: derived order makes top < bottom
    Sc2022Bulky,
    Sc2022Hyper,
    Sc2022Light,
    V300,
    V310,
    V311,
    V400,
    V401,
    #[default]
    V402,
}

/// Checks if the version was set manually via a feature
macro_rules! version_set_manually {
    () => {
        cfg!(any(
            feature = "v4-0-2",
            feature = "v4-0-1",
            feature = "v4-0-0",
            feature = "v3-1-1",
            feature = "v3-1-0",
            feature = "v3-0-0",
            feature = "sc2022-light",
            feature = "sc2022-hyper",
            feature = "sc2022-bulky",
        ))
    };
}

impl Version {
    fn determine() -> Self {
        if cfg!(feature = "v4-0-2") {
            Version::V402
        } else if cfg!(feature = "v4-0-1") {
            Version::V401
        } else if cfg!(feature = "v4-0-0") {
            Version::V400
        } else if cfg!(feature = "v3-1-1") {
            Version::V311
        } else if cfg!(feature = "v3-1-0") {
            Version::V310
        } else if cfg!(feature = "v3-0-0") {
            Version::V300
        } else if cfg!(feature = "sc2022-light") {
            Version::Sc2022Light
        } else if cfg!(feature = "sc2022-hyper") {
            Version::Sc2022Hyper
        } else if cfg!(feature = "sc2022-bulky") {
            Version::Sc2022Bulky
        } else {
            // default to newest version
            Version::default()
        }
    }

    fn reference(self) -> &'static str {
        match self {
            Version::Sc2022Bulky => "refs/tags/sc2022-bulky",
            Version::Sc2022Hyper => "refs/tags/sc2022-hyper",
            Version::Sc2022Light => "refs/tags/sc2022-light",
            Version::V300 => "refs/tags/rel-3.0.0",
            Version::V310 => "refs/tags/rel-3.1.0",
            Version::V311 => "refs/tags/rel-3.1.1",
            Version::V400 => "refs/tags/rel-4.0.0",
            Version::V401 => "refs/tags/rel-4.0.1",
            Version::V402 => "refs/tags/rel-4.0.2",
        }
    }
}

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();

    let version = Version::determine();

    // Build C library
    let kissat_src_dir = build(version);

    // Built solver is in out_dir
    println!("cargo:rustc-link-search={out_dir}");
    println!("cargo:rustc-link-search={out_dir}/lib");
    println!("cargo:rustc-link-lib=static=kissat");

    // Generate Rust FFI bindings
    generate_bindings(&kissat_src_dir, &out_dir);
}

fn get_kissat_src(version: Version) -> PathBuf {
    if let Ok(src_dir) = std::env::var("KISSAT_SRC_DIR") {
        if version_set_manually!() {
            println!("cargo:warning=Both version feature and KISSAT_SRC_DIR. Will ignore version feature");
        }
        return PathBuf::from(src_dir);
    }

    if version == Version::default() {
        // the sources for the default version are included with the crate and do not need to be
        // cloned
        return PathBuf::from("csrc");
    }
    let mut kissat_src_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    kissat_src_dir.push("kissat");
    update_repo(
        &kissat_src_dir,
        "https://github.com/arminbiere/kissat.git",
        "master",
        version.reference(),
    );
    kissat_src_dir
}

/// Generates Rust FFI bindings
fn generate_bindings(kissat_src_dir: &Path, out_dir: &str) {
    let bindings = bindgen::Builder::default()
        .rust_target("1.66.1".parse().unwrap()) // Set MSRV of RustSAT
        .header(
            kissat_src_dir
                .join("src")
                .join("kissat.h")
                .to_str()
                .unwrap(),
        )
        .header(kissat_src_dir.join("src").join("error.h").to_str().unwrap())
        .blocklist_function("kissat_copyright")
        .blocklist_function("kissat_build")
        .blocklist_function("kissat_banner")
        .blocklist_function("kissat_has_configuration")
        .blocklist_function("kissat_error")
        .blocklist_function("kissat_fatal")
        .blocklist_function("kissat_fatal_message_start")
        .blocklist_function("kissat_abort")
        .blocklist_function("kissat_set_prefix")
        .generate()
        .expect("Unable to generate ffi bindings");
    bindings
        .write_to_file(PathBuf::from(out_dir).join("bindings.rs"))
        .expect("Could not write ffi bindings");
}

fn build(version: Version) -> PathBuf {
    let kissat_src_dir = get_kissat_src(version);
    let kissat_dir_str = kissat_src_dir.to_str().unwrap();

    // We specify the build manually here instead of calling make for better portability
    let src_files = glob(&format!("{kissat_dir_str}/src/*.c"))
        .unwrap()
        .filter_map(|res| {
            if let Ok(p) = res {
                if let Some(name) = p.file_name() {
                    if name == "main.c"
                        || name == "application.c"
                        || name == "handle.c"
                        || name == "parse.c"
                        || name == "witness.c"
                    {
                        return None; // Filter out application files
                    }
                };
                Some(p)
            } else {
                None
            }
        });
    // Setup build configuration
    let mut kissat_build = cc::Build::new();
    if cfg!(feature = "debug") && env::var("PROFILE").unwrap() == "debug" {
        kissat_build
            .opt_level(0)
            .define("DEBUG", None)
            .warnings(true)
            .debug(true);
    } else {
        kissat_build
            .opt_level(3)
            .define("NDEBUG", None)
            .warnings(false);
    }
    #[cfg(feature = "safe")]
    kissat_build.define("SAFE", None); // --safe
    #[cfg(feature = "quiet")]
    kissat_build.define("QUIET", None); // --quiet

    // Generate build header
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let mut build_header =
        File::create(out_dir.join("build.h")).expect("Could not create kissat build header");
    let mut kissat_version =
        fs::read_to_string(kissat_src_dir.join("VERSION")).expect("Cannot read kissat version");
    kissat_version.retain(|c| c != '\n');
    let (compiler_desc, compiler_flags) = get_compiler_description(&kissat_build.get_compiler());
    write!(
                build_header,
                "#define VERSION \"{}\"\n#define COMPILER \"{} {}\"\n#define ID \"{}\"\n#define BUILD \"{}\"\n#define DIR \"{}\"",
                kissat_version, compiler_desc, compiler_flags, version.reference(), chrono::Utc::now(), kissat_dir_str
            ).expect("Failed to write kissat build.h");
    // Build Kissat
    kissat_build
        .include(kissat_src_dir.join("src"))
        .include(out_dir)
        .warnings(false)
        .files(src_files)
        .compile("kissat");

    kissat_src_dir
}

/// Returns true if there were changes, false if not
fn update_repo(path: &Path, url: &str, branch: &str, reference: &str) -> bool {
    let mut changed = false;
    let repo = if let Ok(repo) = git2::Repository::open(path) {
        if repo.find_reference(reference).is_err() {
            // Fetch repo
            let mut remote = repo
                .find_remote("origin")
                .unwrap_or_else(|e| panic!("Expected remote \"origin\" in git repo {path:?}: {e}"));
            remote.fetch(&[branch], None, None).unwrap_or_else(|e| {
                panic!("Could not fetch \"origin/{branch}\" for git repo {path:?}: {e}")
            });
            drop(remote);
            changed = true;
        }
        repo
    } else {
        if path.exists() {
            fs::remove_dir_all(path).unwrap_or_else(|e| {
                panic!(
                    "Could not delete directory {}: {}",
                    path.to_str().unwrap(),
                    e
                )
            });
        };
        changed = true;
        git2::Repository::clone(url, path)
            .unwrap_or_else(|e| panic!("Could not clone repository {url}: {e}"))
    };
    let target_commit = repo
        .find_reference(reference)
        .expect("could not find specified reference")
        .peel_to_commit()
        .expect("could not peel to commit");
    repo.checkout_tree(
        target_commit.as_object(),
        Some(git2::build::CheckoutBuilder::new().force()),
    )
    .expect("could not checkout commit");
    repo.set_head_detached(target_commit.id())
        .expect("could not detach head");
    changed
}

/// Gets a description of the C(pp) compiler used and the used flags
fn get_compiler_description(compiler: &cc::Tool) -> (String, String) {
    let compiler_command = compiler.to_command();
    let mut first_line = true;
    let compiler_version = match Command::new(compiler_command.get_program())
        .arg("--version")
        .output()
    {
        Ok(output) => {
            let mut version = String::from_utf8(output.stdout).unwrap();
            version.retain(|c| {
                if first_line && c == '\n' {
                    first_line = false;
                    false
                } else {
                    first_line
                }
            });
            version
        }
        Err(_) => String::from(compiler_command.get_program().to_str().unwrap()),
    };
    let compiler_flags = compiler.cflags_env();
    (
        compiler_version,
        String::from(compiler_flags.to_str().unwrap()),
    )
}
