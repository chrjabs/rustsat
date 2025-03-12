#![warn(clippy::pedantic)]

use git2::Repository;
use glob::glob;
use std::{
    env,
    fs::{self, File},
    io::{Read, Write},
    path::{Path, PathBuf},
    process::Command,
    str,
};

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Version {
    // Note: derived order makes top < bottom
    V150,
    V151,
    V152,
    V153,
    V154,
    V155,
    V156,
    V160,
    V170,
    V171,
    V172,
    V173,
    V174,
    V175,
    V180,
    V190,
    V191,
    V192,
    V193,
    V194,
    V195,
    V200,
    V210,
    V211,
    V212,
    #[default]
    V213,
    // Don't forget to update the crate documentation when adding a newer version
}

/// Checks if the version was set manually via a feature
macro_rules! version_set_manually {
    () => {
        cfg!(any(
            feature = "v2-1-3",
            feature = "v2-1-2",
            feature = "v2-1-1",
            feature = "v2-1-0",
            feature = "v2-0-0",
            feature = "v1-9-5",
            feature = "v1-9-4",
            feature = "v1-9-3",
            feature = "v1-9-2",
            feature = "v1-9-1",
            feature = "v1-9-0",
            feature = "v1-8-0",
            feature = "v1-7-5",
            feature = "v1-7-4",
            feature = "v1-7-3",
            feature = "v1-7-2",
            feature = "v1-7-1",
            feature = "v1-7-0",
            feature = "v1-6-0",
            feature = "v1-5-6",
            feature = "v1-5-5",
            feature = "v1-5-4",
            feature = "v1-5-3",
            feature = "v1-5-2",
            feature = "v1-5-1",
            feature = "v1-5-0",
        ))
    };
}

impl Version {
    fn determine() -> Self {
        if cfg!(feature = "v2-1-3") {
            Version::V213
        } else if cfg!(feature = "v2-1-2") {
            Version::V212
        } else if cfg!(feature = "v2-1-1") {
            Version::V211
        } else if cfg!(feature = "v2-1-0") {
            Version::V210
        } else if cfg!(feature = "v2-0-0") {
            Version::V200
        } else if cfg!(feature = "v1-9-5") {
            Version::V195
        } else if cfg!(feature = "v1-9-4") {
            Version::V194
        } else if cfg!(feature = "v1-9-3") {
            Version::V193
        } else if cfg!(feature = "v1-9-2") {
            Version::V192
        } else if cfg!(feature = "v1-9-1") {
            Version::V191
        } else if cfg!(feature = "v1-9-0") {
            Version::V190
        } else if cfg!(feature = "v1-8-0") {
            Version::V180
        } else if cfg!(feature = "v1-7-5") {
            Version::V175
        } else if cfg!(feature = "v1-7-4") {
            Version::V174
        } else if cfg!(feature = "v1-7-3") {
            Version::V173
        } else if cfg!(feature = "v1-7-2") {
            Version::V172
        } else if cfg!(feature = "v1-7-1") {
            Version::V171
        } else if cfg!(feature = "v1-7-0") {
            Version::V170
        } else if cfg!(feature = "v1-6-0") {
            Version::V160
        } else if cfg!(feature = "v1-5-6") {
            Version::V156
        } else if cfg!(feature = "v1-5-5") {
            Version::V155
        } else if cfg!(feature = "v1-5-4") {
            Version::V154
        } else if cfg!(feature = "v1-5-3") {
            Version::V153
        } else if cfg!(feature = "v1-5-2") {
            Version::V152
        } else if cfg!(feature = "v1-5-1") {
            Version::V151
        } else if cfg!(feature = "v1-5-0") {
            Version::V150
        } else {
            // default to newest version
            Version::default()
        }
    }

    fn reference(self) -> &'static str {
        match self {
            Version::V150 => "refs/tags/rel-1.5.0",
            Version::V151 => "refs/tags/rel-1.5.1",
            Version::V152 => "refs/tags/rel-1.5.2",
            Version::V153 => "refs/tags/rel-1.5.3",
            Version::V154 => "refs/tags/rel-1.5.4",
            Version::V155 => "refs/tags/rel-1.5.5",
            Version::V156 => "refs/tags/rel-1.5.6",
            Version::V160 => "refs/tags/rel-1.6.0",
            Version::V170 => "refs/tags/rel-1.7.0",
            Version::V171 => "refs/tags/rel-1.7.1",
            Version::V172 => "refs/tags/rel-1.7.2",
            Version::V173 => "refs/tags/rel-1.7.3",
            Version::V174 => "refs/tags/rel-1.7.4",
            Version::V175 => "refs/tags/rel-1.7.5",
            Version::V180 => "refs/tags/rel-1.8.0",
            Version::V190 => "refs/tags/rel-1.9.0",
            Version::V191 => "refs/tags/rel-1.9.1",
            Version::V192 => "refs/tags/rel-1.9.2",
            Version::V193 => "refs/tags/rel-1.9.3",
            Version::V194 => "refs/tags/rel-1.9.4",
            Version::V195 => "refs/tags/rel-1.9.5",
            Version::V200 => "refs/tags/rel-2.0.0",
            Version::V210 => "refs/tags/rel-2.1.0",
            Version::V211 => "refs/tags/rel-2.1.1",
            Version::V212 => "refs/tags/rel-2.1.2",
            Version::V213 => "refs/tags/rel-2.1.3",
        }
    }

    fn patch(self) -> &'static str {
        #![allow(clippy::enum_glob_use)]
        use Version::*;
        match self {
            V150 | V151 | V152 | V153 => "v150.patch",
            V154 | V155 => "v154.patch",
            V156 => "v156.patch",
            V160 => "v160.patch",
            V170 => "v170.patch",
            V171 | V172 | V173 | V174 | V175 => "v171.patch",
            V180 => "v180.patch",
            V190 | V191 => "v190.patch",
            V192 | V193 | V194 | V195 => "v192.patch",
            V200 => "v200.patch",
            V210 => "v210.patch",
            V211 | V212 => "v211.patch",
            V213 => "v213.patch",
        }
    }

    fn has_flip(self) -> bool {
        self >= Version::V154
    }

    fn has_ilb(self) -> bool {
        self >= Version::V190
    }

    fn has_reimply(self) -> bool {
        self >= Version::V190 && self < Version::V194
    }

    fn has_ipasir_up(self) -> bool {
        self >= Version::V160
    }

    fn has_propagate(self) -> bool {
        self >= Version::V213
    }
}

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();

    let version = Version::determine();

    #[cfg(all(feature = "quiet", feature = "logging"))]
    compile_error!("cannot combine cadical features quiet and logging");

    // Build C++ library
    build(
        "https://github.com/arminbiere/cadical.git",
        "master",
        version,
    );

    // Built solver is in out_dir
    println!("cargo:rustc-link-search={out_dir}");
    println!("cargo:rustc-link-search={out_dir}/lib");
    println!("cargo:rustc-link-lib=static=cadical");

    // Link c++ std lib
    // Note: this should be _after_ linking the solver itself so that it is actually pulled in
    #[cfg(target_os = "macos")]
    println!("cargo:rustc-link-lib=dylib=c++");
    #[cfg(not(any(target_os = "macos", target_os = "windows")))]
    println!("cargo:rustc-link-lib=dylib=stdc++");

    for ext in ["h", "cpp"] {
        for file in glob(&format!("cpp-extension/*.{ext}")).unwrap() {
            println!("cargo:rerun-if-changed={}", file.unwrap().display());
        }
    }

    let cadical_dir = get_cadical_dir(version, None);

    generate_bindings(&format!("{cadical_dir}/src/ccadical.h"), version, &out_dir);

    // Set custom configs for features only present in some version
    println!("cargo:rustc-check-cfg=cfg(cadical_feature, values(\"flip\", \"propagate\", \"pysat-propcheck\"))");
    if version.has_flip() {
        println!("cargo:rustc-cfg=cadical_feature=\"flip\"");
    }
    if version.has_propagate() {
        println!("cargo:rustc-cfg=cadical_feature=\"propagate\"");
    } else {
        println!("cargo:rustc-cfg=cadical_feature=\"pysat-propcheck\"");
    }
}

/// Generates Rust FFI bindings
fn generate_bindings(header_path: &str, version: Version, out_dir: &str) {
    let bindings = bindgen::Builder::default()
        .rust_target("1.70.0".parse().unwrap()) // Set MSRV of RustSAT
        .clang_arg("-Icpp-extension")
        .header(header_path)
        .allowlist_file(header_path)
        .allowlist_file("cpp-extension/ccadical_extension.h")
        .blocklist_item("FILE")
        .blocklist_function("ccadical_add")
        .blocklist_function("ccadical_assume")
        .blocklist_function("ccadical_solve")
        .blocklist_function("ccadical_constrain")
        .blocklist_function("ccadical_set_option")
        .blocklist_function("ccadical_limit")
        .blocklist_function("ccadical_trace_proof")
        .blocklist_function("ccadical_close_proof")
        .blocklist_function("ccadical_conclude")
        .blocklist_function("ccadical_simplify");
    let bindings = if version.has_flip() {
        bindings.clang_arg("-DFLIP")
    } else {
        bindings
    };
    let bindings = if version.has_propagate() {
        bindings.clang_arg("-DPROPAGATE")
    } else {
        bindings.clang_arg("-DPYSAT_PROPCHECK")
    };
    let bindings = bindings
        .generate()
        .expect("Unable to generate ffi bindings");
    bindings
        .write_to_file(PathBuf::from(out_dir).join("bindings.rs"))
        .expect("Could not write ffi bindings");
}

fn get_cadical_dir(version: Version, remote: Option<(&str, &str)>) -> String {
    if let Ok(src_dir) = std::env::var("CADICAL_SRC_DIR") {
        if version_set_manually!() {
            println!("cargo:warning=Both version feature and CADICAL_SRC_DIR. It is your responsibility to ensure that they make sense together.");
        }
        return src_dir;
    }

    if version == Version::default() {
        // the sources for the default version are included with the crate and do not need to be
        // cloned
        return String::from("cppsrc");
    }

    let mut src_dir = env::var("OUT_DIR").unwrap();
    src_dir.push_str("/cadical");
    if let Some((repo, branch)) = remote {
        update_repo(
            Path::new(&src_dir),
            repo,
            branch,
            version.reference(),
            Path::new("patches").join(version.patch()),
        );
    }
    src_dir
}

fn build(repo: &str, branch: &str, version: Version) {
    let cadical_dir_str = get_cadical_dir(version, Some((repo, branch)));
    let cadical_dir = Path::new(&cadical_dir_str);
    // We specify the build manually here instead of calling make for better portability
    let src_files = glob(&format!("{cadical_dir_str}/src/*.cpp"))
        .unwrap()
        .filter_map(|res| {
            if let Ok(p) = res {
                if let Some(name) = p.file_name() {
                    if name == "cadical.cpp" || name == "mobical.cpp" || name == "ipasir.cpp" {
                        return None; // Filter out application files and IPASIR interface
                    }
                };
                Some(p)
            } else {
                None
            }
        });
    // Setup build configuration
    let mut cadical_build = cc::Build::new();
    cadical_build.cpp(true).std("c++11");
    if cfg!(feature = "debug") && env::var("PROFILE").unwrap() == "debug" {
        cadical_build
            .opt_level(0)
            .define("DEBUG", None)
            .warnings(true)
            .debug(true);
    } else {
        cadical_build
            .opt_level(3)
            .define("NDEBUG", None)
            .define("NCONTRACTS", None) // --no-contracts
            .define("NTRACING", None) // --no-tracing
            .warnings(false);
    }
    #[cfg(feature = "quiet")]
    cadical_build.define("QUIET", None); // --quiet
    #[cfg(feature = "logging")]
    cadical_build.define("LOGGING", None); // --log
    if version >= Version::V211 && cfg!(target_os = "macos") {
        cadical_build.define("NCLOSEFROM", None);
    }
    if version.has_flip() {
        cadical_build.define("FLIP", None);
    }
    if version.has_ilb() {
        cadical_build.define("ILB", None);
    }
    if version.has_reimply() {
        cadical_build.define("REIMPLY", None);
    }
    if version.has_ipasir_up() {
        cadical_build.define("IPASIRUP", None);
    }
    if version.has_propagate() {
        cadical_build.define("PROPAGATE", None);
    } else {
        cadical_build.define("PYSAT_PROPCHECK", None);
    }

    let out_dir = std::env::var("OUT_DIR").unwrap();
    let out_dir = Path::new(&out_dir);

    // Generate build header
    let mut build_header =
        File::create(out_dir.join("build.hpp")).expect("Could not create CaDiCaL header");
    let mut cadical_version =
        fs::read_to_string(cadical_dir.join("VERSION")).expect("Cannot read CaDiCaL version");
    cadical_version.retain(|c| c != '\n');
    let (compiler_desc, compiler_flags) = get_compiler_description(&cadical_build.get_compiler());
    write!(
                build_header,
                "#define VERSION \"{}\"\n#define IDENTIFIER \"{}\"\n#define COMPILER \"{}\"\n#define FLAGS \"{}\"\n#define DATE \"{}\"",
                cadical_version, version.reference(), compiler_desc, compiler_flags, chrono::Utc::now()
            ).expect("Failed to write CaDiCaL build.hpp");
    // Build CaDiCaL
    cadical_build
        .include(out_dir)
        .include(cadical_dir.join("src"))
        .include("cpp-extension")
        .warnings(false)
        .files(src_files)
        .compile("cadical");
}

fn update_repo(repo_path: &Path, url: &str, branch: &str, reference: &str, patch: PathBuf) {
    let repo = if let Ok(repo) = git2::Repository::open(repo_path) {
        if repo.find_reference(reference).is_err() {
            // Fetch repo
            let mut remote = repo.find_remote("origin").unwrap_or_else(|e| {
                panic!("Expected remote \"origin\" in git repo {repo_path:?}: {e}",)
            });
            remote.fetch(&[branch], None, None).unwrap_or_else(|e| {
                panic!("Could not fetch \"origin/{branch}\" for git repo {repo_path:?}: {e}")
            });
            drop(remote);
        }
        repo
    } else {
        if repo_path.exists() {
            fs::remove_dir_all(repo_path).unwrap_or_else(|e| {
                panic!(
                    "Could not delete directory {}: {}",
                    repo_path.to_str().unwrap(),
                    e
                )
            });
        };
        git2::Repository::clone(url, repo_path)
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

    apply_patch(&repo, patch);

    // Allow for manually applying patches
    if let Ok(patches) = std::env::var("CADICAL_PATCHES") {
        for patch in patches.split(':') {
            apply_patch(&repo, patch);
        }
    }
}

/// Applies a patch to the repository
fn apply_patch<P: AsRef<Path>>(repo: &Repository, patch: P) {
    let mut f = File::open(patch).unwrap();
    let mut buffer = Vec::new();
    f.read_to_end(&mut buffer).unwrap();
    let patch = git2::Diff::from_buffer(&buffer).unwrap();
    repo.apply(&patch, git2::ApplyLocation::WorkDir, None)
        .unwrap();
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
