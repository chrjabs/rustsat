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

    #[cfg(feature = "git")]
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

    fn has_lrat(self) -> bool {
        self >= Version::V170
    }

    fn has_frat(self) -> bool {
        // NOTE: FRAT is technically supported since v1.7.0, but the options for requesting it differ
        self >= Version::V190
    }

    fn has_idrup(self) -> bool {
        self >= Version::V200
    }

    fn has_proof_tracer(self) -> bool {
        self >= Version::V200
    }

    fn set_defines(self, build: &mut cc::Build) {
        if !has_cpp_feature(CppFeature::FlexibleArrayMembers) {
            build.define("NFLEXIBLE", None);
        }
        if !has_cpp_feature(CppFeature::UnlockedIo) {
            build.define("NUNLOCKED", None);
        }
        if self >= Version::V211 && !has_cpp_feature(CppFeature::Closefrom) {
            build.define("NCLOSEFROM", None);
        }
        if self.has_flip() {
            build.define("FLIP", None);
        }
        if self.has_ilb() {
            build.define("ILB", None);
        }
        if self.has_reimply() {
            build.define("REIMPLY", None);
        }
        if self.has_ipasir_up() {
            build.define("IPASIRUP", None);
        }
        if self.has_propagate() {
            build.define("PROPAGATE", None);
        } else {
            build.define("PYSAT_PROPCHECK", None);
        }
        if self.has_proof_tracer() {
            build.define("TRACER", None);
        }
    }

    /// Sets custom `rustc` `--cfg` arguments for features only present in some version
    fn set_cfgs(self) {
        println!("cargo:rustc-check-cfg=cfg(cadical_feature, values(\"flip\", \"propagate\", \"pysat-propcheck\", \"lrat\", \"frat\", \"idrup\", \"proof-tracer\"))");
        if self.has_flip() {
            println!("cargo:rustc-cfg=cadical_feature=\"flip\"");
        }
        if self.has_propagate() {
            println!("cargo:rustc-cfg=cadical_feature=\"propagate\"");
        } else {
            println!("cargo:rustc-cfg=cadical_feature=\"pysat-propcheck\"");
        }
        if self.has_lrat() {
            println!("cargo:rustc-cfg=cadical_feature=\"lrat\"");
        }
        if self.has_frat() {
            println!("cargo:rustc-cfg=cadical_feature=\"frat\"");
        }
        if self.has_idrup() {
            println!("cargo:rustc-cfg=cadical_feature=\"idrup\"");
        }
        if self.has_proof_tracer() {
            println!("cargo:rustc-cfg=cadical_feature=\"proof-tracer\"");
        }
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

    generate_bindings(&cadical_dir, version, &out_dir);

    version.set_cfgs();
}

/// Generates Rust FFI bindings
fn generate_bindings(cadical_dir: &str, version: Version, out_dir: &str) {
    let header_path = format!("{cadical_dir}/src/ccadical.h");

    let bindings = bindgen::Builder::default()
        .rust_target("1.77.0".parse().unwrap()) // Set MSRV
        .clang_arg(format!("-I{cadical_dir}/src"))
        .clang_arg("-Icpp-extension")
        .allowlist_file(&header_path)
        .allowlist_file("cpp-extension/ccadical_extension.h")
        .blocklist_item("FILE")
        .blocklist_item("_IO_FILE")
        .blocklist_item("__sFILE")
        .blocklist_item("fpos_t")
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
    let bindings = if version.has_proof_tracer() {
        // in this case, `ccadical.h` is included from `ctracer.h`
        bindings
            .header("cpp-extension/ctracer.h")
            .allowlist_file("cpp-extension/ctracer.h")
    } else {
        bindings.header(&header_path)
    };
    #[cfg(not(feature = "tracing"))]
    let bindings = bindings.blocklist_function("ccadical_trace_api_calls");
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
    let bindings = if cfg!(feature = "tracing")
        || cfg!(feature = "debug") && env::var("PROFILE").unwrap() == "debug"
    {
        bindings
    } else {
        bindings.clang_arg("-DNTRACING")
    };
    let bindings = bindings
        .generate()
        .expect("Unable to generate ffi bindings");
    bindings
        .write_to_file(PathBuf::from(out_dir).join("bindings.rs"))
        .expect("Could not write ffi bindings");
}

fn get_cadical_dir(version: Version, _remote: Option<(&str, &str)>) -> String {
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

    #[cfg(feature = "git")]
    {
        let mut src_dir = env::var("OUT_DIR").unwrap();
        src_dir.push_str("/cadical");
        if let Some((repo, branch)) = _remote {
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
    #[cfg(not(feature = "git"))]
    unreachable!("non-default features enable the git feature")
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
                }
                Some(p)
            } else {
                None
            }
        });
    // Setup build configuration
    let mut cadical_build = default_build();
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
            .warnings(false);
        #[cfg(not(feature = "tracing"))]
        cadical_build.define("NTRACING", None); // --no-tracing
    }
    #[cfg(feature = "quiet")]
    cadical_build.define("QUIET", None); // --quiet
    #[cfg(feature = "logging")]
    cadical_build.define("LOGGING", None); // --log
    version.set_defines(&mut cadical_build);

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
        .files(src_files)
        .compile("cadical");
}

#[cfg(feature = "git")]
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
#[cfg(feature = "git")]
fn apply_patch<P: AsRef<Path>>(repo: &git2::Repository, patch: P) {
    use std::io::Read;

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

/// Gets a [`cc::Build`] with the default configuration applied
/// (used in main build and when checking Cpp features)
fn default_build() -> cc::Build {
    let mut build = cc::Build::new();
    build.cpp(true).std("c++11");
    build
}

#[derive(Clone, Copy, Debug)]
enum CppFeature {
    FlexibleArrayMembers,
    UnlockedIo,
    Closefrom,
}

const FLEXIBLE_ARRAY_MEMBERS_TEST: &str = r"
#include <cstdlib>
struct S {
  int size;
  int flexible_array_member[];
};
int main () {
  struct S * s = (struct S*) malloc (12);
  s->size = 2;
  s->flexible_array_member[0] = 1;
  s->flexible_array_member[1] = -1;
  int res = 0;
  for (int i = 0; i != s->size; i++)
    res += s->flexible_array_member[i];
  return res;
}
";

const UNLOCKED_IO_TEST: &str = r#"
#include <cstdio>
int main () {
  FILE * file = stdout;
  if (!file) return 1;
  if (putc_unlocked (42, file) != 42) return 1;
  if (fclose (file)) return 1;
  file = fopen (path, "r");
  if (!file) return 1;
  if (getc_unlocked (file) != 42) return 1;
  if (fclose (file)) return 1;
  return 0;
}
"#;

const CLOSEFROM_TEST: &str = r#"
extern "C" {
#include <unistd.h>
};
int main () {
  closefrom (0);
  return 0;
}
"#;

/// Checks whether a Cpp feature is available
///
/// The actual checks are taken from CaDiCaL's `configure` script
fn has_cpp_feature(feature: CppFeature) -> bool {
    let out_dir = env::var("OUT_DIR").unwrap();
    let (name, content) = match feature {
        CppFeature::FlexibleArrayMembers => {
            ("has-flexible-array-members", FLEXIBLE_ARRAY_MEMBERS_TEST)
        }
        CppFeature::UnlockedIo => ("has-unlocked-io", UNLOCKED_IO_TEST),
        CppFeature::Closefrom => ("has-closefrom", CLOSEFROM_TEST),
    };

    // write test to file
    let test_file = format!("{out_dir}/{name}.cpp");
    {
        let mut test_file = fs::File::create(&test_file).expect("cannot open test file");
        write!(test_file, "{content}").expect("failed to write test file");
    }

    // compile and run test
    let out_file = format!("{out_dir}/{name}.out");
    let mut compile = default_build().get_compiler().to_command();
    let compile = compile
        .current_dir(out_dir)
        .args([&test_file, "-o", &out_file])
        .output()
        .expect("failed to run test compilation");
    if !compile.status.success() {
        return false;
    }
    let output = Command::new(out_file)
        .output()
        .expect("failed to execute compiled test");
    output.status.success()
}
