use git2::Repository;
use glob::glob;
use std::{
    env,
    fs::{self, File},
    io::{Read, Write},
    path::Path,
    process::Command,
    str,
};

fn main() {
    if std::env::var("DOCS_RS").is_ok() {
        // don't build c++ library on docs.rs due to network restrictions
        return;
    }

    #[cfg(all(feature = "quiet", feature = "logging"))]
    compile_error!("cannot combine cadical features quiet and logging");

    // Select commit based on features. If conflict, always choose newest release
    let (tag, patch) = if cfg!(feature = "v1-9-5") {
        ("refs/tags/rel-1.9.5", "patches/v192.patch")
    } else if cfg!(feature = "v1-9-4") {
        ("refs/tags/rel-1.9.4", "patches/v192.patch")
    } else if cfg!(feature = "v1-9-3") {
        ("refs/tags/rel-1.9.3", "patches/v192.patch")
    } else if cfg!(feature = "v1-9-2") {
        ("refs/tags/rel-1.9.2", "patches/v192.patch")
    } else if cfg!(feature = "v1-9-1") {
        ("refs/tags/rel-1.9.1", "patches/v190.patch")
    } else if cfg!(feature = "v1-9-0") {
        ("refs/tags/rel-1.9.0", "patches/v190.patch")
    } else if cfg!(feature = "v1-8-0") {
        ("refs/tags/rel-1.8.0", "patches/v180.patch")
    } else if cfg!(feature = "v1-7-5") {
        ("refs/tags/rel-1.7.5", "patches/v171.patch")
    } else if cfg!(feature = "v1-7-4") {
        ("refs/tags/rel-1.7.4", "patches/v171.patch")
    } else if cfg!(feature = "v1-7-3") {
        ("refs/tags/rel-1.7.3", "patches/v171.patch")
    } else if cfg!(feature = "v1-7-2") {
        ("refs/tags/rel-1.7.2", "patches/v171.patch")
    } else if cfg!(feature = "v1-7-1") {
        ("refs/tags/rel-1.7.1", "patches/v171.patch")
    } else if cfg!(feature = "v1-7-0") {
        ("refs/tags/rel-1.7.0", "patches/v170.patch")
    } else if cfg!(feature = "v1-6-0") {
        ("refs/tags/rel-1.6.0", "patches/v160.patch")
    } else if cfg!(feature = "v1-5-6") {
        ("refs/tags/rel-1.5.6", "patches/v156.patch")
    } else if cfg!(feature = "v1-5-5") {
        ("refs/tags/rel-1.5.5", "patches/v154.patch")
    } else if cfg!(feature = "v1-5-4") {
        ("refs/tags/rel-1.5.4", "patches/v154.patch")
    } else if cfg!(feature = "v1-5-3") {
        ("refs/tags/rel-1.5.3", "patches/v150.patch")
    } else if cfg!(feature = "v1-5-2") {
        ("refs/tags/rel-1.5.2", "patches/v150.patch")
    } else if cfg!(feature = "v1-5-1") {
        ("refs/tags/rel-1.5.1", "patches/v150.patch")
    } else if cfg!(feature = "v1-5-0") {
        ("refs/tags/rel-1.5.0", "patches/v150.patch")
    } else {
        // default to newest version
        ("refs/tags/rel-1.9.5", "patches/v192.patch")
    };

    // Build C++ library
    build(
        "https://github.com/arminbiere/cadical.git",
        "master",
        tag,
        patch,
    );

    let out_dir = env::var("OUT_DIR").unwrap();

    #[cfg(target_os = "macos")]
    println!("cargo:rustc-flags=-l dylib=c++");

    #[cfg(not(target_os = "macos"))]
    println!("cargo:rustc-flags=-l dylib=stdc++");

    // Built solver is in out_dir
    println!("cargo:rustc-link-search={}", out_dir);
    println!("cargo:rustc-link-search={}/lib", out_dir);
}

fn build(repo: &str, branch: &str, reference: &str, patch: &str) {
    let out_dir = env::var("OUT_DIR").unwrap();
    let mut cadical_dir_str = out_dir.clone();
    cadical_dir_str.push_str("/cadical");
    let cadical_dir = Path::new(&cadical_dir_str);
    if update_repo(cadical_dir, repo, branch, reference, patch)
        || !Path::new(&out_dir).join("libcadical.a").exists()
    {
        // Repo changed, rebuild
        // We specify the build manually here instead of calling make for better portability
        let src_files = glob(&format!("{}/src/*.cpp", cadical_dir_str))
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
                .debug(true)
                .define("NCONTRACTS", None) // --no-contracts
                .define("NTRACING", None); // --no-tracing
        } else {
            cadical_build
                .opt_level(3)
                .define("NDEBUG", None)
                .warnings(false);
        }
        #[cfg(feature = "quiet")]
        cadical_build.define("QUIET", None); // --quiet
        #[cfg(feature = "logging")]
        cadical_build.define("LOGGING", None); // --log

        // Generate build header
        let mut build_header = File::create(cadical_dir.join("src").join("build.hpp"))
            .expect("Could not create kissat CaDiCaL header");
        let mut cadical_version =
            fs::read_to_string(cadical_dir.join("VERSION")).expect("Cannot read CaDiCaL version");
        cadical_version.retain(|c| c != '\n');
        let (compiler_desc, compiler_flags) =
            get_compiler_description(cadical_build.get_compiler());
        write!(
                build_header,
                "#define VERSION \"{}\"\n#define IDENTIFIER \"{}\"\n#define COMPILER \"{}\"\n#define FLAGS \"{}\"\n#define DATE \"{}\"",
                cadical_version, reference, compiler_desc, compiler_flags, chrono::Utc::now()
            ).expect("Failed to write CaDiCaL build.hpp");
        // Build CaDiCaL
        cadical_build
            .include(cadical_dir.join("src"))
            .warnings(false)
            .files(src_files)
            .compile("cadical");
    };
}

/// Returns true if there were changes, false if not
fn update_repo(path: &Path, url: &str, branch: &str, reference: &str, patch: &str) -> bool {
    let mut changed = false;
    let repo = match git2::Repository::open(path) {
        Ok(repo) => {
            if repo.find_reference(reference).is_err() {
                // Fetch repo
                let mut remote = repo.find_remote("origin").unwrap_or_else(|e| {
                    panic!("Expected remote \"origin\" in git repo {:?}: {}", path, e)
                });
                remote.fetch(&[branch], None, None).unwrap_or_else(|e| {
                    panic!(
                        "Could not fetch \"origin/{}\" for git repo {:?}: {}",
                        branch, path, e
                    )
                });
                drop(remote);
                changed = true;
            }
            repo
        }
        Err(_) => {
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
                .unwrap_or_else(|e| panic!("Could not clone repository {}: {}", url, e))
        }
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

    changed
}

/// Applies a patch to the repo
fn apply_patch(repo: &Repository, patch: &str) {
    let mut f = File::open(patch).unwrap();
    let mut buffer = Vec::new();
    f.read_to_end(&mut buffer).unwrap();
    let patch = git2::Diff::from_buffer(&buffer).unwrap();
    repo.apply(&patch, git2::ApplyLocation::WorkDir, None)
        .unwrap();
}

/// Gets a description of the C(++) compiler used and the used flags
fn get_compiler_description(compiler: cc::Tool) -> (String, String) {
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
