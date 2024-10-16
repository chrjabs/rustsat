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

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();

    if std::env::var("DOCS_RS").is_ok() {
        // don't build c library on docs.rs due to network restrictions
        // instead, only generate bindings from included header file
        generate_bindings("csrc/dummy-kissat.h", "csrc/dummy-error.h", &out_dir);
        return;
    }

    // Select commit based on features. If conflict, always choose newest release
    let tag = if cfg!(feature = "v4-0-1") {
        "refs/tags/rel-4.0.1"
    } else if cfg!(feature = "v4-0-0") {
        "refs/tags/rel-4.0.0"
    } else if cfg!(feature = "v3-1-1") {
        "refs/tags/rel-3.1.1"
    } else if cfg!(feature = "v3-1-0") {
        "refs/tags/rel-3.1.0"
    } else if cfg!(feature = "v3-0-0") {
        "refs/tags/rel-3.0.0"
    } else if cfg!(feature = "sc2022-light") {
        "refs/tags/sc2022-light"
    } else if cfg!(feature = "sc2022-hyper") {
        "refs/tags/sc2022-hyper"
    } else if cfg!(feature = "sc2022-bulky") {
        "refs/tags/sc2022-bulky"
    } else {
        // default to newest version
        "refs/tags/rel-4.0.1"
    };

    // Build C library
    // Full commit hash needs to be provided
    build("https://github.com/arminbiere/kissat.git", "master", tag);

    // Built solver is in out_dir
    println!("cargo:rustc-link-search={out_dir}");
    println!("cargo:rustc-link-search={out_dir}/lib");
    println!("cargo:rustc-link-lib=static=kissat");

    // Generate Rust FFI bindings
    generate_bindings(
        &format!("{out_dir}/kissat/src/kissat.h"),
        &format!("{out_dir}/kissat/src/error.h"),
        &out_dir,
    );
}

/// Generates Rust FFI bindings
fn generate_bindings(main_header_path: &str, error_header_path: &str, out_dir: &str) {
    let bindings = bindgen::Builder::default()
        .header(main_header_path)
        .header(error_header_path)
        .blocklist_function("kissat_copyright")
        .blocklist_function("kissat_build")
        .blocklist_function("kissat_banner")
        .blocklist_function("kissat_has_configuration")
        .blocklist_function("kissat_error")
        .blocklist_function("kissat_fatal")
        .blocklist_function("kissat_fatal_message_start")
        .blocklist_function("kissat_abort")
        .generate()
        .expect("Unable to generate ffi bindings");
    bindings
        .write_to_file(PathBuf::from(out_dir).join("bindings.rs"))
        .expect("Could not write ffi bindings");
}

fn build(repo: &str, branch: &str, reference: &str) {
    let out_dir = env::var("OUT_DIR").unwrap();
    let mut kissat_dir_str = out_dir.clone();
    kissat_dir_str.push_str("/kissat");
    let kissat_dir = Path::new(&kissat_dir_str);
    if update_repo(kissat_dir, repo, branch, reference)
        || !Path::new(&out_dir).join("libkissat.a").exists()
    {
        // Repo changed, rebuild
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
        let mut build_header = File::create(kissat_dir.join("src").join("build.h"))
            .expect("Could not create kissat build header");
        let mut kissat_version =
            fs::read_to_string(kissat_dir.join("VERSION")).expect("Cannot read kissat version");
        kissat_version.retain(|c| c != '\n');
        let (compiler_desc, compiler_flags) =
            get_compiler_description(&kissat_build.get_compiler());
        write!(
                build_header,
                "#define VERSION \"{}\"\n#define COMPILER \"{} {}\"\n#define ID \"{}\"\n#define BUILD \"{}\"\n#define DIR \"{}\"",
                kissat_version, compiler_desc, compiler_flags, reference, chrono::Utc::now(), kissat_dir.as_os_str().to_str().unwrap()
            ).expect("Failed to write kissat build.h");
        // Build Kissat
        kissat_build
            .include(kissat_dir.join("src"))
            .warnings(false)
            .files(src_files)
            .compile("kissat");
    };
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

/// Gets a description of the C(++) compiler used and the used flags
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
