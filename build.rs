use glob::glob;
use std::{
    env,
    fs::{self, File},
    io::Write,
    path::Path,
    process::Command,
    str,
};

fn main() {
    // Build external solver dependencies
    // Full commit hashes need to be provided
    build_cadical(
        "https://github.com/chrjabs/cadical.git",
        "0fe57b6945f1db37bb0e1adb64d24056035c3bbb",
    );
    build_kissat(
        "https://github.com/arminbiere/kissat.git",
        "97917ddf2b12adc6f63c7b2a5a403a1ee7d81836",
    );

    let out_dir = env::var("OUT_DIR").unwrap();

    // All built solvers are there
    println!("cargo:rustc-link-search={}", out_dir);
}

fn build_cadical(repo: &str, commit: &str) {
    #[cfg(feature = "cadical")]
    {
        let out_dir = env::var("OUT_DIR").unwrap();
        let mut cadical_dir_str = out_dir.clone();
        cadical_dir_str.push_str("/cadical");
        let cadical_dir = Path::new(&cadical_dir_str);
        if update_repo(cadical_dir, repo, commit)
            || !Path::new(&out_dir).join("libcadical.a").exists()
        {
            // Repo changed, rebuild
            // We specify the build manually here instead of calling make for better portability
            let src_files = glob(&format!("{}/src/*.cpp", cadical_dir_str))
                .unwrap()
                .into_iter()
                .filter_map(|res| {
                    if let Ok(p) = res {
                        if let Some(name) = p.file_name() {
                            if name == "cadical.cpp" || name == "mobical.cpp" {
                                return None; // Filter out application files
                            }
                        };
                        Some(p)
                    } else {
                        None
                    }
                });
            cc::Build::new()
                .cpp(true)
                .opt_level(3)
                .define("NDEBUG", None)
                .define("NBUILD", None) // Build without build.hpp
                .include(cadical_dir.join("src"))
                .warnings(false)
                .files(src_files)
                .compile("cadical");
        };

        println!("cargo:rustc-link-lib=static=cadical");

        #[cfg(target_os = "macos")]
        println!("cargo:rustc-flags=-l dylib=c++");

        #[cfg(not(target_os = "macos"))]
        println!("cargo:rustc-flags=-l dylib=stdc++");
    }
}

fn build_kissat(repo: &str, commit: &str) {
    #[cfg(feature = "kissat")]
    {
        let out_dir = env::var("OUT_DIR").unwrap();
        let mut kissat_dir_str = out_dir.clone();
        kissat_dir_str.push_str("/kissat");
        let kissat_dir = Path::new(&kissat_dir_str);
        if update_repo(kissat_dir, repo, commit)
            || !Path::new(&out_dir).join("libkissat.a").exists()
        {
            // Repo changed, rebuild
            // We specify the build manually here instead of calling make for better portability
            let src_files = glob(&format!("{}/src/*.c", kissat_dir_str))
                .unwrap()
                .into_iter()
                .filter_map(|res| {
                    if let Ok(p) = res {
                        if let Some(name) = p.file_name() {
                            if name == "application.c"
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
            kissat_build.opt_level(3).define("NDEBUG", None);
            // Generate build header
            let mut build_header = File::create(kissat_dir.join("src").join("build.h"))
                .expect("Could not create kissat build header");
            let mut kissat_version =
                fs::read_to_string(kissat_dir.join("VERSION")).expect("Cannot read kissat version");
            kissat_version.retain(|c| c != '\n');
            let compiler_desc = get_compiler_description(kissat_build.get_compiler());
            write!(
                build_header,
                "#define VERSION \"{}\"\n#define COMPILER \"{}\"\n#define ID \"{}\"\n#define BUILD \"{}\"\n#define DIR \"{}\"",
                kissat_version, compiler_desc, commit, chrono::Utc::now(), kissat_dir.as_os_str().to_str().unwrap()
            ).expect("Failed to write kissat build.h");
            kissat_build
                .include(kissat_dir.join("src"))
                .warnings(false)
                .files(src_files)
                .compile("kissat");
        };

        println!("cargo:rustc-link-lib=static=kissat");
    }
}

/// Returns true if there were changes, false if not
fn update_repo(path: &Path, url: &str, commit: &str) -> bool {
    let mut changed = false;
    let repo = match git2::Repository::open(path) {
        Ok(repo) => repo,
        Err(_) => {
            if path.exists() {
                fs::remove_dir_all(path).unwrap_or_else(|_| {
                    panic!("Could not delete directory: {}", path.to_str().unwrap())
                });
            };
            changed = true;
            git2::Repository::clone(url, path)
                .unwrap_or_else(|_| panic!("Could not clone repository: {}", url))
        }
    };
    let target_oid = git2::Oid::from_str(commit).unwrap();
    if let Some(oid) = repo.head().unwrap().target_peel() {
        if oid == target_oid {
            return changed;
        }
    };
    repo.set_head_detached(target_oid)
        .unwrap_or_else(|_| panic!("Could not checkout commit: {}", commit));
    changed
}

/// Gets a description of the C(++) compiler used
fn get_compiler_description(compiler: cc::Tool) -> String {
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
    format!("{} {}", compiler_version, compiler_flags.to_str().unwrap())
}
