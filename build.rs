#![allow(dead_code, unused)]
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
    #[cfg(feature = "ipasir")]
    {
        // IPASIR conflicts with incremental solvers that implement IPASIR
        #[cfg(feature = "cadical")]
        println!("cargo:warning=Feature `cadical` (potentially) conflicts with feature `ipasir`");

        // Link to custom IPASIR solver
        // Uncomment and modify this for linking to your static library
        // The name of the library should be _without_ the prefix 'lib' and the suffix '.a'
        //println!("cargo:rustc-link-lib=static=<path-to-your-static-lib>");
        //println!("cargo:rustc-link-search=<name-of-your-static-lib>");
        // If your IPASIR solver links to the C++ stdlib, uncomment the next four lines
        //#[cfg(target_os = "macos")]
        //println!("cargo:rustc-flags=-l dylib=c++");
        //#[cfg(not(target_os = "macos"))]
        //println!("cargo:rustc-flags=-l dylib=stdc++");
    }

    // Build external solver dependencies
    // Full commit hashes need to be provided
    build_cadical(
        "https://github.com/chrjabs/cadical.git",
        "master",
        "02d8231b6dbefdba6292c06ddea83b9892cdaf10",
    );
    build_kissat(
        "https://github.com/arminbiere/kissat.git",
        "master",
        "97917ddf2b12adc6f63c7b2a5a403a1ee7d81836",
    );
    build_glucose4(
        "https://github.com/chrjabs/glucose4",
        "main",
        "35a008f1b64da2235c4ea469446d7a046ea24fbc",
    );
    build_minisat(
        "https://github.com/chrjabs/minisat",
        "main",
        "7b20f5002b169715a9d2d834e39b2b6c744136eb",
    );

    let out_dir = env::var("OUT_DIR").unwrap();

    // All built solvers are there
    println!("cargo:rustc-link-search={}", out_dir);
    println!("cargo:rustc-link-search={}/lib", out_dir);

    // Configuration has a solver
    #[cfg(any(
        feature = "kissat",
        feature = "cadical",
        feature = "glucose4",
        feature = "minisat",
        feature = "ipasir"
    ))]
    println!("cargo:rustc-cfg=solver");
    // Configuration has an incremental solver
    #[cfg(any(
        feature = "cadical",
        feature = "glucose4",
        feature = "minisat",
        feature = "ipasir"
    ))]
    println!("cargo:rustc-cfg=incsolver");
}

fn build_cadical(repo: &str, branch: &str, commit: &str) -> bool {
    #[cfg(feature = "cadical")]
    {
        let out_dir = env::var("OUT_DIR").unwrap();
        let mut cadical_dir_str = out_dir.clone();
        cadical_dir_str.push_str("/cadical");
        let cadical_dir = Path::new(&cadical_dir_str);
        if update_repo(cadical_dir, repo, branch, commit)
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
            // Setup build configuration
            let mut cadical_build = cc::Build::new();
            cadical_build.cpp(true);
            if env::var("PROFILE").unwrap() == "debug" {
                cadical_build
                    .opt_level(0)
                    .define("DEBUG", None)
                    .warnings(true)
                    .debug(true);
            } else {
                cadical_build
                    .opt_level(3)
                    .define("NDEBUG", None)
                    .warnings(false);
            }
            // Generate build header
            let mut build_header = File::create(cadical_dir.join("src").join("build.hpp"))
                .expect("Could not create kissat CaDiCaL header");
            let mut cadical_version = fs::read_to_string(cadical_dir.join("VERSION"))
                .expect("Cannot read CaDiCaL version");
            cadical_version.retain(|c| c != '\n');
            let (compiler_desc, compiler_flags) =
                get_compiler_description(cadical_build.get_compiler());
            write!(
                build_header,
                "#define VERSION \"{}\"\n#define IDENTIFIER \"{}\"\n#define COMPILER \"{}\"\n#define FLAGS \"{}\"\n#define DATE \"{}\"",
                cadical_version, commit, compiler_desc, compiler_flags, chrono::Utc::now()
            ).expect("Failed to write CaDiCaL build.hpp");
            // Build CaDiCaL
            cadical_build
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

        return true;
    }
    false
}

fn build_kissat(repo: &str, branch: &str, commit: &str) -> bool {
    #[cfg(feature = "kissat")]
    {
        let out_dir = env::var("OUT_DIR").unwrap();
        let mut kissat_dir_str = out_dir.clone();
        kissat_dir_str.push_str("/kissat");
        let kissat_dir = Path::new(&kissat_dir_str);
        if update_repo(kissat_dir, repo, branch, commit)
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
            if env::var("PROFILE").unwrap() == "debug" {
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
            // Generate build header
            let mut build_header = File::create(kissat_dir.join("src").join("build.h"))
                .expect("Could not create kissat build header");
            let mut kissat_version =
                fs::read_to_string(kissat_dir.join("VERSION")).expect("Cannot read kissat version");
            kissat_version.retain(|c| c != '\n');
            let (compiler_desc, compiler_flags) =
                get_compiler_description(kissat_build.get_compiler());
            write!(
                build_header,
                "#define VERSION \"{}\"\n#define COMPILER \"{} {}\"\n#define ID \"{}\"\n#define BUILD \"{}\"\n#define DIR \"{}\"",
                kissat_version, compiler_desc, compiler_flags, commit, chrono::Utc::now(), kissat_dir.as_os_str().to_str().unwrap()
            ).expect("Failed to write kissat build.h");
            // Build Kissat
            kissat_build
                .include(kissat_dir.join("src"))
                .warnings(false)
                .files(src_files)
                .compile("kissat");
        };

        println!("cargo:rustc-link-lib=static=kissat");

        return true;
    }
    false
}

fn build_glucose4(repo: &str, branch: &str, commit: &str) -> bool {
    #[cfg(feature = "glucose4")]
    {
        let out_dir = env::var("OUT_DIR").unwrap();
        let mut glucose4_dir_str = out_dir.clone();
        glucose4_dir_str.push_str("/glucose4");
        let glucose4_dir = Path::new(&glucose4_dir_str);
        if update_repo(glucose4_dir, repo, branch, commit)
            || !Path::new(&out_dir)
                .join("lib")
                .join("libglucose4.a")
                .exists()
        {
            cmake::build(glucose4_dir);
        };

        println!("cargo:rustc-link-lib=static=glucose4");

        return true;
    }
    false
}

fn build_minisat(repo: &str, branch: &str, commit: &str) -> bool {
    #[cfg(feature = "minisat")]
    {
        let out_dir = env::var("OUT_DIR").unwrap();
        let mut minisat_dir_str = out_dir.clone();
        minisat_dir_str.push_str("/minisat");
        let minisat_dir = Path::new(&minisat_dir_str);
        if update_repo(minisat_dir, repo, branch, commit)
            || !Path::new(&out_dir)
                .join("lib")
                .join("libminisat.a")
                .exists()
        {
            cmake::build(minisat_dir);
        };

        println!("cargo:rustc-link-lib=static=minisat");

        return true;
    }
    false
}

/// Returns true if there were changes, false if not
fn update_repo(path: &Path, url: &str, branch: &str, commit: &str) -> bool {
    let mut changed = false;
    let target_oid = git2::Oid::from_str(commit)
        .unwrap_or_else(|e| panic!("Invalid commit hash {}: {}", commit, e));
    let repo = match git2::Repository::open(path) {
        Ok(repo) => {
            // Check if already at correct commit
            if let Some(oid) = repo.head().unwrap().target_peel() {
                if oid == target_oid {
                    return changed;
                }
            };
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
            repo
        }
        Err(_) => {
            if path.exists() {
                fs::remove_dir_all(path).unwrap_or_else(|e| {
                    panic!("Could not delete directory {}: e", path.to_str().unwrap())
                });
            };
            changed = true;
            git2::Repository::clone(url, path)
                .unwrap_or_else(|e| panic!("Could not clone repository {}: {}", url, e))
        }
    };
    let target_commit = repo
        .find_commit(target_oid)
        .unwrap_or_else(|e| panic!("Could not find commit {}: {}", commit, e));
    repo.checkout_tree(target_commit.as_object(), None)
        .unwrap_or_else(|e| panic!("Could not checkout commit {}: {}", commit, e));
    repo.set_head_detached(target_oid)
        .unwrap_or_else(|e| panic!("Could not detach head at {}: {}", commit, e));
    changed
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
