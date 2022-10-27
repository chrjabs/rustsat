use cc;
use git2;
use glob::glob;
use std::{env, fs, path::Path};

fn main() {
    // Build external solver dependencies
    // Full commit hashes need to be provided
    build_cadical(
        "https://github.com/chrjabs/cadical.git",
        "0fe57b6945f1db37bb0e1adb64d24056035c3bbb",
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

/// Returns true if there were changes, false if not
fn update_repo(path: &Path, url: &str, commit: &str) -> bool {
    let mut changed = false;
    let repo = match git2::Repository::open(path) {
        Ok(repo) => repo,
        Err(_) => {
            if path.exists() {
                fs::remove_dir_all(path).expect(&format!(
                    "Could not delete directory: {}",
                    path.to_str().unwrap()
                ));
            };
            changed = true;
            git2::Repository::clone(url, path)
                .expect(&format!("Could not clone repository: {}", url))
        }
    };
    let target_oid = git2::Oid::from_str(commit).unwrap();
    if let Some(oid) = repo.head().unwrap().target_peel() {
        if oid == target_oid {
            return changed;
        }
    };
    repo.set_head_detached(target_oid)
        .expect(&format!("Could not checkout commit: {}", commit));
    changed
}
