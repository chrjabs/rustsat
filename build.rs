use std::path::Path;
use std::process::Command;

fn main() {
    #[cfg(feature = "cadical")]
    {
        let cadical_path = "solvers/cadical";
        println!("cargo:rerun-if-changed={}", cadical_path);
        Command::new("git")
            .arg("submodule")
            .arg("update")
            .arg("--init")
            .arg(cadical_path)
            .output()
            .expect("failed to update CaDiCaL submodule");
        if !Path::new(&format!("{}/makefile", cadical_path)).exists() {
            // Only configure if makefile doesn't exist
            Command::new("sh")
                .arg("configure")
                .current_dir(cadical_path)
                .output()
                .expect("failed to run CaDiCal configure script");
        }
        Command::new("make")
            .arg("-j")
            .current_dir(cadical_path)
            .output()
            .expect("failed to make CaDiCaL");
        println!("cargo:rustc-link-search=native={}/build", cadical_path);
        println!("cargo:rustc-link-lib=static=cadical");

        #[cfg(target_os = "macos")]
        println!("cargo:rustc-flags=-l dylib=c++");

        #[cfg(not(target_os = "macos"))]
        println!("cargo:rustc-flags=-l dylib=stdc++");
    }
}
