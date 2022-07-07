use std::process::Command;

fn main() {
    #[cfg(feature = "cadical")]
    {
        // TODO: Only configure if necessary
        Command::new("./configure")
            .current_dir("solvers/cadical")
            .output()
            .expect("failed to run CaDiCal configure script");
        Command::new("make")
            .current_dir("solvers/cadical")
            .output()
            .expect("failed to make CaDiCaL");
        println!("cargo:rustc-link-search=native=solvers/cadical/build");
        println!("cargo:rustc-link-lib=static=cadical");

        #[cfg(target_os = "macos")]
        println!("cargo:rustc-flags=-l dylib=c++");

        #[cfg(not(target_os = "macos"))]
        println!("cargo:rustc-flags=-l dylib=stdc++");
    }
}
