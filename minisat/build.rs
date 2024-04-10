use std::{env, path::Path};

fn main() {
    if std::env::var("DOCS_RS").is_ok() {
        // don't build c++ library on docs.rs due to network restrictions
        return;
    }

    // Build C++ library
    // Full commit hash needs to be provided
    build();

    let out_dir = env::var("OUT_DIR").unwrap();

    println!("cargo:rerun-if-changed=cppsrc/");

    #[cfg(target_os = "macos")]
    println!("cargo:rustc-flags=-l dylib=c++");

    #[cfg(not(any(target_os = "macos", target_os = "windows")))]
    println!("cargo:rustc-flags=-l dylib=stdc++");

    // Built solver is in out_dir
    println!("cargo:rustc-link-search={}", out_dir);
    println!("cargo:rustc-link-search={}/lib", out_dir);
}

fn build() {
    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let mut minisat_dir_str = crate_dir.clone();
    minisat_dir_str.push_str("/cppsrc");
    let minisat_dir = Path::new(&minisat_dir_str);
    let mut conf = cmake::Config::new(minisat_dir);
    conf.define("BUILD_BINARIES", "OFF");
    #[cfg(feature = "quiet")]
    conf.define("QUIET", "ON");
    #[cfg(not(feature = "debug"))]
    conf.profile("Release");
    conf.build();
}
