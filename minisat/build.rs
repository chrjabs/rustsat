#![warn(clippy::pedantic)]

use std::{
    env,
    path::{Path, PathBuf},
};

fn main() {
    // Build C++ library
    build();

    let out_dir = env::var("OUT_DIR").unwrap();

    println!("cargo:rerun-if-changed=cppsrc/");

    // Built solver is in out_dir
    println!("cargo:rustc-link-search={out_dir}");
    println!("cargo:rustc-link-search={out_dir}/lib");
    println!("cargo:rustc-link-lib=static=minisat");

    // Link c++ std lib
    // Note: this should be _after_ linking the solver itself so that it is actually pulled in
    #[cfg(target_os = "macos")]
    println!("cargo:rustc-link-lib=dylib=c++");
    #[cfg(not(any(target_os = "macos", target_os = "windows")))]
    println!("cargo:rustc-link-lib=dylib=stdc++");

    // Generate Rust FFI bindings
    let bindings = bindgen::Builder::default()
        .rust_target("1.70.0".parse().unwrap()) // Set MSRV of RustSAT
        .header("cppsrc/minisat/cminisat.h")
        .allowlist_file("cppsrc/minisat/cminisat.h")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate ffi bindings");
    bindings
        .write_to_file(PathBuf::from(out_dir).join("bindings.rs"))
        .expect("Could not write ffi bindings");
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
