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
    println!("cargo:rustc-link-search={out_dir}/build/lib");
    println!("cargo:rustc-link-lib=static=cryptominisat5");

    // Link c++ std lib
    // Note: this should be _after_ linking the solver itself so that it is actually pulled in
    #[cfg(target_os = "macos")]
    println!("cargo:rustc-link-lib=dylib=c++");
    #[cfg(not(any(target_os = "macos", target_os = "windows")))]
    println!("cargo:rustc-link-lib=dylib=stdc++");

    // Generate Rust FFI bindings
    let bindings = bindgen::Builder::default()
        .rust_target("1.66.1".parse().unwrap()) // Set MSRV of RustSAT
        .header("cppsrc/src/cryptominisat_c.h")
        .allowlist_file("cppsrc/src/cryptominisat_c.h")
        .blocklist_function("cmsat_print_stats")
        .blocklist_function("cmsat_set_up_for_scalmc")
        .blocklist_function("set_up_for_arjun")
        .blocklist_function("cmsat_set_yes_comphandler")
        .blocklist_function("cmsat_simplify")
        .blocklist_function("cmsat_set_polarity_auto")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate ffi bindings");
    bindings
        .write_to_file(PathBuf::from(out_dir).join("bindings.rs"))
        .expect("Could not write ffi bindings");
}

fn build() {
    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let mut cms_dir_str = crate_dir.clone();
    cms_dir_str.push_str("/cppsrc");
    let cms_dir = Path::new(&cms_dir_str);
    let mut conf = cmake::Config::new(cms_dir);
    conf.build_target("cryptominisat5")
        .define("STATICCOMPILE", "ON")
        .define("ENABLE_PYTHON_INTERFACE", "OFF")
        .define("ONLY_SIMPLE", "ON")
        .define("NOZLIB", "ON")
        .define("NOM4RI", "ON")
        .define("STATS", "OFF")
        .define("NOVALGRIND", "ON")
        .define("ENABLE_TESTING", "OFF");
    #[cfg(not(feature = "debug"))]
    conf.profile("Release");
    conf.build();
}
