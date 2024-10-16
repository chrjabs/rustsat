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
    println!("cargo:rustc-link-lib=static=glucose4");

    // Link c++ std lib
    // Note: this should be _after_ linking the solver itself so that it is actually pulled in
    #[cfg(target_os = "macos")]
    println!("cargo:rustc-link-lib=dylib=c++");
    #[cfg(not(any(target_os = "macos", target_os = "windows")))]
    println!("cargo:rustc-link-lib=dylib=stdc++");

    // Generate Rust FFI bindings
    let bindings = bindgen::Builder::default()
        .header("cppsrc/cglucose4.h")
        .allowlist_file("cppsrc/cglucose4.h")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate ffi bindings");
    bindings
        .write_to_file(PathBuf::from(out_dir).join("bindings.rs"))
        .expect("Could not write ffi bindings");
}

fn build() {
    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let mut glucose_dir_str = crate_dir.clone();
    glucose_dir_str.push_str("/cppsrc");
    let glucose_dir = Path::new(&glucose_dir_str);
    let mut conf = cmake::Config::new(glucose_dir);
    conf.define("BUILD_SYRUP", "OFF")
        .define("BUILD_EXECUTABLES", "OFF");
    #[cfg(feature = "quiet")]
    conf.define("QUIET", "ON");
    #[cfg(not(feature = "debug"))]
    conf.profile("Release");
    conf.build();
}
