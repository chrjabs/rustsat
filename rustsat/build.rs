extern crate cbindgen;

use std::env;

fn main() {
    #[cfg(feature = "ipasir")]
    {
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

    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();

    cbindgen::Builder::new()
        .with_config(
            cbindgen::Config::from_file(format!("{}/cbindgen.toml", crate_dir))
                .expect("could not read cbindgen.toml"),
        )
        .with_crate(crate_dir)
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file("rustsat.h");

    print!("cargo:rerun-if-changed=cbindgen.toml");
    print!("cargo:rerun-if-changed=src/capi.rs");
}
