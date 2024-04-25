extern crate cbindgen;

use std::env;

fn main() {
    if std::env::var("DOCS_RS").is_ok() {
        // exit the build script early on docs.rs because cbindgen needs network access
        return;
    }

    let crate_dir = env::var("CARGO_MANIFEST_DIR").unwrap();

    // Generate C-API header
    cbindgen::Builder::new()
        .with_config(
            cbindgen::Config::from_file(format!("{}/cbindgen.toml", crate_dir))
                .expect("could not read cbindgen.toml"),
        )
        .with_crate(crate_dir)
        .generate()
        .expect("Unable to generate bindings")
        .write_to_file("rustsat.h");

    println!("cargo:rerun-if-changed=cbindgen.toml");
    println!("cargo:rerun-if-changed=src/capi.rs");

    // Setup inline-c
    let include_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let ld_dir = target_dir().unwrap();

    let cflags = format!("cargo:rustc-env=INLINE_C_RS_CFLAGS=-I{I} -L{L} -lrustsat_capi -D_DEBUG -D_CRT_SECURE_NO_WARNINGS", I=include_dir, L=ld_dir.to_string_lossy());
    let cflags = format!("{} -llzma -lbz2", cflags);
    println!("{}", cflags);

    let ldflags = format!(
        "cargo:rustc-env=INLINE_C_RS_LDFLAGS={L}/librustsat_capi.a",
        L = ld_dir.to_string_lossy()
    );
    let ldflags = format!("{} -llzma -lbz2", ldflags);
    println!("{}", ldflags);
}

// https://github.com/rust-lang/cargo/issues/9661#issuecomment-1722358176
fn target_dir() -> Result<std::path::PathBuf, Box<dyn std::error::Error>> {
    let out_dir = std::path::PathBuf::from(std::env::var("OUT_DIR")?);
    let profile = std::env::var("PROFILE")?;
    let mut target_dir = None;
    let mut sub_path = out_dir.as_path();
    while let Some(parent) = sub_path.parent() {
        if parent.ends_with(&profile) {
            target_dir = Some(parent);
            break;
        }
        sub_path = parent;
    }
    let target_dir = target_dir.ok_or("not found")?;
    Ok(target_dir.to_path_buf())
}
