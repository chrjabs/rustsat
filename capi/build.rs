#![warn(clippy::pedantic)]

extern crate cbindgen;

use std::env;

fn main() {
    // Setup inline-c
    let include_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let ld_dir = target_dir().unwrap();

    let cflags = format!("-I{include_dir} -D_DEBUG -D_CRT_SECURE_NO_WARNINGS");
    println!("cargo:rustc-env=INLINE_C_RS_CFLAGS={cflags}");

    let ldflags = format!("-L{L} -lrustsat_capi", L = ld_dir.to_string_lossy());
    let ldflags = format!("{ldflags} -llzma -lbz2");
    println!("cargo:rustc-env=INLINE_C_RS_LDFLAGS={ldflags}");
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
