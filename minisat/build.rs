#![warn(clippy::pedantic)]

fn main() {
    if std::mem::size_of::<std::ffi::c_int>() != std::mem::size_of::<u32>() {
        // NOTE: this is required for RustSAT and Minisat literals to have compatible memory
        // layouts
        println!("cargo:error=target architecture not supported since `c_int` is not 32 bits");
        panic!("target architecture not supported since `c_int` is not 32 bits");
    }

    // Build C++ library
    build();

    let out_dir = std::env::var("OUT_DIR").unwrap();

    println!("cargo:rerun-if-changed=vendor/");

    // Built solver is in out_dir
    println!("cargo:rustc-link-search={out_dir}");
    println!("cargo:rustc-link-search={out_dir}/lib");
    println!("cargo:rustc-link-lib=static=minisat");

    // Link c++ std lib
    // Note: this should be _after_ linking the solver itself so that it is actually pulled in
    // Note: `cfg!(target_os)` in a build script refers to the host, so read the target from cargo
    match std::env::var("CARGO_CFG_TARGET_OS").unwrap().as_str() {
        "macos" => println!("cargo:rustc-link-lib=dylib=c++"),
        "windows" => {}
        "emscripten" => {
            // rustc links with `emcc`, which unlike `em++` does not add the C++ ABI library
            println!("cargo:rustc-link-lib=dylib=c++");
            println!("cargo:rustc-link-lib=dylib=c++abi");
        }
        _ => println!("cargo:rustc-link-lib=dylib=stdc++"),
    }

    // Generate Rust FFI bindings
    let bindings = bindgen::Builder::default()
        .rust_target("1.87.0".parse().unwrap()) // Set MSRV
        .clang_args(emscripten_bindgen_args())
        .header("vendor/minisat/cminisat.h")
        .allowlist_file("vendor/minisat/cminisat.h")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate ffi bindings");
    bindings
        .write_to_file(std::path::PathBuf::from(out_dir).join("bindings.rs"))
        .expect("Could not write ffi bindings");
}

fn build() {
    let crate_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let mut minisat_dir_str = crate_dir;
    minisat_dir_str.push_str("/vendor");
    let minisat_dir = std::path::Path::new(&minisat_dir_str);
    let mut conf = cmake::Config::new(minisat_dir);
    conf.define("BUILD_BINARIES", "OFF");
    // The solver wrapper catches C++ exceptions (e.g., `std::bad_alloc`), which emscripten
    // disables by default. Use the same exception model as Rust's emscripten target.
    if std::env::var("CARGO_CFG_TARGET_OS").unwrap() == "emscripten" {
        conf.cxxflag("-fwasm-exceptions");
        // `emcmake` adds emscripten's toolchain file, but unless the `cmake` crate knows about it,
        // it also passes `CMAKE_<LANG>_COMPILER`. That differs from the toolchain file's value and
        // makes CMake delete its cache, and with it the toolchain, when reconfiguring.
        if !cmake_toolchain_file_in_env() {
            conf.define("CMAKE_TOOLCHAIN_FILE", emscripten_toolchain_file());
        }
    }
    #[cfg(feature = "quiet")]
    conf.define("QUIET", "ON");
    #[cfg(not(feature = "debug"))]
    conf.profile("Release");
    conf.build();
}

/// Extra clang arguments for bindgen when targeting emscripten
///
/// Clang defaults to hidden visibility on wasm targets and bindgen skips hidden functions, so
/// without `-fvisibility=default` the bindings contain no functions at all. libclang also does
/// not know the emscripten sysroot, so the compile flags are queried from `emcc`.
fn emscripten_bindgen_args() -> Vec<String> {
    if std::env::var("CARGO_CFG_TARGET_OS").unwrap() != "emscripten" {
        return vec![];
    }
    let output = std::process::Command::new("emcc")
        .arg("--cflags")
        .output()
        .expect("failed to run `emcc --cflags`, is emscripten installed?");
    assert!(
        output.status.success(),
        "`emcc --cflags` failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let cflags = String::from_utf8(output.stdout).expect("`emcc --cflags` output is not UTF-8");
    assert!(
        !cflags.contains(['"', '\'', '\\']),
        "cannot split quoted `emcc --cflags` output: {cflags}"
    );
    let mut args: Vec<String> = cflags.split_whitespace().map(String::from).collect();
    args.push(String::from("-fvisibility=default"));
    args
}

/// Path to emscripten's toolchain file, as added by `emcmake`
fn emscripten_toolchain_file() -> std::path::PathBuf {
    let output = std::process::Command::new("em-config")
        .arg("EMSCRIPTEN_ROOT")
        .output()
        .expect("failed to run `em-config EMSCRIPTEN_ROOT`, is emscripten installed?");
    assert!(
        output.status.success(),
        "`em-config EMSCRIPTEN_ROOT` failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let root = String::from_utf8(output.stdout).expect("`em-config` output is not UTF-8");
    let path = std::path::Path::new(root.trim()).join("cmake/Modules/Platform/Emscripten.cmake");
    assert!(
        path.is_file(),
        "emscripten toolchain file {} does not exist",
        path.display()
    );
    path
}

/// Whether a toolchain file is set via the environment variables that the `cmake` crate checks
fn cmake_toolchain_file_in_env() -> bool {
    let target = std::env::var("TARGET").unwrap();
    [
        format!("CMAKE_TOOLCHAIN_FILE_{target}"),
        format!("CMAKE_TOOLCHAIN_FILE_{}", target.replace('-', "_")),
        String::from("TARGET_CMAKE_TOOLCHAIN_FILE"),
        String::from("CMAKE_TOOLCHAIN_FILE"),
    ]
    .iter()
    .any(|var| std::env::var_os(var).is_some())
}
