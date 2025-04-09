use std::path::Path;

use libtest_mimic::{Arguments, Failed, Trial};

fn main() {
    let args = Arguments::from_args();
    let tests = collect_tests();
    libtest_mimic::run(&args, tests).exit();
}

fn collect_tests() -> Vec<Trial> {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let mut tests = vec![];
    for entry in
        std::fs::read_dir(format!("{manifest_dir}/tests/")).expect("failed to find c tests")
    {
        let entry = entry.unwrap();
        let file_type = entry.file_type().unwrap();
        let path = entry.path();
        if file_type.is_file() {
            if path.extension() == Some(std::ffi::OsStr::new("c")) {
                let name = path.file_stem().unwrap().to_str().unwrap().to_string();
                tests.push(Trial::test(name, move || run_test(&path)));
            } else {
                eprintln!("skipping file `{path:?}`");
            }
        } else if file_type.is_dir() {
            eprintln!("skipping subdir `{path:?}`");
        }
    }
    tests
}

fn run_test(path: &Path) -> Result<(), Failed> {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let out_dir = env!("CARGO_TARGET_TMPDIR");
    let name = path.file_stem().unwrap().to_str().unwrap();
    let host = target_lexicon::HOST.to_string();
    let msvc = host.contains("msvc");
    let oname = if msvc {
        format!("{name}.exe")
    } else {
        name.to_string()
    };

    let compile = cc::Build::new()
        .cargo_metadata(false)
        .warnings(true)
        .extra_warnings(true)
        .warnings_into_errors(true)
        .host(&host)
        .target(&host)
        .opt_level(1)
        .debug(false)
        .get_compiler();
    let clang = compile.is_like_clang();
    let mut compile = compile.to_command();
    compile.current_dir(out_dir);
    if msvc && !clang {
        compile.args([
            &format!("/I{manifest_dir}"),
            path.as_os_str().to_str().unwrap(),
            &std::env::var("CAPI_LIB_PATH").expect("should be set by cargo nextest setup script"),
            "ntdll.lib",
            "userenv.lib",
            "ws2_32.lib",
            "/link",
            "/defaultlib:msvcrt",
            &format!("/out:{oname}"),
        ]);
    } else {
        compile.args([
            path.as_os_str().to_str().unwrap(),
            "-o",
            &oname,
            &format!("-I{manifest_dir}"),
            &format!(
                "-L{}",
                std::env::var("CAPI_LIB_DIR").expect("should be set by cargo nextest setup script")
            ),
            "-lrustsat_capi",
        ]);
    };
    let compile = dbg!(compile).output()?;
    if !compile.status.success() {
        return Err(format!(
            r#"failed to compile test `{path:?}`: exit code {}
            === stdout ===
            {}
            === stderr ===
            {}"#,
            compile.status,
            std::str::from_utf8(&compile.stdout)?,
            std::str::from_utf8(&compile.stderr)?,
        )
        .into());
    }

    let mut cmd = std::path::PathBuf::from(out_dir);
    cmd.push(name);
    let run = std::process::Command::new(cmd).output()?;
    if !run.status.success() {
        return Err(format!(
            r#"test {name} failed: exit code {}
            === stdout ===
            {}
            === stderr ===
            {}"#,
            compile.status,
            std::str::from_utf8(&compile.stdout)?,
            std::str::from_utf8(&compile.stderr)?,
        )
        .into());
    }
    Ok(())
}
