spellcheck *args:
    cargo-spellcheck --code 1 {{ args }}
    typos

test *args:
    cargo nextest run --workspace --exclude rustsat-pyapi --features=all,internals {{ args }}

test-external-solver *args:
    echo "RS_EXT_SOLVER=$RS_EXT_SOLVER"
    cargo nextest run {{ args }} -p rustsat --test external_solver --verbose -- --ignored

doc-tests *args:
    cargo test --workspace --exclude rustsat-capi --exclude rustsat-pyapi --features=all,internals --doc {{ args }}

clippy *args:
    cargo clippy --workspace --all-targets --target-dir target/clippy --features=all,internals {{ args }} -- -Dwarnings

gen *args:
    cargo run -p rustsat-codegen -- {{ args }}

readmes *args:
    cargo-rdme {{ args }}
    cargo-rdme --workspace-project pigeons {{ args }}
    cargo-rdme --workspace-project rustsat-batsat {{ args }}
    cargo-rdme --workspace-project rustsat-cadical {{ args }}
    cargo-rdme --workspace-project rustsat-capi {{ args }}
    cargo-rdme --workspace-project rustsat-glucose {{ args }}
    cargo-rdme --workspace-project rustsat-ipasir {{ args }}
    cargo-rdme --workspace-project rustsat-kissat {{ args }}
    cargo-rdme --workspace-project rustsat-minisat {{ args }}
    cargo-rdme --workspace-project rustsat-pyapi {{ args }}
    cargo-rdme --workspace-project rustsat-tools {{ args }}

pyapi cmd *args:
    maturin {{ cmd }} -m pyapi/Cargo.toml {{ args }}

pyapi-build-install: (pyapi "build")
    pip install --no-index --find-links target/wheels/ rustsat

docs *args:
    cargo doc -Zunstable-options -Zrustdoc-scrape-examples --workspace --features=all,internals {{ args }}

test-each-feature *args:
    cargo hack nextest run --each-feature {{ args }}

feature-powerset *args:
    cargo hack nextest run -p rustsat --feature-powerset --depth 2 --exclude-features bench {{ args }}

semver-checks:
    cargo semver-checks --workspace --exclude rustsat-cadical
    cargo semver-checks -p rustsat-cadical --default-features

kani:
    cargo kani

precommit: gen spellcheck (readmes "--check")

prepush: clippy test

subtree tree cmd ref:
    #!/usr/bin/env -S bash -euo pipefail
    declare -A prefixes
    prefixes=(
        ["minisat"]="minisat/cppsrc"
        ["glucose"]="glucose/cppsrc"
        ["cadical"]="cadical/cppsrc"
        ["kissat"]="kissat/csrc"
    )

    case {{ cmd }} in
        pull)
            echo "Pulling subtree {{ tree }} from ref {{ ref }}"
            git subtree pull --prefix "${prefixes[{{ tree }}]}" {{ tree }} {{ ref }} --squash -m "chore({{ tree }}: update subtree"
            ;;

        push)
            echo "Pushing subtree {{ tree }} from ref {{ ref }}"
            git subtree push --prefix "${prefixes[{{ tree }}]}" {{ tree }} {{ ref }}
            ;;

        *)
            2>&1 echo "Unknown command {{ cmd }}"
            2>&1 echo "Usage: subtree <tree> <command> <ref>"
            exit 1
    esac

ci-cache *args:
    #!/usr/bin/env -S bash -euo pipefail
    source .env
    if [[ -x /runner/cache.sh ]]; then
        cmd_group "/runner/cache.sh {{ args }}"
    fi

coverage *args:
    cargo llvm-cov --no-report nextest --workspace --exclude rustsat-pyapi --features=all,internals
    cargo llvm-cov --no-report --doc --workspace --exclude rustsat-ipasir --features=all,internals
    cargo llvm-cov report --doctests --html {{ args }}

coverage-ci:
    #!/usr/bin/env -S bash -euo pipefail
    source .env
    cmd_group "cargo llvm-cov --no-report nextest --workspace --exclude rustsat-pyapi --features=all,internals"
    cmd_group "cargo llvm-cov --no-report --doc --workspace --exclude rustsat-ipasir --features=all,internals"
    cmd_group "RS_EXT_SOLVER=$(which cadical) cargo llvm-cov --no-report nextest -p rustsat --test external_solver --verbose -- --ignored"
    mkdir coverage
    cmd_group "cargo llvm-cov report --doctests --lcov --output-path coverage/lcov.info"

valgrind *args:
    cargo valgrind nextest run {{ args }}

# note: something in libtest-mimic seems to be leaking memory
capi-valgrind:
    #!/usr/bin/env -S bash -euo pipefail
    cargo nextest run -p rustsat-capi
    for test in capi/tests/*.c; do
        valgrind target/tmp/"$(basename -s .c "$test")"
    done

all-valgrind *args: (valgrind "--workspace --exclude rustsat-pyapi --exclude rustsat-capi --features=all,internals" args) capi-valgrind

miri *args:
    MIRIFLAGS=-Zmiri-disable-isolation cargo miri nextest run {{ args }}

all-miri *args: (miri "--workspace --exclude rustsat-pyapi --features=all,internals" args)

# CI checks

msrv-ci: (ci-cache "restore --key ci-msrv-build") && (ci-cache "save --rust --key ci-msrv-build")
    #!/usr/bin/env -S bash -euo pipefail
    source .env
    cmd_group "cargo hack build --rust-version --workspace --features=all,internals --ignore-unknown-features"

# TODO:
python-api-ci: (ci-cache "restore --key ci-python-api") && (ci-cache "save --rust --key ci-python-api")
    #!/usr/bin/env -S bash -euo pipefail
    source .env
    source "$PYTHON_API_VENV/bin/activate"
    cmd_group "just pyapi-build-install"
    cmd_group "python pyapi/examples/pyapi-dpw.py"
    cmd_group "stubtest --mypy-config-file pyapi/pyproject.toml --allowlist pyapi/stubtest-allowlist.txt rustsat"
    cmd_group "pip uninstall -y rustsat"

# TODO:
pages-ci:
    #!/usr/bin/env -S bash -euo pipefail
    source .env
    mkdir -p _site/
    cmd_group "just docs --no-deps"
    mv target/doc/ _site/main/
    source "$PAGES_VENV/bin/activate"
    cmd_group "just pyapi-build-install"
    cmd_group "pdoc -o _site/pyapi/ --no-show-source rustsat"
    cmd_group "pip uninstall -y rustsat"
