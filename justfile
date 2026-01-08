spellcheck *args:
    cargo spellcheck --code 1 {{ args }}
    typos

test *args:
    cargo nextest run --workspace --exclude rustsat-pyapi --features=_test {{ args }}

test-external-solver *args:
    echo "RS_EXT_SOLVER=$RS_EXT_SOLVER"
    cargo nextest run {{ args }} -p rustsat --test external_solver --verbose -- --ignored

doc-tests *args:
    cargo test --workspace --exclude rustsat-capi --exclude rustsat-pyapi --features=_test --doc {{ args }}

clippy *args:
    cargo clippy --workspace --all-targets --target-dir target/clippy --features=_test {{ args }} -- -Dwarnings

gen *args:
    cargo run -p rustsat-codegen -- {{ args }}

readmes *args:
    cargo rdme {{ args }}
    # keep-sorted start
    cargo rdme --workspace-project pigeons {{ args }}
    cargo rdme --workspace-project rustsat-batsat {{ args }}
    cargo rdme --workspace-project rustsat-cadical {{ args }}
    cargo rdme --workspace-project rustsat-capi {{ args }}
    cargo rdme --workspace-project rustsat-glucose {{ args }}
    cargo rdme --workspace-project rustsat-ipasir {{ args }}
    cargo rdme --workspace-project rustsat-kissat {{ args }}
    cargo rdme --workspace-project rustsat-minisat {{ args }}
    cargo rdme --workspace-project rustsat-pyapi {{ args }}
    cargo rdme --workspace-project rustsat-tools {{ args }}
    # keep-sorted end

pyapi cmd *args:
    maturin {{ cmd }} -m pyapi/Cargo.toml {{ args }}

pyapi-build-install: (pyapi "build")
    pip install --no-index --find-links target/wheels/ rustsat

docs *args:
    cargo doc -Zunstable-options -Zrustdoc-scrape-examples --workspace --features=_docs {{ args }}

test-each-feature *args:
    cargo hack nextest run --each-feature {{ args }}

feature-powerset *args:
    cargo hack nextest run -p rustsat --feature-powerset --depth 2 --exclude-features bench {{ args }}

semver-checks:
    nix develop '.#semverChecks' --command cargo semver-checks --workspace --exclude rustsat-cadical
    nix develop '.#semverChecks' --command cargo semver-checks -p rustsat-cadical --default-features

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
    declare -A repos
    repos=(
        ["minisat"]="git@github.com:chrjabs/minisat.git"
        ["glucose"]="git@github.com:chrjabs/glucose.git"
        ["cadical"]="git@github.com:arminbiere/cadical.git"
        ["kissat"]="git@github.com:arminbiere/kissat.git"
    )

    case {{ cmd }} in
        pull)
            echo "Pulling subtree {{ tree }} from ref {{ ref }}"
            git subtree pull --prefix "${prefixes[{{ tree }}]}" "${repos[{{ tree }}]}" {{ ref }} --squash -m "chore({{ tree }}): update subtree to {{ ref }}"
            ;;

        push)
            echo "Pushing subtree {{ tree }} from ref {{ ref }}"
            git subtree push --prefix "${prefixes[{{ tree }}]}" "${repos[{{ tree }}]}" {{ ref }}
            ;;

        *)
            2>&1 echo "Unknown command {{ cmd }}"
            2>&1 echo "Usage: subtree <tree> <command> <ref>"
            exit 1
    esac

coverage *args:
    cargo llvm-cov --no-report nextest --workspace --exclude rustsat-pyapi --features=_test
    cargo llvm-cov --no-report --doc --workspace --exclude rustsat-ipasir --features=_test
    cargo llvm-cov report --doctests --html {{ args }}

valgrind *args:
    cargo valgrind nextest run {{ args }}

# note: something in libtest-mimic seems to be leaking memory
capi-valgrind:
    #!/usr/bin/env -S bash -euo pipefail
    cargo nextest run -p rustsat-capi
    for test in capi/tests/*.c; do
        valgrind target/tmp/"$(basename -s .c "$test")"
    done

all-valgrind *args: (valgrind "--workspace --exclude rustsat-pyapi --exclude rustsat-capi --features=_test" args) capi-valgrind

miri *args:
    MIRIFLAGS=-Zmiri-disable-isolation cargo miri nextest run {{ args }}

all-miri *args: (miri "--workspace --exclude rustsat-pyapi --features=_test" args)

deny *args:
    cargo deny --exclude-unpublished --exclude-dev check {{ args }}
