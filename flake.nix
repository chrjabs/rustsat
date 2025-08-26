{
  description = "Rust library for tools and encodings related to SAT solving library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

    flake-parts.url = "github:hercules-ci/flake-parts";

    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";

    crane.url = "github:ipetkov/crane";

    nur-packages.url = "github:chrjabs/nur-packages";
    nur-packages.inputs.nixpkgs.follows = "nixpkgs";
    nur-packages.inputs.rust-overlay.follows = "rust-overlay";

    treefmt-nix.url = "github:numtide/treefmt-nix";
    treefmt-nix.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } (_: {
      imports = [ inputs.treefmt-nix.flakeModule ];
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      perSystem =
        {
          config,
          system,
          pkgs,
          ...
        }:
        let
          lib = pkgs.lib;

          libs = with pkgs; [
            openssl
            xz
            bzip2
          ];

          stdenv = pkgs.clangStdenv;

          craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (p: p.rust-toolchain);
          wasmCraneLib = (inputs.crane.mkLib pkgs).overrideToolchain (p: p.wasm-toolchain);
          src =
            let
              additionalSrcFilter =
                path: _type:
                builtins.match ".*(data.*|cp?p?|hp?p?|j2|CMakeLists.txt|VERSION|README.md)$" path != null;
              allSrc = path: type: (additionalSrcFilter path type) || (craneLib.filterCargoSources path type);
            in
            lib.cleanSourceWith {
              src = ./.;
              filter = allSrc;
              name = "source";
            };
          commonArgs = {
            inherit src;
            strictDeps = true;
            nativeBuildInputs = with pkgs; [
              llvmPackages.bintools
              pkg-config
              clang
              cmake
            ];
            cargoExtraArgs = "--locked --workspace --features=all,internals";
            cargoTestExtraArgs = "--no-run --exclude rustsat-pyapi";
            LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
            PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
            LD_LIBRARY_PATH = lib.makeLibraryPath libs;
            CARGO_PROFILE = "";
            NEXTEST_PROFILE = "ci";
          };
          cargoArtifacts = craneLib.buildDepsOnly (
            commonArgs
            // {
              nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ cargo-llvm-cov ]);
              # Also build tests for llvm cov
              checkPhaseCargoCommand = ''
                cargo test --locked --workspace --features=all,internals --no-run --exclude rustsat-pyapi
                source <(cargo llvm-cov show-env --export-prefix)
                cargo test --locked --workspace --features=all,internals --no-run --exclude rustsat-pyapi
                ln -s "." "''${CARGO_TARGET_DIR:-target}/llvm-cov-target"
              '';
            }
          );
          cargoWasmArtifacts = wasmCraneLib.buildDepsOnly (
            commonArgs
            // {
              buildPhaseCargoCommand = "cargo check --locked --target wasm32-unknown-unknown -p rustsat-batsat";
              checkPhaseCargoCommand = "";
            }
          );

          crateValgrind =
            crate:
            craneLib.mkCargoDerivation (
              commonArgs
              // {
                pnameSuffix = "${crate}-valgrind";
                cargoArtifacts = craneLib.buildDepsOnly (
                  commonArgs
                  // {
                    pnameSuffix = "-${crate}-test-deps";
                    inherit cargoArtifacts;
                    checkPhaseCargoCommand = "cargo test --locked --no-run -p ${crate}";
                  }
                );
                nativeBuildInputs =
                  commonArgs.nativeBuildInputs
                  ++ (with pkgs; [
                    jq
                    cargo-valgrind
                    cargo-nextest
                  ]);
                buildPhaseCargoCommand = ''
                  cargo valgrind nextest run -p ${crate}
                '';
              }
            );

          workspaceMsrv = (lib.importTOML ./Cargo.toml).workspace.package.rust-version;
          crateMsrvs = {
            rustsat = workspaceMsrv;
            rustsat-pyapi = workspaceMsrv;
            rustsat-tools = (lib.importTOML ./tools/Cargo.toml).package.rust-version;
            rustsat-kissat = (lib.importTOML ./kissat/Cargo.toml).package.rust-version;
            pigeons = (lib.importTOML ./pigeons/Cargo.toml).package.rust-version;
            rustsat-ipasir = workspaceMsrv;
            rustsat-batsat = workspaceMsrv;
            rustsat-cadical = (lib.importTOML ./cadical/Cargo.toml).package.rust-version;
            rustsat-capi = workspaceMsrv;
            rustsat-glucose = workspaceMsrv;
            rustsat-minisat = workspaceMsrv;
          };
          checkMsrv =
            crate:
            let
              craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (
                p: (p.extend (import inputs.rust-overlay)).rust-bin.stable."${crateMsrvs."${crate}"}".minimal
              );
              cargoArtifacts = craneLib.buildDepsOnly (
                commonArgs
                // {
                  pnameSuffix = "-${crateMsrvs."${crate}"}-deps";
                  buildPhaseCargoCommand = "cargo build --workspace";
                  checkPhaseCargoCommand = "";
                }
              );
            in
            craneLib.buildPackage (
              (builtins.removeAttrs commonArgs [ "cargoTestExtraArgs" ])
              // {
                inherit cargoArtifacts;
                pname = "${crate}-msrv";
                cargoExtraArgs = "--locked -p ${crate}";
                doCheck = false;
              }
            );
          # Dummy derivation merging multiple MSRV check
          msrv = stdenv.mkDerivation {
            name = "rustsat-check-msrv";
            nativeBuildInputs = map (crate: checkMsrv crate) (builtins.attrNames crateMsrvs);
            doCheck = false;
            unpackPhase = "true";
            buildPhase = ''
              mkdir -p $out
            '';
          };
          wasm = wasmCraneLib.mkCargoDerivation (
            commonArgs
            // {
              pnameSuffix = "-check-wasm";
              cargoArtifacts = cargoWasmArtifacts;
              buildPhaseCargoCommand = "cargo check --locked --target wasm32-unknown-unknown -p rustsat-batsat";
            }
          );
          docTests = craneLib.mkCargoDerivation (
            commonArgs
            // {
              pnameSuffix = "-doctests";
              doCheck = true;
              nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ cargo-llvm-cov ]);
              inherit cargoArtifacts;
              cargoTestExtraArgs = "--exclude rustsat-capi --exclude rustsat-pyapi";
              buildPhaseCargoCommand = "mkdir -p $out";
              checkPhaseCargoCommand = ''
                cargo llvm-cov --doc --workspace \
                  --exclude rustsat-ipasir \
                  --exclude rustsat-capi \
                  --exclude rustsat-pyapi \
                  --features=all,internals --lcov --output-path $out/coverage.lcov
              '';
            }
          );
          tests = craneLib.cargoNextest (
            commonArgs
            // {
              inherit cargoArtifacts;
              cargoNextestExtraArgs = "--exclude rustsat-pyapi";
              nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ jq ]);
              withLlvmCov = true;
              cargoLlvmCovExtraArgs = "--lcov --output-path $out/coverage.lcov --exclude-from-report rustsat-codegen";
            }
          );

          externalSolverTest =
            slv:
            (craneLib.cargoNextest (
              commonArgs
              // {
                inherit cargoArtifacts;
                cargoExtraArgs = "--locked --features=all,internals";
                cargoNextestExtraArgs = "-p rustsat --test external_solver -- --ignored";
                withLlvmCov = true;
                cargoLlvmCovExtraArgs = "--lcov --output-path $out/coverage.lcov";
                RS_EXT_SOLVER = slv;
              }
            ));
          externalCadical = externalSolverTest (lib.getExe' pkgs.cadical "cadical");
          externalKissat = externalSolverTest (lib.getExe pkgs.kissat);
          externalGimsatul = externalSolverTest (lib.getExe pkgs.gimsatul);
          doc = craneLib.cargoDoc (
            commonArgs
            // {
              inherit cargoArtifacts;
              cargoDocExtraArgs = "--no-deps -Zunstable-options -Zrustdoc-scrape-examples";
              env.RUSTDOCFLAGS = "--deny warnings";
            }
          );
          pyapi = pkgs.python3Packages.callPackage ./pyapi { };
          pyapiDoc = pkgs.callPackage ./pyapi/doc.nix { };
          clippy = craneLib.cargoClippy (
            commonArgs
            // {
              inherit cargoArtifacts;
              cargoClippyExtraArgs = "--all-targets -- --deny warnings";
            }
          );
          codegen = craneLib.mkCargoDerivation (
            commonArgs
            // {
              pnameSuffix = "-codegen-check";
              inherit cargoArtifacts;
              buildPhaseCargoCommand = ''
                cargo run -p rustsat-codegen -- --check
              '';
            }
          );
          readmes = craneLib.mkCargoDerivation (
            commonArgs
            // {
              pnameSuffix = "-readmes";
              inherit cargoArtifacts;
              nativeBuildInputs = with pkgs; [ cargo-rdme ];
              buildPhaseCargoCommand = ''
                cargo rdme --check
                cargo rdme --check --workspace-project pigeons
                cargo rdme --check --workspace-project rustsat-batsat
                cargo rdme --check --workspace-project rustsat-cadical
                cargo rdme --check --workspace-project rustsat-capi
                cargo rdme --check --workspace-project rustsat-glucose
                cargo rdme --check --workspace-project rustsat-ipasir
                cargo rdme --check --workspace-project rustsat-kissat
                cargo rdme --check --workspace-project rustsat-minisat
                cargo rdme --check --workspace-project rustsat-pyapi
                cargo rdme --check --workspace-project rustsat-tools
              '';
            }
          );
          spellcheck = stdenv.mkDerivation {
            name = "cargo-spellcheck-check";
            nativeBuildInputs = with pkgs; [ cargo-spellcheck ];
            doCheck = true;
            unpackPhase = "true";
            buildPhase = ''
              mkdir -p $out
            '';
            checkPhase = ''
              mkdir -p .cache
              HOME=$PWD cargo-spellcheck --code 1 check
            '';
          };
          typosCheck = stdenv.mkDerivation {
            name = "typos-check";
            nativeBuildInputs = with pkgs; [ typos ];
            doCheck = true;
            unpackPhase = "true";
            buildPhase = ''
              mkdir -p $out
            '';
            checkPhase = ''
              typos
            '';
          };
          featurePowerset = craneLib.mkCargoDerivation (
            commonArgs
            // {
              pname-suffix = "-feature-powerset";
              inherit cargoArtifacts;
              nativeBuildInputs =
                commonArgs.nativeBuildInputs
                ++ (with pkgs; [
                  cargo-hack
                  cargo-nextest
                ]);
              buildPhaseCargoCommand = ''
                cargo hack --feature-powerset --clean-per-run --depth 2 --exclude-features bench nextest run -p rustsat
              '';
            }
          );
          capiValgrind = craneLib.mkCargoDerivation (
            commonArgs
            // {
              pnameSuffix = "-capi-valgrind";
              inherit cargoArtifacts;
              nativeBuildInputs =
                commonArgs.nativeBuildInputs
                ++ (with pkgs; [
                  jq
                  valgrind
                  cargo-nextest
                ]);
              # libtestmimic calling threads is leaking memory
              # C-API tests are only actually build when _executing_ them, so we can't use `--no-run`
              buildPhaseCargoCommand = ''
                cargo nextest run -p rustsat-capi
                for test in capi/tests/*.c; do
                  valgrind ''${CARGO_TARGET_DIR:-target}/tmp/"$(basename -s .c "$test")"
                done
              '';
            }
          );
        in
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays =
              let
                rustPkgs = pkgs.extend (import inputs.rust-overlay);
                toolchain-overlay = final: _super: {
                  rust-toolchain = rustPkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml;
                  rust-toolchain-platform = rustPkgs.makeRustPlatform {
                    cargo = final.rust-toolchain;
                    rustc = final.rust-toolchain;
                  };
                  wasm-toolchain = (rustPkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml).override {
                    targets = [ "wasm32-unknown-unknown" ];
                  };
                };
              in
              [
                toolchain-overlay
                inputs.nur-packages.overlays.default
              ];
          };

          packages = {
            tools = pkgs.callPackage ./tools { };
            inherit doc;
            inherit pyapi;
            inherit pyapiDoc;
            devDeps = cargoArtifacts;
            testCoverage = stdenv.mkDerivation {
              name = "rustsat-test-coverage";
              unpackPhase = "true";
              buildPhase = ''
                mkdir -p $out
                cp ${tests}/coverage.lcov $out/tests.lcov
                cp ${externalCadical}/coverage.lcov $out/external-cadical.lcov
                cp ${externalKissat}/coverage.lcov $out/external-kissat.lcov
                cp ${externalGimsatul}/coverage.lcov $out/external-gimsatul.lcov
                cp ${docTests}/coverage.lcov $out/doc-tests.lcov
                for cov in $out/*.lcov; do
                  substituteInPlace $cov --replace-fail '/build/source/' './'
                done
              '';
            };
            pages = stdenv.mkDerivation {
              name = "rustsat-pages";
              unpackPhase = "true";
              buildPhase = ''
                mkdir -p $out
                cp -r ${doc}/share/doc $out/main
                cp -r ${pyapiDoc}/share/doc $out/pyapi
              '';
            };
          };

          devShells =
            let
              mkBaseShell =
                { nativeBuildInputs, ... }@args:
                pkgs.mkShell.override { inherit stdenv; } (
                  {
                    nativeBuildInputs =
                      (with pkgs; [
                        just
                        jq
                        llvmPackages.bintools
                        pkg-config
                        clang
                        cmake
                      ])
                      ++ nativeBuildInputs;
                    buildInputs = libs;
                    LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
                    LD_LIBRARY_PATH = lib.makeLibraryPath libs;
                    PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
                  }
                  // (builtins.removeAttrs args [ "nativeBuildInputs" ])
                );
            in
            {
              default = mkBaseShell {
                nativeBuildInputs = with pkgs; [
                  rust-toolchain
                  cargo-rdme
                  cargo-nextest
                  cargo-hack
                  cargo-spellcheck
                  cargo-llvm-cov
                  cargo-valgrind
                  valgrind
                  release-plz
                  maturin
                  kani
                  veripb
                  typos
                  rust-cbindgen
                  config.treefmt.build.wrapper
                ];
                VERIPB_CHECKER = lib.getExe pkgs.veripb;
                RS_EXT_SOLVER = lib.getExe' pkgs.cadical "cadical";
              };
              semverChecks = mkBaseShell {
                nativeBuildInputs = with pkgs; [
                  # use the stable toolchain here for compatibility with semver-checks
                  cargo
                  cargo-semver-checks
                ];
              };
              releasePlz = mkBaseShell {
                nativeBuildInputs = with pkgs; [
                  # use the stable toolchain here for compatibility with semver-checks
                  cargo
                  cargo-semver-checks
                  release-plz
                ];
              };
              ci = mkBaseShell {
                nativeBuildInputs = with pkgs; [
                  rust-toolchain
                  cargo-hack
                  cargo-nextest
                  craneLib.inheritCargoArtifactsHook
                ];
                inherit cargoArtifacts;
                shellHook = ''
                  rm -rf "$CARGO_TARGET_DIR"
                  inheritCargoArtifacts
                '';
                CARGO_TARGET_DIR = "./target-ci/";
              };
            };

          checks = {
            inherit
              tests
              externalCadical
              externalKissat
              externalGimsatul
              doc
              docTests
              pyapi
              clippy
              codegen
              readmes
              spellcheck
              featurePowerset
              msrv
              capiValgrind
              wasm
              ;
            typos = typosCheck;
            cadicalValgrind = crateValgrind "rustsat-cadical";
            kissatValgrind = crateValgrind "rustsat-kissat";
            minisatValgrind = crateValgrind "rustsat-minisat";
            glucoseValgrind = crateValgrind "rustsat-glucose";
          };

          treefmt = {
            settings.global = {
              on-unmatched = "error";
              excludes = [
                "cadical/cppsrc/**"
                "kissat/csrc/**"
                "minisat/cppsrc/minisat/core/**"
                "minisat/cppsrc/minisat/mtl/**"
                "minisat/cppsrc/minisat/simp/**"
                "minisat/cppsrc/minisat/utils/**"
                "minisat/cppsrc/LICENSE"
                "minisat/cppsrc/README"
                "minisat/cppsrc/doc/ReleaseNotes-2.2.0.txt"
                "glucose/cppsrc/core/**"
                "glucose/cppsrc/mtl/**"
                "glucose/cppsrc/parallel/**"
                "glucose/cppsrc/simp/**"
                "glucose/cppsrc/utils/**"
                "glucose/cppsrc/Changelog"
                "glucose/cppsrc/LICENCE"
                "glucose/cppsrc/README.md"
                "**/.gitignore"
                "*.mk"
                "*.png"
                "*.gz"
                "*.bz2"
              ];
            };
            programs = {
              # Rust
              rustfmt = {
                enable = true;
                edition = "2021";
                package = pkgs.rust-toolchain;
              };
              # Cpp
              clang-format = {
                enable = true;
                excludes = [ "capi/rustsat.h" ];
              };
              cmake-format = {
                enable = true;
                includes = [
                  "**/CMakeLists.txt"
                ];
              };
              # Python
              black.enable = true;
              # Spellchecking
              typos.enable = true;
              # Nix
              deadnix.enable = true;
              nixfmt.enable = true;
              # Shell
              shellcheck = {
                enable = true;
                excludes = [ ".envrc" ];
              };
              shfmt.enable = true;
              # TOML
              taplo.enable = true;
              # Github actions
              actionlint.enable = true;
              yamlfmt.enable = true;
              # Justfile
              just.enable = true;
              # Docker
              dockfmt.enable = true;
            };
          };
        };
    });
}
