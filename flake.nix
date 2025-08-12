{
  description = "Rust library for tools and encodings related to SAT solving library";

  nixConfig = {
    extra-substituters = [
      "https://chrjabs.cachix.org"
    ];
    extra-trusted-public-keys = [
      "chrjabs.cachix.org-1:hnjWCdXP+IWya+Y+/xTwyfpNtwOlbR0X3/9OqyLoE1o="
    ];
  };

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

          craneLib = (inputs.crane.mkLib pkgs).overrideToolchain (p: p.rust-toolchain);
          craneLibStable = inputs.crane.mkLib pkgs;
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
          };
          cargoArtifacts = craneLib.buildDepsOnly (commonArgs // { CARGO_PROFILE = "release"; });
          cargoDevArtifacts = craneLib.buildDepsOnly commonArgs;
          cargoDevArtifactsStable = craneLibStable.buildDepsOnly commonArgs;

          crateEachFeature =
            {
              crate,
              excludeFeatures ? [ ],
            }:
            craneLib.mkCargoDerivation (
              commonArgs
              // {
                pname = "${crate}-each-feature";
                cargoArtifacts = cargoDevArtifacts;
                nativeBuildInputs =
                  commonArgs.nativeBuildInputs
                  ++ (with pkgs; [
                    cargo-hack
                    cargo-nextest
                  ]);
                buildPhaseCargoCommand = ''
                  cargo hack --each-feature ${
                    builtins.concatStringsSep " " (map (feat: "--exclude-feature ${feat}") excludeFeatures)
                  }nextest run -p ${crate} --profile ci
                '';
              }
            );
          crateValgrind =
            crate:
            craneLib.mkCargoDerivation (
              commonArgs
              // {
                pname = "${crate}-valgrind";
                cargoArtifacts = cargoDevArtifacts;
                nativeBuildInputs =
                  commonArgs.nativeBuildInputs
                  ++ (with pkgs; [
                    cargo-valgrind
                    cargo-nextest
                  ]);
                buildPhaseCargoCommand = ''
                  cargo valgrind nextest run --profile ci -p ${crate}
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
                };
              in
              [
                toolchain-overlay
                inputs.nur-packages.overlays.default
              ];
          };

          packages = {
            tools = pkgs.callPackage ./tools { };
            devDeps = cargoDevArtifacts;
            deps = cargoArtifacts;
          };

          devShells =
            let
              libs = with pkgs; [
                openssl
                xz
                bzip2
              ];
              defBuildInputs = with pkgs; [
                just
                jq
                llvmPackages.bintools
                pkg-config
                clang
                cmake
              ];
              mkBaseShell =
                args:
                pkgs.mkShell.override { stdenv = pkgs.clangStdenv; } (
                  {
                    nativeBuildInputs = defBuildInputs ++ args.extraNativeBuildInputs;
                    buildInputs = libs;
                    LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
                    LD_LIBRARY_PATH = lib.makeLibraryPath libs;
                    PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
                  }
                  // args
                );
            in
            {
              default = mkBaseShell {
                extraNativeBuildInputs = with pkgs; [
                  rust-toolchain
                  cargo-rdme
                  cargo-nextest
                  cargo-semver-checks
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
            };

          checks = {
            tests = craneLib.cargoNextest (
              commonArgs
              // {
                cargoArtifacts = cargoDevArtifacts;
                cargoNextestPartitionsExtraArgs = "--profile ci --exclude rustsat-pyapi";
                nativeBuildInputs = commonArgs.nativeBuildInputs ++ (with pkgs; [ jq ]);
              }
            );
            clippy = craneLib.cargoClippy (
              commonArgs
              // {
                cargoArtifacts = cargoDevArtifacts;
                cargoClippyExtraArgs = "--all-targets -- --deny warnings";
              }
            );
            doc = craneLib.cargoDoc (
              commonArgs
              // {
                cargoArtifacts = cargoDevArtifacts;
                cargoDocExtraArgs = "--no-deps -Zunstable-options -Zrustdoc-scrape-examples";
                env.RUSTDOCFLAGS = "--deny warnings";
              }
            );
            docTests = craneLib.cargoDocTest (
              commonArgs
              // {
                cargoArtifacts = cargoDevArtifacts;
                cargoTestExtraArgs = "--exclude rustsat-capi --exclude rustsat-pyapi";
              }
            );
            codegen = craneLib.mkCargoDerivation (
              commonArgs
              // {
                pname = "rustsat-codegen-check";
                cargoArtifacts = cargoDevArtifacts;
                buildPhaseCargoCommand = ''
                  cargo run -p rustsat-codegen -- --check
                '';
              }
            );
            readmes = craneLib.mkCargoDerivation (
              commonArgs
              // {
                pname = "rustsat-readmes";
                cargoArtifacts = cargoDevArtifacts;
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
            spellcheck = pkgs.stdenv.mkDerivation {
              inherit src;
              name = "cargo-spellcheck-check";
              nativeBuildInputs = with pkgs; [ cargo-spellcheck ];
              doCheck = true;
              buildPhase = ''
                mkdir -p $out
              '';
              checkPhase = ''
                mkdir -p .cache
                HOME=$PWD cargo-spellcheck --code 1 check
              '';
            };
            typos = pkgs.stdenv.mkDerivation {
              inherit src;
              name = "typos-check";
              nativeBuildInputs = with pkgs; [ typos ];
              doCheck = true;
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
                pname = "rustsat-feature-powerset";
                cargoArtifacts = cargoDevArtifacts;
                nativeBuildInputs =
                  commonArgs.nativeBuildInputs
                  ++ (with pkgs; [
                    cargo-hack
                    cargo-nextest
                  ]);
                buildPhaseCargoCommand = ''
                  cargo hack --feature-powerset --depth 2 --exclude-features bench nextest run -p rustsat --exclude-features bench --profile ci
                '';
              }
            );
            cadicalEachFeature = crateEachFeature {
              crate = "rustsat-cadical";
              excludeFeatures = [ "logging" ];
            };
            kissatEachFeature = crateEachFeature {
              crate = "rustsat-kissat";
            };
            cadicalValgrind = crateValgrind "rustsat-cadical";
            kissatValgrind = crateValgrind "rustsat-kissat";
            minisatValgrind = crateValgrind "rustsat-minisat";
            glucoseValgrind = crateValgrind "rustsat-glucose";
            capiValgrind = craneLib.mkCargoDerivation (
              commonArgs
              // {
                pname = "rustsat-capi-valgrind";
                cargoArtifacts = cargoDevArtifacts;
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
            semverChecks = craneLibStable.mkCargoDerivation (
              commonArgs
              // {
                pname = "rustsat-cargo-semver-checks";
                cargoArtifacts = cargoDevArtifactsStable;
                nativeBuildInputs =
                  commonArgs.nativeBuildInputs
                  ++ (with pkgs; [
                    cargo-semver-checks
                  ]);
                # libtestmimic calling threads is leaking memory
                # C-API tests are only actually build when _executing_ them, so we can't use `--no-run`
                buildPhaseCargoCommand = ''
                  cargo semver-checks --workspace --exclude rustsat-cadical
                  cargo semver-checks -p rustsat-cadical --default-features
                '';
              }
            );
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
