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
        in
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays =
              let
                toolchain-overlay = _: super: {
                  rust-toolchain = super.symlinkJoin {
                    name = "rust-toolchain";
                    paths = [
                      ((pkgs.extend (import inputs.rust-overlay)).rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)
                    ];
                    buildInputs = [ super.makeWrapper ];
                    postBuild = ''
                      wrapProgram $out/bin/cargo --set LIBCLANG_PATH ${super.libclang.lib}/lib
                    '';
                  };
                };
              in
              [
                toolchain-overlay
                inputs.nur-packages.overlays.default
              ];
          };

          packages.tools = pkgs.callPackage ./tools { };

          devShells.default =
            let
              libs = with pkgs; [
                openssl
                xz
                bzip2
              ];
            in
            pkgs.mkShell.override { stdenv = pkgs.clangStdenv; } rec {
              nativeBuildInputs = with pkgs; [
                llvmPackages.bintools
                pkg-config
                clang
                cmake
                rust-toolchain
                cargo-rdme
                cargo-nextest
                cargo-semver-checks
                cargo-hack
                cargo-spellcheck
                cargo-llvm-cov
                cargo-valgrind
                valgrind
                just
                release-plz
                jq
                maturin
                kani
                veripb
                typos
                rust-cbindgen
                config.treefmt.build.wrapper
              ];
              buildInputs = libs;
              LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
              LD_LIBRARY_PATH = lib.makeLibraryPath libs;
              PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig/";
              VERIPB_CHECKER = lib.getExe pkgs.veripb;
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
