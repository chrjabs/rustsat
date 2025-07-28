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
  };

  outputs = inputs @ {flake-parts, ...}:
    flake-parts.lib.mkFlake {inherit inputs;} (_: {
      systems = ["x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin"];
      perSystem = {
        system,
        pkgs,
        ...
      }: let
        lib = pkgs.lib;
      in {
        _module.args.pkgs = import inputs.nixpkgs {
          inherit system;
          overlays = let
            toolchain-overlay = _: super: {
              rust-toolchain = super.symlinkJoin {
                name = "rust-toolchain";
                paths = [((pkgs.extend (import inputs.rust-overlay)).rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)];
                buildInputs = [super.makeWrapper];
                postBuild = ''
                  wrapProgram $out/bin/cargo --set LIBCLANG_PATH ${super.libclang.lib}/lib
                '';
              };
            };
          in [
            toolchain-overlay
            inputs.nur-packages.overlays.default
          ];
        };

        packages.tools = pkgs.callPackage ./tools {};

        devShells.default = let
          libs = with pkgs; [openssl xz bzip2];
        in
          pkgs.mkShell.override {stdenv = pkgs.clangStdenv;} rec {
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
            ];
            buildInputs = libs;
            LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
            LD_LIBRARY_PATH = lib.makeLibraryPath libs;
            PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig/";
            VERIPB_CHECKER = lib.getExe pkgs.veripb;
          };
      };
    });
}
