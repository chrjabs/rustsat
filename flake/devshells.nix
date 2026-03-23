{
  lib,
  pkgs,
  config,
  # from shared
  stdenv,
  libDeps,
  craneLib,
  cargoArtifacts,
  ...
}:
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
        buildInputs = libDeps;
        LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
        LD_LIBRARY_PATH = lib.makeLibraryPath libDeps;
        PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
        shellHook = ''
          export CC=${lib.getExe pkgs.clang}
          export CXX=${lib.getExe' pkgs.clang "clang++"}
        '';
      }
      // (builtins.removeAttrs args [ "nativeBuildInputs" ])
    );
in
{
  default = mkBaseShell {
    nativeBuildInputs = with pkgs; [
      # keep-sorted start
      cargo-deny
      cargo-hack
      cargo-insta
      cargo-llvm-cov
      cargo-machete
      cargo-nextest
      cargo-rdme
      cargo-show-asm
      cargo-spellcheck
      cargo-udeps
      cargo-valgrind
      config.treefmt.build.wrapper
      git-cliff
      gungraun-runner
      kani
      maturin
      release-plz
      rust-cbindgen
      rust-toolchain
      typos
      valgrind
      veripb
      # keep-sorted end
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
  cargoDeny = mkBaseShell {
    nativeBuildInputs = with pkgs; [
      cargo-deny
      rust-toolchain
    ];
  };
  ci = mkBaseShell {
    nativeBuildInputs = with pkgs; [
      # keep-sorted start
      cargo-hack
      cargo-nextest
      craneLib.inheritCargoArtifactsHook
      rust-toolchain
      # keep-sorted end
    ];
    inherit cargoArtifacts;
    shellHook = ''
      rm -rf "$CARGO_TARGET_DIR"
      inheritCargoArtifacts
    '';
    CARGO_TARGET_DIR = "./target-ci/";
  };
}
