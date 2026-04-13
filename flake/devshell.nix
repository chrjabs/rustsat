flake-args: {
  perSystem =
    {
      lib,
      pkgs,
      self',
      config,
      ...
    }:
    let
      libDeps = flake-args.config.flake.shared.libDeps pkgs;
    in
    {
      devShells = {
        base = pkgs.mkShell.override { stdenv = pkgs.clangStdenv; } {
          nativeBuildInputs = with pkgs; [
            # keep-sorted start
            clang
            cmake
            jq
            llvmPackages.bintools
            pkg-config
            # keep-sorted end
          ];
          buildInputs = libDeps;
          LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
          LD_LIBRARY_PATH = lib.makeLibraryPath libDeps;
          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";
          shellHook = ''
            export CC=${lib.getExe pkgs.clang}
            export CXX=${lib.getExe' pkgs.clang "clang++"}
          '';
        };

        default = self'.devShells.base.overrideAttrs (prevAttrs: {
          nativeBuildInputs =
            prevAttrs.nativeBuildInputs
            ++ (with pkgs; [
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
              just
              kani
              maturin
              release-plz
              rust-cbindgen
              self'.packages.rust-toolchain
              typos
              valgrind
              veripb
              # keep-sorted end
            ]);
          VERIPB_CHECKER = lib.getExe pkgs.veripb;
          RS_EXT_SOLVER = lib.getExe' pkgs.cadical "cadical";
          JJ_PRE_PUSH_CHECKER = lib.getExe pkgs.prek;
          shellHook = prevAttrs.shellHook + config.pre-commit.shellHook;
        });
      };
    };
}
