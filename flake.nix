{
  description = "Rust library for tools and encodings related to SAT solving library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    systems.url = "github:nix-systems/default";

    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";

    nix-config.url = "github:chrjabs/nix-config";
    nix-config.inputs.nixpkgs.follows = "nixpkgs";
    nix-config.inputs.rust-overlay.follows = "rust-overlay";

    git-hooks.url = "github:chrjabs/git-hooks.nix";
    git-hooks.inputs.nixpkgs.follows = "nixpkgs";

    nix-github-actions.url = "github:nix-community/nix-github-actions";
    nix-github-actions.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = {
    self,
    nixpkgs,
    systems,
    rust-overlay,
    nix-config,
    git-hooks,
    nix-github-actions,
  }: let
    lib = nixpkgs.lib;
    forAllSystems = lib.genAttrs (import systems);
    pkgsFor = rust-overlay-fn:
      lib.genAttrs (import systems) (system: (import nixpkgs {
        inherit system;
        overlays = [(import rust-overlay) rust-overlay-fn] ++ builtins.attrValues nix-config.overlays;
      }));
    rust-toolchain-overlay = _: super: {
      rust-toolchain = super.symlinkJoin {
        name = "rust-toolchain";
        paths = [(super.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)];
        buildInputs = [super.makeWrapper];
        postBuild = ''
          wrapProgram $out/bin/cargo --set LIBCLANG_PATH ${super.libclang.lib}/lib
        '';
      };
    };
    devShellSystemRustOverlay = system: rust-overlay-fn: let
      pkgs = (pkgsFor rust-overlay-fn).${system};
      libs = with pkgs; [openssl xz bzip2];
    in
      pkgs.mkShell.override {stdenv = pkgs.clangStdenv;} rec {
        inherit (self.checks.${system}.pre-commit-check) shellHook;
        nativeBuildInputs = with pkgs;
          [
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
            pboxide
            typos
            rust-cbindgen
          ]
          ++ self.checks.${system}.pre-commit-check.enabledPackages;
        buildInputs = libs;
        LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
        LD_LIBRARY_PATH = lib.makeLibraryPath libs;
        PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig/";
        VERIPB_CHECKER = lib.getExe pkgs.pboxide;
      };
  in {
    devShells = forAllSystems (system: {
      default = devShellSystemRustOverlay system rust-toolchain-overlay;
    });

    packages = forAllSystems (system: {
      tools = (pkgsFor rust-toolchain-overlay).${system}.callPackage ./tools {};
    });

    checks = forAllSystems (system: {
      pre-commit-check = let
        pkgs = (pkgsFor rust-toolchain-overlay).${system};
      in
        git-hooks.lib.${system}.run {
          src = ./.;
          tools.cargo = pkgs.rust-toolchain;
          settings.rust.check.cargoDeps = pkgs.rustPlatform.importCargoLock {lockFile = ./Cargo.lock;};
          hooks = {
            # Rust
            cargo-check = {
              enable = true;
              args = ["--workspace"];
              extraPackages = with pkgs; [
                pkg-config
                clang
                cmake
                openssl
                libclang
              ];
            };
            rustfmt.enable = true;
            # Just hooks
            just-precommit = {
              enable = true;
              name = "just precommit";
              entry = "${lib.getExe pkgs.just} precommit";
              language = "system";
              pass_filenames = false;
            };
            just-prepush = {
              enable = true;
              name = "just prepush";
              entry = "${lib.getExe pkgs.just} prepush";
              language = "system";
              pass_filenames = false;
              stages = ["pre-push"];
            };
            # TOML
            check-toml.enable = true;
            taplo.enable = true;
            # Github actions
            actionlint.enable = true;
            check-yaml.enable = true;
            # Nix
            alejandra.enable = true;
            deadnix.enable = true;
            # Python
            black.enable = true;
            # General neatness
            check-added-large-files.enable = true;
            end-of-file-fixer = {
              enable = true;
              excludes = [".+\\.(patch|log)$" "cadical/cppsrc/.+" "kissat/csrc/.+"];
            };
            trim-trailing-whitespace = {
              enable = true;
              excludes = [".+\\.(patch|log)$" "cadical/cppsrc/.+" "kissat/csrc/.+"];
            };
            check-symlinks.enable = true;
            no-commit-to-branch.enable = true;
          };
        };
    });

    githubActions = nix-github-actions.lib.mkGithubMatrix {
      checks = self.checks // self.packages;
    };
  };
}
