{
  description = "Rust library for tools and encodings related to SAT solving library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    systems.url = "github:nix-systems/default";

    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";

    nix-tools.url = "github:gleachkr/nix-tools";
    nix-tools.inputs.nixpkgs.follows = "nixpkgs";

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
    nix-tools,
    git-hooks,
    nix-github-actions,
  }: let
    lib = nixpkgs.lib;
    forAllSystems = lib.genAttrs (import systems);
    pkgsFor = lib.genAttrs (import systems) (system: (import nixpkgs {
      inherit system;
      overlays = [(import rust-overlay) nix-tools.overlays.default rust-toolchain-overlay];
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
  in {
    devShells = forAllSystems (system: {
      default = let
        pkgs = pkgsFor.${system};
        libs = with pkgs; [openssl xz bzip2];
        git-subtree-cmd =
          pkgs.writeShellScriptBin "git-subtree"
          /*
          bash
          */
          ''
            SUBTREE="$1"
            CMD="$2"
            REF="$3"

            declare -A prefixes
            prefixes=(
              ["minisat"]="minisat/cppsrc"
              ["glucose"]="glucose/cppsrc"
              ["cadical"]="cadical/cppsrc"
              ["kissat"]="kissat/csrc"
            )

            case $CMD in
              pull)
                echo "Pulling subtree $SUBTREE from ref $REF"
                git subtree pull --prefix "''${prefixes[$SUBTREE]}" "$SUBTREE" "$REF" --squash -m "chore($SUBTREE): update subtree"
                ;;

              push)
                echo "Pushing subtree $SUBTREE to ref $REF"
                git subtree push --prefix "''${prefixes[$SUBTREE]}" "$SUBTREE" "$REF"
                ;;

              *)
                2>&1 echo "Unknown command $CMD"
                2>&1 echo "Usage: git-subtree <subtree> <command> <ref>"
            esac
          '';
      in
        pkgs.mkShell.override {stdenv = pkgs.clangStdenv;} rec {
          inherit (self.checks.${system}.pre-commit-check) shellHook;
          nativeBuildInputs = with pkgs;
            [
              llvmPackages_12.bintools
              pkg-config
              clang
              cmake
              rust-toolchain
              cargo-rdme
              cargo-nextest
              release-plz
              jq
              maturin
              kani
              git-subtree-cmd
            ]
            ++ self.checks.${system}.pre-commit-check.enabledPackages;
          buildInputs = libs;
          LIBCLANG_PATH = "${pkgs.libclang.lib}/lib";
          LD_LIBRARY_PATH = lib.makeLibraryPath libs;
          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig/";
        };
    });

    packages = forAllSystems (system: {
      tools = pkgsFor.${system}.callPackage ./tools {};
    });

    checks = forAllSystems (system: {
      pre-commit-check = let
        pkgs = pkgsFor.${system};
      in
        git-hooks.lib.${system}.run {
          src = ./.;
          tools.cargo = pkgs.rust-toolchain;
          settings.rust.check.cargoDeps = pkgs.rustPlatform.importCargoLock {lockFile = ./Cargo.lock;};
          hooks = let
            cargo-spellcheck = lib.getExe pkgs.cargo-spellcheck;
          in {
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
            cargo-spellcheck = {
              enable = true;
              name = "Spellchecking documentation";
              entry = "${cargo-spellcheck} --code 1";
              language = "system";
              files = "(.+\\.rs|docs/.+\\.md)$";
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
