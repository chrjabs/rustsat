{
  lib,
  pkgs,
  config,
  ...
}:
{
  settings = {
    package = pkgs.prek;

    # For `jj` pre-commit doesn't really make sense, integrate with `jj-pre-push`
    default_stages = [
      "manual"
      "pre-push"
    ];

    hooks =
      let
        exclude_external = [
          # keep-sorted start
          "/vendor/"
          "\\.snap$"
          "^cadical/patches"
          "^data/.+\\.log$"
          # keep-sorted end
        ];
      in
      {
        # Fast checks that modify files, therefore sequential

        trim-trailing-whitespace = {
          enable = true;
          excludes = exclude_external;
          stages = [
            "manual"
            "pre-push"
          ];
          priority = 1;
        };

        end-of-file-fixer = {
          enable = true;
          excludes = exclude_external;
          priority = 2;
        };

        # Fast/medium checks that don't modify in parallel

        # keep-sorted start: block=yes
        action-validator = {
          enable = true;
          priority = 10;
        };
        actionlint = {
          enable = true;
          priority = 10;
        };
        cargo-deny = {
          enable = true;
          entry = "${lib.getExe pkgs.cargo-deny} --exclude-unpublished --exclude-dev check";
          pass_filenames = false;
          priority = 10;
        };
        cargo-machete = {
          enable = true;
          entry = "${lib.getExe pkgs.cargo-machete}";
          pass_filenames = false;
          priority = 10;
        };
        codegen = {
          enable = true;
          entry = "${lib.getExe' pkgs.rust-toolchain "cargo"} run -p rustsat-codegen -- --check";
          files = "^codegen/";
          pass_filenames = false;
          priority = 10;
        };
        readmes = {
          enable = true;
          entry = lib.getExe (
            pkgs.writeShellScriptBin "check-readmes" ''
              #!/usr/bin/env -S bash -euo pipefail

              CHECKER=${lib.getExe pkgs.cargo-rdme}

              for lib in $@; do
                case $lib in
                  "README.md" | "src/lib.rs")
                    "$CHECKER" --check
                    ;;
                  "pigeons/README.md" | "pigeons/src/lib.rs")
                    "$CHECKER" --check --workspace-project pigeons
                    ;;
                  "*/README.md" | "*/src/lib.rs")
                    subcrate=$(dirname $(dirname $lib))
                    "$CHECKER" --check --workspace-project "rustsat-$subcrate"
                    ;;
                esac
                if [ $? -ne 0 ]; then
                  echo "README not up to date for: $lib"
                fi
              done
            ''
          );
          files = "(lib\\.rs|README\\.md)";
          excludes = [ "^codegen/src/lib\\.rs" ];
        };
        spellcheck = {
          enable = true;
          entry = "${lib.getExe pkgs.cargo-spellcheck} check --code 1";
          files = "(\\.rs$|README\\.md$)";
          excludes = exclude_external;
          priority = 10;
        };
        treefmt = {
          enable = true;
          package = config.treefmt.build.wrapper;
          priority = 10;
        };
        typos = {
          enable = true;
          priority = 10;
        };
        # keep-sorted end

        # Expensive tests that are parallelized by themselves

        clippy = {
          enable = true;
          packageOverrides = {
            cargo = pkgs.rust-toolchain;
            clippy = pkgs.rust-toolchain;
          };
          settings = {
            denyWarnings = true;
            extraArgs = lib.strings.concatStringsSep " " [
              "--workspace"
              "--all-targets"
              "--target-dir=target/clippy"
              "--features=_test"
            ];
          };
          priority = 20;
        };

        tests = {
          enable = true;
          files = "\\.rs|\\.snap$$";
          pass_filenames = false;
          entry = ''
            ${lib.getExe' pkgs.rust-toolchain "cargo"} nextest run \
              --workspace --exclude rustsat-pyapi --features=_test
          '';
          priority = 21;
        };
      };
  };
}
