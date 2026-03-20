{ pkgs, ... }:
{
  settings.global = {
    on-unmatched = "error";
    excludes = [
      # keep-sorted start
      "**/.gitignore"
      "*.bz2"
      "*.gz"
      "*.mk"
      "*.png"
      "cadical/vendor/**"
      "glucose/vendor/Changelog"
      "glucose/vendor/LICENCE"
      "glucose/vendor/README.md"
      "glucose/vendor/core/**"
      "glucose/vendor/mtl/**"
      "glucose/vendor/parallel/**"
      "glucose/vendor/simp/**"
      "glucose/vendor/utils/**"
      "kissat/vendor/**"
      "minisat/vendor/LICENSE"
      "minisat/vendor/README"
      "minisat/vendor/doc/ReleaseNotes-2.2.0.txt"
      "minisat/vendor/minisat/core/**"
      "minisat/vendor/minisat/mtl/**"
      "minisat/vendor/minisat/simp/**"
      "minisat/vendor/minisat/utils/**"
      # keep-sorted end
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
      includes = [ "**/CMakeLists.txt" ];
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
    # Sorting lists
    keep-sorted.enable = true;
  };
}
