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
      "cadical/cppsrc/**"
      "glucose/cppsrc/Changelog"
      "glucose/cppsrc/LICENCE"
      "glucose/cppsrc/README.md"
      "glucose/cppsrc/core/**"
      "glucose/cppsrc/mtl/**"
      "glucose/cppsrc/parallel/**"
      "glucose/cppsrc/simp/**"
      "glucose/cppsrc/utils/**"
      "kissat/csrc/**"
      "minisat/cppsrc/LICENSE"
      "minisat/cppsrc/README"
      "minisat/cppsrc/doc/ReleaseNotes-2.2.0.txt"
      "minisat/cppsrc/minisat/core/**"
      "minisat/cppsrc/minisat/mtl/**"
      "minisat/cppsrc/minisat/simp/**"
      "minisat/cppsrc/minisat/utils/**"
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
