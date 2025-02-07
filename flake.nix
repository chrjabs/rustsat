{
  description = "Rust library for tools and encodings related to SAT solving library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    systems.url = "github:nix-systems/default-linux";

    rust-overlay.url = "github:oxalica/rust-overlay";
    rust-overlay.inputs.nixpkgs.follows = "nixpkgs";

    nix-tools.url = "github:gleachkr/nix-tools";
    nix-tools.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs @ {
    self,
    nixpkgs,
    systems,
    rust-overlay,
    nix-tools,
  }: let
    lib = nixpkgs.lib;
    pkgsFor = lib.genAttrs (import systems) (system: (import nixpkgs {
      inherit system;
      overlays = [(import rust-overlay) nix-tools.overlays.default];
    }));
    forEachSystem = f: lib.genAttrs (import systems) (system: f pkgsFor.${system});
  in {
    devShells = forEachSystem (pkgs: {
      default = let
        libs = with pkgs; [openssl xz bzip2];
      in
        pkgs.mkShell rec {
          nativeBuildInputs = with pkgs; [
            llvmPackages_12.bintools
            pkg-config
            clang
            cmake
            (rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)
            cargo-rdme
            cargo-nextest
            release-plz
            jq
            maturin
            kani
          ];
          buildInputs = libs;
          LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath libs;
          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig/";
        };
    });

    packages = forEachSystem (pkgs: {
      tools = pkgs.callPackage ./tools {};
    });
  };
}
