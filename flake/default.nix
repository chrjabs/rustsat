inputs:
{
  pkgs,
  system,
  ...
}@args:
let

  shared = import ./shared.nix (args // { inherit inputs; });
in
{
  _module.args.pkgs = import inputs.nixpkgs {
    inherit system;
    overlays =
      let
        rustPkgs = pkgs.extend (import inputs.rust-overlay);
        toolchain-overlay = final: _super: {
          rust-toolchain = rustPkgs.rust-bin.fromRustupToolchainFile ../rust-toolchain.toml;
          rust-toolchain-platform = rustPkgs.makeRustPlatform {
            cargo = final.rust-toolchain;
            rustc = final.rust-toolchain;
          };
          wasm-toolchain = (rustPkgs.rust-bin.fromRustupToolchainFile ../rust-toolchain.toml).override {
            targets = [ "wasm32-unknown-unknown" ];
          };
        };
      in
      [
        toolchain-overlay
        inputs.nur-packages.overlays.default
      ];
  };

  packages = import ./packages.nix (args // shared);

  devShells = import ./devshells.nix (args // shared);

  checks = import ./checks.nix (args // shared // { inherit inputs; });

  treefmt = import ./treefmt.nix args;
}
