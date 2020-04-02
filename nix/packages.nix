{ sources ? import ./sources.nix }:
import sources.nixpkgs {
  overlays = [
    (_: pkgs: { inherit sources; })
    (_: pkgs: { verilator = pkgs.callPackage ./verilator.nix {}; })
  ];
  config = {};
}
