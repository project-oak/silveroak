{ pkgs ? import ./nix/packages.nix {} }:
(import ./default.nix { inherit pkgs; }).cava-shell
