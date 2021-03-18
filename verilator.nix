{ pkgs ? import ./nix/packages.nix {} }:
(import ./default.nix { inherit pkgs; }).verilator-shell
