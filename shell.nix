{ pkgs ? import ./nix/packages.nix {}, buildVerilator ? true }:
(import ./default.nix { inherit pkgs buildVerilator; }).cava-shell
