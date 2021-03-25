{ sources ? import ./nix/sources.nix
, pkgs ? import ./nix/packages.nix { inherit sources; }
}:

let
  tools = with pkgs; [
    # Building
    coq_8_12
    (haskell.packages.ghc8104.ghcWithPackages (pkgs: with pkgs; [Cabal]))
    gcc
    verilator

    # Common tools
    git
    gnumake
    bash
    stdenv
    coreutils
    findutils
    diffutils
    binutils.bintools
  ];
in
rec {
  cava-shell = pkgs.mkShell {
      name = "cava-shell";
      buildInputs = tools;
    };

  silveroak-image = pkgs.dockerTools.buildLayeredImage {
    name = "gcr.io/oak-ci/silveroak";
    tag = "latest";
    contents = tools;
    config = {
      WorkingDir = "/workspace";
      Volumes = {
        "/workspace" = {};
        "/tmp" = {};
      };
    };
    maxLayers = 120;
  };
}

