{ sources ? import ./nix/sources.nix
, pkgs ? import ./nix/packages.nix { inherit sources; }
}:

let
  tools = with pkgs; [
    # Building
    coq_8_11
    coqPackages_8_11.coq-ext-lib
    (haskell.packages.ghc865.ghcWithPackages (pkgs: with pkgs; [Cabal]))

    # Simulation
    verilog #iverilog
    verilator

    # Common tools
    gcc
    git
    gnumake
    stdenv
    coreutils
    findutils
    bash
    binutils.bintools
  ];
in
rec {
  cava-shell = pkgs.mkShell {
      name = "cava-shell";
      buildInputs = tools;
    };

  docker-image-build = pkgs.dockerTools.buildLayeredImage {
    name = "gcr.io/oak-ci/oak-hardware";
    tag = "latest";
    contents = tools;
    config = {
      WorkingDir = "/workspace";
      Volumes = {
        "/workspace" = {};
        "/tmp" = {};
      };
      # Fix COQPATH for docker image as this isn't propogated.
      Env = [
        "COQPATH=${pkgs.coqPackages_8_11.coq-ext-lib}/lib/coq/8.11/user-contrib"
      ];
    };
    maxLayers = 120;
  };
}

