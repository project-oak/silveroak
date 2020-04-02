#!/bin/bash

set -e

nix-channel --add https://nixos.org/channels/nixos-20.03
nix-channel --update


# TODO: remove makefile dependence on git so this can be removed
nix-env -iA nixpkgs.git
git init
git add .

nix-build --max-jobs 16 --cores 16 -A docker-image-build

nix-env -iA nixpkgs.docker

docker load < result
