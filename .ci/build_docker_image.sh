#!/bin/bash

set -e

nix-channel --add https://nixos.org/channels/nixpkgs-unstable nixpkgs
nix-channel --update

nix-env -iA nixpkgs.docker

nix-build default.nix --argstr imageName gcr.io/oak-ci/oak-hardware

docker load < result
docker push gcr.io/oak-ci/oak-hardware:latest
