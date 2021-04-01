{ lib, buildDunePackage, fetchFromGitHub
, ocaml, findlib, pkg-config
, gmp, dune_2, ocamlPackages, coq_8_13
}:


let coq = coq_8_13; in
buildDunePackage rec {
  pname = "koika";
  version = "0.0.1";
  src = fetchFromGitHub {
    owner = "mit-plv";
    repo = "koika";
    rev = "61c3587b5b5ee46b39ef1723e816fe7f6b6a609e";
    sha256 = "0iq39qbqyxc9giqsfjx7b2jxyf5pn0y58x7y00s70k3acaj697kq";
    fetchSubmodules = true;
  };
  useDune2 = true;
  minimumOCamlVersion = "4.06";

  nativeBuildInputs = [coq_8_13];
  propagatedBuildInputs = with ocamlPackages; [ zarith ppx_jane core parsexp (ocamlPackages.callPackage (import ./hashcons.nix) {}) ];

  postInstall = ''
      mv $out/lib/ocaml/${ocaml.version}/site-lib/coq $out/lib/TEMPORARY
      mkdir $out/lib/coq/
      mv $out/lib/TEMPORARY $out/lib/coq/${coq.coq-version}
    '';
  installFlags =
    [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
}
