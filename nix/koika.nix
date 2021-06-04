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
    rev = "da0ba135fbaf772d98f93d5f1ebc6a7b971f9042";
    sha256 = "0cc35walqsqc4q8jr14r2x9v71nvzzmlqjf7fiabk13ann5kab25";
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
