{ stdenv, lib, fetchFromGitHub, coqPackages, ocaml, dune_3 }:

let inherit (coqPackages) coq; in

let mathcomp = coqPackages.mathcomp.override { version = "2.2.0"; }
; in

let rev = "1abe5ade5240115aed1e3c140e261f1554af2322"; in

stdenv.mkDerivation rec {
  version = "3.2-git-${builtins.substring 0 8 rev}";
  pname = "coq${coq.coq-version}-mathcomp-word";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    hash = "sha256-s6UD9aYsaRXlxMNxkZGD/yZx1rlDVqJLU1mLfJAg6To=";
  };

  buildInputs = [ coq ocaml dune_3 ];

  propagatedBuildInputs = [ mathcomp.algebra mathcomp.fingroup mathcomp.ssreflect ];

  buildPhase = ''
    runHook preBuild
    dune build -p coq-mathcomp-word
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    dune install --prefix=$out
    mkdir -p $out/lib/coq/${coq.coq-version}/
    mv $out/lib/coq/user-contrib $out/lib/coq/${coq.coq-version}/
    runHook postInstall
  '';

  meta = {
    description = "Yet Another Coq Library on Machine Words";
    license = lib.licenses.mit;
    inherit (src.meta) homepage;
    inherit (coq.meta) platforms;
  };
}
