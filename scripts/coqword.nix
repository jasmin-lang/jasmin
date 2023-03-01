{ stdenv, lib, fetchFromGitHub, coqPackages, ocaml, dune_3 }:

let inherit (coqPackages) coq; in

let mathcomp = coqPackages.mathcomp.override { version = "1.15.0"; }
; in

let rev = "bbab8bb37bfe3c7e83753d681fd35c89295b2fa2"; in

stdenv.mkDerivation rec {
  version = "2.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    hash = "sha256-oN/zvnePq64Nt7l/zIDLdhb4t9ayKxnZCsn+pzqS030=";
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
