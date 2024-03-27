{ stdenv, lib, fetchFromGitHub, coqPackages, ocaml, dune_3 }:

let inherit (coqPackages) coq; in

let mathcomp = coqPackages.mathcomp.override { version = "2.1.0"; }
; in

let rev = "a7f2d08c132e09c036521768ea511b70c2023e9e"; in

stdenv.mkDerivation rec {
  version = "3.1-git-${builtins.substring 0 8 rev}";
  pname = "coq${coq.coq-version}-mathcomp-word";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    hash = "sha256-vrirhOCLwD+oCyqUe6cDDA2aoIlvNoml70jYSrvw0uE=";
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
