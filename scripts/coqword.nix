{ stdenv, lib, fetchFromGitHub, coqPackages, ocaml, dune_2 }:

let inherit (coqPackages) coq; in

let mathcomp = coqPackages.mathcomp.override { version = "1.12.0"; }
; in

let rev = "a97b482de0c00e305f5bdd5250e327965efb2118"; in

stdenv.mkDerivation rec {
  version = "1.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "sha256:108sbslvj4rgzq2fr79li9bxiv08d05v5y9n223wqzwws0dqvag9";
  };

  buildInputs = [ coq ocaml dune_2 ];

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
    license = lib.licenses.cecill-b;
    inherit (src.meta) homepage;
    inherit (coq.meta) platforms;
  };
}
