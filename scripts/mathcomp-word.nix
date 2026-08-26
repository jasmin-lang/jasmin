{ stdenv, lib, fetchFromGitHub, coqPackages, ocaml, dune }:

let inherit (coqPackages) coq; in

let rev = "86ed49aeca65a8d32e81bb386778f49b45ee505b"; in

stdenv.mkDerivation rec {
  version = "3.5-git-${builtins.substring 0 8 rev}";
  pname = "coq${coq.coq-version}-mathcomp-word";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    hash = "sha256-TdjMp/4Eo9uEcUWhV3OSy/eX1GzQO2nhym3MNTzNvwY=";
  };

  buildInputs = [ coq ocaml dune ];

  propagatedBuildInputs = (with coqPackages.mathcomp; [ algebra fingroup ssreflect ])
  ++ [ coqPackages.stdlib ];

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
