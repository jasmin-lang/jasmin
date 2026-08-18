{ stdenv, lib, fetchFromGitHub, coqPackages, ocaml, dune }:

let inherit (coqPackages) coq; in

let rev = "3df23a6ea0bffdeaf9211368cf6d4b46e2d0ebd0"; in

stdenv.mkDerivation rec {
  version = "3.5-git-${builtins.substring 0 8 rev}";
  pname = "coq${coq.coq-version}-mathcomp-word";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    hash = "sha256-tPrVwYn783LKzkbW0aDX3frpgW7uFOh/z0wOZQhZaao=";
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
