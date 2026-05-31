{ stdenv, lib, fetchFromGitHub, coqPackages, ocaml, dune_3 }:

let inherit (coqPackages) coq; in

let rev = "3ba8484ae779a2178ea3c6a470f102a0dd57a8a9"; in

stdenv.mkDerivation rec {
  version = "3.4-git-${builtins.substring 0 8 rev}";
  pname = "coq${coq.coq-version}-mathcomp-word";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    hash = "sha256-M2Yw1aPhJlXhmJJhHpuQZnhGDV4YdJhtc2RwJzqAVcI=";
  };

  buildInputs = [ coq ocaml dune_3 ];

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
