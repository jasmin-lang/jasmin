{ stdenv, lib, fetchFromGitHub, coqPackages, ocaml, dune_2 }:

let inherit (coqPackages) coq; in

let mathcomp =
 (if coqPackages ? mathcomp_
  then coqPackages.mathcomp_ "1.12.0"
  else coqPackages.mathcomp.override { version = "1.12.0"; }
 ).algebra
; in

let rev = "e39e96d51aa96f386222fd1b38776f2117f325c5"; in

stdenv.mkDerivation rec {
  version = "1.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "sha256:0703m97rnivcbc7vvbd9rl2dxs6l8n52cbykynw61c6w9rhxspcg";
  };

  buildInputs = [ coq ocaml dune_2 ];

  propagatedBuildInputs = [ mathcomp ];

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
