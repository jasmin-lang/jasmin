with import <nixpkgs> {};

let coqPackages = coqPackages_8_9; in

let coqword = callPackage ../coqword.nix { inherit coqPackages; }; in
let inherit (coqPackages) coq; in

let jasmin =
stdenv.mkDerivation rec {
  name = "jasmin-20210408";
  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "jasmin";
    rev = "ac5e3c913a56e487abbcf73d3c0214199941269e";
    sha256 = "0s63c055hjxbs1mggnj42qvahzcssjk5c4w3fs7mz6b1x71iscl1";
  };

  buildInputs = [ coq coqword mpfr ppl ]
  ++ (with coq.ocamlPackages; [
    ocaml findlib ocamlbuild
    (batteries.overrideAttrs (_: { doCheck = false; }))
    menhir zarith camlidl apron yojson
  ])
  ;

  buildPhase = ''
    make -j $NIX_BUILD_CORES -C proofs
    make -C compiler CIL build
  '';

  installFlags = [ "PREFIX=$(out)" ];
}; in

let jasmin-ct = jasmin.overrideAttrs (_: {
  name = "jasmin-ct-0.1.0";
  src = fetchFromGitLab {
    owner = "vbgl";
    repo = "jasmin";
    rev = "2d78c8e8d2b6ec89d96dd00d1d549711f7ed8f38";
    sha256 = "1kjwqycx120wlps1bg55dqzf0l2gvqimn67df7k0cpmf89698lbb";
  };
}); in


stdenv.mkDerivation {
name = "env";
JASMIN_REF = jasmin;
JASMIN_CT = jasmin-ct;
buildInputs = [
  hyperfine
];

}
