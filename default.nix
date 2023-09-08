{ pkgs ? import (if pinned-nixpkgs then scripts/nixpkgs.nix else <nixpkgs>) {}
, inCI ? false
, pinned-nixpkgs ? inCI
, coqDeps ? !inCI
, ocamlDeps ? !inCI
, testDeps ? !inCI
, devTools ? !inCI
, ecRef ? ""
, opamDeps ? false
, enableFramePointers ? false
}:

with pkgs;

let inherit (lib) optionals; in

let coqPackages = coqPackages_8_17; in

let mathcomp-word = callPackage scripts/mathcomp-word.nix { inherit coqPackages; }; in

let easycrypt = callPackage scripts/easycrypt.nix {
  inherit ecRef;
  why3 = pkgs.why3.overrideAttrs (o: rec {
      version = "1.6.0";
      src = pkgs.fetchurl {
        url = "https://why3.gitlabpages.inria.fr/releases/${o.pname}-${version}.tar.gz";
        hash = "sha256-hFvM6kHScaCtcHCc6Vezl9CR7BFbiKPoTEh7kj0ZJxw=";
      };
    });
}; in

let inherit (coqPackages.coq) ocamlPackages; in

let oP =
  if enableFramePointers
  then ocamlPackages.overrideScope' (self: super: {
    ocaml = super.ocaml.overrideAttrs (o: {
      configureFlags = o.configureFlags ++ [ "--enable-frame-pointers" ];
    });
  })
  else ocamlPackages
; in

if !lib.versionAtLeast oP.ocaml.version "4.08"
then throw "Jasmin requires OCaml ≥ 4.08"
else

let ecDeps = ecRef != ""; in

stdenv.mkDerivation {
  name = "jasmin-0";
  src = null;
  buildInputs = []
    ++ optionals coqDeps [ coqPackages.coq mathcomp-word ]
    ++ optionals testDeps ([ oP.apron.out ] ++ (with python3Packages; [ python pyyaml ]))
    ++ optionals ocamlDeps ([ mpfr ppl ] ++ (with oP; [
         ocaml findlib ocamlbuild
         (batteries.overrideAttrs (o: { doCheck = false; }))
         menhir (oP.menhirLib or null) zarith camlidl apron yojson ]))
    ++ optionals devTools (with oP; [ merlin ])
    ++ optionals ecDeps [ easycrypt easycrypt.runtest alt-ergo z3.out ]
    # Apron as packaged in opam is broken with gnumake ≥ 4.4
    # Bringing gnumake 4.2 in scope works around this issue
    ++ optionals opamDeps [ gnumake42 rsync git pkg-config perl ppl mpfr opam ]
    ;
}
