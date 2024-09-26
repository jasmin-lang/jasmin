{ pkgs ? import (if pinned-nixpkgs then scripts/nixpkgs.nix else <nixpkgs>) {}
, inCI ? false
, pinned-nixpkgs ? inCI
, coqDeps ? !inCI
, coqMaster ? false
, ocamlDeps ? !inCI
, testDeps ? !inCI
, devTools ? !inCI
, ecRef ? ""
, opamDeps ? false
, enableFramePointers ? false
}:

with pkgs;

let inherit (lib) optionals; in

let coqPackages =
  if coqMaster then
    pkgs.coqPackages.overrideScope (self: super: {
      coq = super.coq.override { version = "master"; };
      coq-elpi = callPackage scripts/coq-elpi.nix {
        version = "master";
        inherit (self) lib mkCoqDerivation coq;
      };
      hierarchy-builder = super.hierarchy-builder.override { version = "master"; };
    })
  else coqPackages_8_19
; in

let mathcomp-word = callPackage scripts/mathcomp-word.nix { inherit coqPackages; }; in

let easycrypt = callPackage scripts/easycrypt.nix {
  inherit ecRef;
  why3 = pkgs.why3.override { ideSupport = false; };
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

if !lib.versionAtLeast oP.ocaml.version "4.11"
then throw "Jasmin requires OCaml ≥ 4.11"
else

let ecDeps = ecRef != ""; in

stdenv.mkDerivation {
  name = "jasmin-0";
  src = nix-gitignore.gitignoreSource [] ./.;
  buildInputs = []
    ++ optionals coqDeps [ coqPackages.coq mathcomp-word ]
    ++ optionals testDeps ([ curl.bin oP.apron.out libllvm ] ++ (with python3Packages; [ python pyyaml ]))
    ++ optionals ocamlDeps ([ mpfr ppl ] ++ (with oP; [
         ocaml findlib dune_3
         cmdliner
         angstrom
         batteries
         menhir (oP.menhirLib or null) zarith camlidl apron yojson ]))
    ++ optionals devTools (with oP; [ merlin ocaml-lsp ])
    ++ optionals ecDeps [ easycrypt alt-ergo z3.out ]
    ++ optionals opamDeps [ rsync git pkg-config perl ppl mpfr opam ]
    ;

  enableParallelBuilding = true;

  installPhase = ''
    make -C compiler install PREFIX=$out
  '';
}
