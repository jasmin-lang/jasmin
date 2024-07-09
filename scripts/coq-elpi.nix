{ lib, mkCoqDerivation, coq, version }:

let elpi =
  coq.ocamlPackages.elpi.override {
    version = "v1.18.2";
  }
; in

mkCoqDerivation {
  pname = "elpi";
  repo  = "coq-elpi";
  owner = "LPCIC";
  inherit version;

  mlPlugin = true;
  useDune = true;
  propagatedBuildInputs = [ elpi ]
  ++ (with coq.ocamlPackages; [ findlib ppx_optcomp ]);

}
