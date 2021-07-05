{ stdenv, lib, fetchFromGitHub, coqPackages }:

let inherit (coqPackages) coq; in

let mathcomp =
 (if coqPackages ? mathcomp_
  then coqPackages.mathcomp_ "1.10.0"
  else coqPackages.mathcomp.override { version = "1.10.0"; }
 ).algebra
; in

let rev = "4b83cbe911364a39b4f87ea2451b5a6119cbca06"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "0235qgjzdjjci1b8h85y16g8akrl0mgdm799lnhf4givx0d90hzv";
  };

  buildInputs = [ coq ];

  propagatedBuildInputs = [ mathcomp ];

  installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

  meta = {
    description = "Yet Another Coq Library on Machine Words";
    license = lib.licenses.cecill-b;
    inherit (src.meta) homepage;
    inherit (coq.meta) platforms;
  };
}
