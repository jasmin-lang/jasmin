{ stdenv, lib, fetchFromGitHub, coqPackages }:

let inherit (coqPackages) coq; in

let mathcomp =
 (if coqPackages ? mathcomp_
  then coqPackages.mathcomp_ "1.11.0"
  else coqPackages.mathcomp.override { version = "1.11.0"; }
 ).algebra
; in

let rev = "131bee8a1c14a67a4925534e455ea0b870ee0615"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "196w51biq9wagbr0dkjd2v2z16nf6sz0yy5r4q1mgnpdld0rs9m1";
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
