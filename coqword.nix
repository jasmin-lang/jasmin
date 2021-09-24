{ stdenv, lib, fetchFromGitHub, coqPackages }:

let inherit (coqPackages) coq; in

let mathcomp =
 (if coqPackages ? mathcomp_
  then coqPackages.mathcomp_ "1.11.0"
  else coqPackages.mathcomp.override { version = "1.11.0"; }
 ).algebra
; in

let rev = "ca7dcd122cb3d5845977a18d584816fdf0a71859"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "1l22cpfifcbzlvcpn29k1dajrnfpzbh3dvnqgv1ggl26g6rq2swp";
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
