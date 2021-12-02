{ stdenv, lib, fetchFromGitHub, coqPackages }:

let inherit (coqPackages) coq; in

let mathcomp =
 (if coqPackages ? mathcomp_
  then coqPackages.mathcomp_ "1.12.0"
  else coqPackages.mathcomp.override { version = "1.12.0"; }
 ).algebra
; in

let rev = "bf1ff6c1695d42d1ccbf9d7f1cc62297a1f472bb"; in

stdenv.mkDerivation rec {
  version = "0.0-git-${builtins.substring 0 8 rev}";
  name = "coq${coq.coq-version}-coqword-${version}";

  src = fetchFromGitHub {
    owner = "jasmin-lang";
    repo = "coqword";
    inherit rev;
    sha256 = "sha256:105ybr7fzaf9p6ll6xm86k6741q2y94kyqj4jh3rli4lyiw4cn87";
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
