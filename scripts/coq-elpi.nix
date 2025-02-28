{ lib, mkCoqDerivation, coq, version }:

mkCoqDerivation {
  pname = "elpi";
  repo  = "coq-elpi";
  owner = "LPCIC";
  inherit version;

  configurePhase = ''
    patchShebangs etc/with-rocq-wrap.sh
    make dune-files || true
  '';

  buildPhase = ''
    etc/with-rocq-wrap.sh dune build -p rocq-elpi @install ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
  '';

  installPhase = ''
    etc/with-rocq-wrap.sh dune install --root . rocq-elpi --prefix=$out --libdir $OCAMLFIND_DESTDIR
    mkdir $out/lib/coq/
    mv $OCAMLFIND_DESTDIR/coq $out/lib/coq/${coq.coq-version}
  '';

  mlPlugin = true;
  useDune = true;
  propagatedBuildInputs = [ ]
  ++ (with coq.ocamlPackages; [
    (elpi.override { version = "master"; })
    findlib
    ppx_optcomp
  ]);

}
