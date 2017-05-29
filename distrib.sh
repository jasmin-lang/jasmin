#!/bin/sh
rm -Rf jasmin jasmin.tar.gz
mkdir jasmin
cp -R compiler proofs LICENSE README.md jasmin
rm -r jasmin/proofs/logic
sed -e "s/Inria$/<Anonymized>/" -i jasmin/proofs/*/*.v jasmin/compiler/src/*.ml
sed -e "s/IMDEA Software Institute/<Anonymized>/" -i jasmin/proofs/*/*.v jasmin/compiler/src/*.ml
sed -e "s,http://jasmin-lang.github.io/,http://example.com," -i jasmin/compiler/opam
sed -e "s,https://github.com/jasmin-lang/jasmin/issues,http://example.com," -i jasmin/compiler/opam
sed -e "/logic/d" -i jasmin/proofs/_CoqProject
rm -f jasmin/proofs/Makefile.coq
tar czf jasmin.tar.gz jasmin
