#!/bin/sh

set -e

opam init --disable-sandboxing --no-setup --compiler=4.14.2
if [ 1 -le $# ]
then
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam install --yes --no-depexts --deps-only ./jasmin.opam
else
  opam install --yes --no-depexts --deps-only ./jasmin-compiler.opam
fi
