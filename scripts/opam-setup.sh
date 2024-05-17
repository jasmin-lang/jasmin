#!/bin/sh

set -e

opam init --disable-sandboxing --no-setup --compiler=4.14.2
if [ 1 -le $# ]
then
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam pin --yes --no-depexts --no-action add .
else
  opam pin --yes --no-depexts --no-action add compiler
fi
opam install --yes --no-depexts --deps-only jasmin

