#!/bin/sh

set -e

opam init --disable-sandboxing --no-setup --compiler=4.14.1
if [ $1 ]
then
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam pin --yes --no-action add coq-mathcomp-word https://github.com/jasmin-lang/coqword.git
  opam pin --yes --no-depexts --no-action add .
else
  opam pin --yes --no-depexts --no-action add compiler
fi
opam install --yes --no-depexts --deps-only jasmin

