#!/bin/sh

set -e

opam init --no-setup --compiler=4.12.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin --yes --no-action add coq-mathcomp-word https://github.com/jasmin-lang/coqword.git
opam pin --yes --no-depexts --no-action add .
opam install --yes --no-depexts --deps-only jasmin

