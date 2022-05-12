#!/bin/sh

set -e

opam init --no-setup --compiler=4.12.1
# If $OPAMROOT is not in a standard location, it may happen that the sandbox
# hides it during the building of packages, which for some packages results in
# a build failure. There is a variable OPAM_USER_PATH_RO that is provided to
# make more directories available inside the sandbox, but the opam nix package
# overrides its value using "makeWrapper --set". This temporary and hacky fix
# consists in patching the sandbox script used by opam to add $OPAMROOT to
# OPAM_USER_PATH_RO after it was overwritten by makeWrapper. In the
# (hopefully near) future, opam 2.2 will make (nearly) the whole filesystem
# available in read-only mode, thus eliminating the need for OPAM_USER_PATH_RO
# and this hack.
if patch -N -r - "$OPAMROOT/opam-init/hooks/sandbox.sh" scripts/fix_path_ro.patch >/dev/null 2>&1 ; then
  echo "$OPAMROOT/opam-init/hooks/sandbox.sh patched successfully"
else
  echo "no need to patch $OPAMROOT/opam-init/hooks/sandbox.sh"
fi
if [ $1 ]
then
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam pin --yes --no-action add coq-mathcomp-word https://github.com/jasmin-lang/coqword.git
  opam pin --yes --no-depexts --no-action add .
else
  opam pin --yes --no-depexts --no-action add compiler
fi
opam install --yes --no-depexts --deps-only jasmin

