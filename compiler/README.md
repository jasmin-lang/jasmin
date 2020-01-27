Installing requirements using OPAM
--------------------------------------------------------------------

Starting with opam 2.0, you can install all the needed dependencies
via the opam OCaml packages manager.

  0. Optionally, switch to a dedicated compiler for Jasmin:

          $> opam switch create jasmin $OVERSION

     where $OVERSION is a valid OCaml version (e.g. ocaml-base-compiler.4.07.0)

  1. Add the Coq Word library opam package:

          $> opam pin add -ny git+https://github.com/jasmin-lang/coqword.git 

  2. Add the Jasmin OPAM package (from the compiler/ subdirectory)

          $> opam pin add -ny jasmin .

  3. Add the Coq remotes:

          $> opam repo add coq-released https://coq.inria.fr/opam/released
          $> opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev

  4. Optionally, use opam to install the system dependencies:

          $> opam install depext
          $> opam depext jasmin

  5. Install Jasmin dependencies:

          $> opam install --deps-only jasmin

Opam can be easily installed from source or via your packages manager:

  * On Ubuntu and derivatives:

        $> add-apt-repository ppa:avsm/ppa
        $> apt-get update
        $> apt-get install ocaml ocaml-native-compilers camlp4-extra opam

  * On MacOSX using brew:

        $> brew install ocaml opam

See [https://opam.ocaml.org/doc/Install.html] for how to install opam.

See [https://opam.ocaml.org/doc/Usage.html] for how to initialize opam

Installing requirements using NIX
--------------------------------------------------------------------

Run `nix-shell` in the top-level directory. This will drop you in a
shell with all required dependencies available.

See [https://nixos.org/nix/] for how to install the NIX package manager.

Compiling
--------------------------------------------------------------------

Simply run:

        $> make CIL build
