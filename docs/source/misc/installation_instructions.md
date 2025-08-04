# Installation instructions

TL;DR: Run `nix-env -iA nixpkgs.jasmin-compiler` ([more info about the nix package manager](https://nixos.org/)), or run `opam install jasmin` ([more info about the opam package manager](https://opam.ocaml.org/)).

***

## Debian packages

Debian packages for the Jasmin toolbox and its dependencies are made available on the Formosa Crypto repository. In order to install these packages, you first need to configure `apt` to use this repository.

 1. Download and add the signing key

    Run as **root** the following command:

        wget -qO- https://formosa-crypto.org/formosa-archive-keyring.pgp | gpg --dearmor > /etc/apt/trusted.gpg.d/formosa-crypto.gpg

 2. Add the package repository to your APT sources.list

    Run as **root** the following command:

        echo 'deb [signed-by=/etc/apt/trusted.gpg.d/formosa-crypto.gpg] https://repo.formosa-crypto.org/debian bookworm main' > /etc/apt/sources.list.d/formosa-crypto.list

 3. Get the latest information about the repository contents

    Run as **root** the following command:

        apt update

 4. Install the Jasmin package

    Run as **root** the following command:

        apt install jasmin-compiler

***

The Jasmin compiler is written in [Coq](https://coq.inria.fr) and [OCaml](https://ocaml.org/).
It is built in two steps: OCaml code is first extracted from the Coq code
then compiled together with the hand-written OCaml code.

If you are not interested in using the Coq formalization, you may skip the first step below.

## From the Coq development

Get the source code from the git repository hosted on <https://github.com/jasmin-lang/jasmin/>,
for instance the current version of the `main` branch:
[jasmin-main.tar.gz](https://github.com/jasmin-lang/jasmin/archive/main.tar.gz).

### Dependencies of the Coq development

The exact set of dependencies can be found in the `default.nix` file at the root of the git repository.

  - [Coq](https://coq.inria.fr/) at version 8.20
  - The [Mathematical Components](https://math-comp.github.io/) library, at version 2.2 (only the following sub-libraries are required: ssreflect, fingroup, algebra)
  - The [mathcomp-word](https://github.com/jasmin-lang/coqword) library, at version 3.2

### Coq compilation

Once all dependencies are available (which can be achieved by running `nix-shell` at the root directory),
change to the `proof` directory and run `make`

### Extract the OCaml code from the Coq development

Change to the `compiler` directory and run `make CIL`

## From OCaml sources

Get the full OCaml source code, either as a result of the extraction process described above, or from the [jasmin-compiler](https://gitlab.com/jasmin-lang/jasmin-compiler/) repository,
for instance the current version of the `main` branch:
[jasmin-compiler.tar.gz](https://gitlab.com/jasmin-lang/jasmin-compiler/-/archive/main/jasmin-compiler-main.tar.gz)

### Dependencies of the OCaml program

The precise set of dependencies can be found in the `default.nix` file.

 - [OCaml](https://ocaml.org) at version 4.14, with the following tools and libraries: menhir, menhirLib, dune, findlib (aka ocamlfind), apron, camlidl, batteries, cmdliner, zarith, yojson.
 - [MPFR](https://www.mpfr.org/)
 - [PPL](https://www.bugseng.com/ppl)

### OCaml compilation

Once all dependencies are available (which can be achieved by running `nix-shell`, either at the root of the source tree — if there is a `default.nix` file there — or within the `compiler` directory),
change to the `compiler` directory (at the root of the source tree, not inside the `proof` directory), and run `make`.
This produces a `jasminc` program (a symbolic link to the actual binary file, that might be moved to a different path; that program is dynamically linked to a few libraries: apron, mpfr, ppl, etc.).
