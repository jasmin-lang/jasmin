# Installation Guide

There are many ways to install the Jasmin tool box, depending on the intended
use-case. This page is meant as a guide through the maze of installation
options, organized by use-cases.

What is your intended use-case?

1. Using **high-assurance cryptographic implementations**

    You are at the wrong place: Jasmin cannot help directly. Sorry.

    <!-- TODO: link? -->

2. Writing or verifying Jasmin programs

    [Install the command-line tools](#install-the-jasmin-tools)

3. Writing or extending trusted Jasmin tools, or hacking the compiler

    [Install the OCaml libraries](#install-the-jasmin-ocaml-libraries)

4. Writing Coq program & proofs about the Jasmin language

    This is an unusual use case. [Use the Coq sources](#install-the-coq-libraries)

## Install the Jasmin tools

Install the compiler (`jasminc`) and associated tools (`jasmin-ct` to check for
constant-time security, `jasmin2tex` to pretty-print Jasmin programs into LaTeX,
`jasmin2ec` to translate Jasmin programs into EasyCrypt models for correctness
and security proofs).

### Using a package manager

Up-to-date packages are available for a few platforms.

#### On Debian and related linux distributions

The packages are distributed through a custom repository. The `apt` package
manager must be configured to trust and use this repository. To this end run the
following commands as root (for Debian Trixie; if you are using Bookworm,
replace “trixie” with “bookworm” in the second command):

~~~
wget -qO- https://formosa-crypto.org/formosa-archive-keyring.pgp | gpg --dearmor > /etc/apt/trusted.gpg.d/formosa-crypto.gpg
echo 'deb [signed-by=/etc/apt/trusted.gpg.d/formosa-crypto.gpg] https://repo.formosa-crypto.org/debian trixie main' > /etc/apt/sources.list.d/formosa-crypto.list
~~~

Then update the list of available packages (`sudo apt update`) and install the package that you need:

- **jasmin-compiler** has the command-line tools
- **easycrypt** (Trixie only) has the proof assistant
- **libjasmin-easycrypt** has the EasyCrypt libraries used for verifying Jasmin implementations

#### On Arch Linux

The packages are distributed through Arch User Repository (AUR), the relevant packages are:
- [**jasmin-compiler-bin**](https://aur.archlinux.org/packages/jasmin-compiler-bin): the command-line tools
- [**easycrypt-bin**](https://aur.archlinux.org/packages/easycrypt-bin): the proof assistant
- [**libjasmin-easycrypt-bin**](https://aur.archlinux.org/packages/libjasmin-easycrypt-bin): the EasyCrypt libraries

Install any of them with your AUR Helper with a command like the following:
~~~
# with yay
yay -S jasmin-compiler-bin

# with paru
paru -S jasmin-compiler-bin
~~~

#### Using the nix (or lix) package manager, on linux, macos, wsl, etc.

Assuming the package-manager is set up and working (see
<https://nixos.org/download/#download-nix> or <https://lix.systems/install/> to
get started), the relevant packages are:

- **jasmin-compiler.bin**: the command-line tools
- **jasmin-compiler.lib**: the EasyCrypt libraries
- **easycrypt**: the proof assistant

Install any of them with a command like the following:

    nix-env -iA nixpkgs.jasmin-compiler.bin

#### Using the opam package manager

Assuming the package manager is set up and working, the relevant package is **jasmin**.

Install it using

    opam install jasmin

### From source

In order to build and install Jasmin from its source code you must:

1. obtain the source code
2. install the build dependencies
3. build the Jasmin toolbox

#### Get the source code

##### Released versions

Available on [github.com](https://github.com/jasmin-lang/jasmin/releases). Download the file `jasmin-compiler-v[version].tar.bz2`, corresponding to the version of your liking.

##### Major development branches

As a product of the continuous integration (CI), a git repository with the
source code of the major development versions is available on
[gitlab.com](https://gitlab.com/jasmin-lang/jasmin-compiler). This repository
contains in particular the source code corresponding to the main branch and the
“release” branches, in which the next minor version is prepared.

##### Specific development versions

Each [CI run](https://gitlab.com/jasmin-lang/jasmin/-/pipelines) has a
**tarball** job which produces as an *artifact* a tarball with the source code
corresponding to the tested version. It can be downloaded following the links on
the website or directly from a URL of the form
`https://gitlab.com/jasmin-lang/jasmin/-/jobs/JOB_NUMBER/artifacts/raw/compiler/jasmin-compiler-COMMIT.tgz`
(but you have to know the job number and the 8-digit prefix of the commit hash).

<!-- This paragraph is confusing and probably of little use
##### From Coq sources

See below to get the Coq source and set up an environment with the proper
dependencies. Then, in the `compiler` directory, run `make CIL` and fix the
version string by changing `@VERSION@` (in the file `src/glob_options.ml`) to
something relevant to your local build. Finally run `make dist`: this produces a
`jasmin-compiler.tgz` file.

-->

#### Get the dependencies

A direct way to properly set up a working environment is to use a package
manager.

As part of the source code, there is a `jasmin.opam` file that you can
use with the `opam` package manager as follows:

    opam install ./jasmin.opam --deps-only

In the `compiler/` directory, there is a `default.nix` file that you can use
with the `nix` package manager, e.g., running `nix-shell compiler/`.

The required dependencies include the following:

 - [OCaml](https://ocaml.org) at version 4.14, with the following tools and libraries: menhir, menhirLib, dune, findlib (aka ocamlfind), apron, camlidl, angstrom, batteries, cmdliner, zarith, yojson.
 - [MPFR](https://www.mpfr.org/)
 - [PPL](https://www.bugseng.com/ppl)

#### Build the Jasmin toolbox

When in a proper environment, simply run `make` in the `compiler/` directory.

### Proofs with EasyCrypt

In order to verify EasyCrypt programs obtained by extraction from Jasmin
programs, the `Jasmin` EasyCrypt library is required. It is can be obtained by
installing one of the **libjasmin-easycrypt** Debian package or the
**jasmin-compiler.lib** nixpkgs package.

You also need to install EasyCrypt, and probably proofgeneral.

Moreover, some configuration can be required; see
[](../tools/jasmin2ec.md#configure-easycrypt-to-verify-jasmin-programs).

## Install the Jasmin OCaml libraries

In order to write OCaml programs working with Jasmin programs, you need the
Jasmin OCaml libraries. They are distributed in the **libjasmin-ocaml-dev**
Debian package, the **jasmin-compiler** nix package, and in the **jasmin** opam
package.

## Install the Coq libraries

There is a `coqPackage.jasmin` package in `nixpkgs`
(i.e., to be used with the `nix` package manager). If that does not cover your needs,
get the Coq source code and install the required dependencies.

### Getting the source code

The Coq source code is available in the main Jasmin git repository:
<https://github.com/jasmin-lang/jasmin>.

Pick a branch or tag that corresponds to your needs:

  - main development occurs in branch `main` (theorems are expected to be proved there).
  - tags correspond to released version
  - other branches are not documented.

### Dependencies

The dependencies of the Coq development are as follows:

  - [Coq](https://coq.inria.fr/) at version 8.20
  - The [Mathematical Components](https://math-comp.github.io/) library, at version 2.2 (only the following sub-libraries are required: ssreflect, fingroup, algebra, algebra-tactics)
  - The [mathcomp-word](https://github.com/jasmin-lang/coqword) library, at version 3.2
  - The [Interaction Trees](https://github.com/DeepSpec/InteractionTrees) library, at version 5.2.1

The file `default.nix` at the root of the repository contains a precise description of these dependencies.
In order to set-up a working environment with those dependencies available and properly configured,
run

    nix-shell --arg pinned-nixpkgs true

There is also an `opam` file to be used with the `opam` package manager.
