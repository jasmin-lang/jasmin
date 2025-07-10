This is a copy of the Jasmin project extend with the work corresponding
to the paper "ITree-Based Relational Hoare Logic for Verified Compilation"


# Download, installation, and sanity-testing instructions

Detail instruction are available at
[link](https://github.com/jasmin-lang/jasmin/wiki/Installation-instructions)

## Dependencies

This formalization has been developed with the tools listed in the opam
file (located at the root of the project).

A convenient way to get the correct dependencies is to use the nix package
manager and to run in this directory:
```
nix-shell
```
This will enter in a shell environment in which all these dependencies are
available.

Alternatively, `opam` can be used. To set up `opam` detail instruction are
available at [link](https://opam.ocaml.org/doc/Install.html). We require that a
valid `opam` switch is configured with a compiler version >= 4.12.0 and is set
as current switch.

First add the Coq repository to the current opam switch
```
opam repo add coq-released https://coq.inria.fr/opam/released
```
then do
```
opam update
```
and install the dependencies listed in the opam file.


## Build

To run Coq and check the validity of the proofs, run in the `proof` directory:
```
make
```
This verifies all Coq files.

Alternatively, to compile the full compiler, run in the root of the
project:
```
make
```


# List of claims in the paper supported by this artifact

## About distribution

## About the ITree implementation

## About RHL and HL

## About Compiler pass proofs

- `proofs/compiler/wint_word.v`: compiler pass proof are in the IT sections
- ......







<!-- ------------------------------------------------------------------------------- -->
<!-- Old Readme -->
<!-- ------------------------------------------------------------------------------- -->

# Jasmin

[![pipeline status](https://gitlab.com/jasmin-lang/jasmin/badges/main/pipeline.svg)](https://gitlab.com/jasmin-lang/jasmin/-/commits/main)
[![project chat](https://readthedocs.org/projects/jasmin-lang/badge/)](https://jasmin-lang.readthedocs.org)
[![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://formosa-crypto.zulipchat.com)

## About

Jasmin denotes both a language and a compiler designed for
writing high-assurance and high-speed cryptography.
Jasmin implementations aim at being efficient, safe, correct, and secure.

Reference documentation of the language and compiler are on [readthedocs](https://jasmin-lang.readthedocs.io).

## Installation

For a complete installation guide covering several use cases, please read our
[documentation](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html).

If you just want to install the Jasmin tools, here is a TL;DR:

- with APT (debian, ubuntu), a package is available in a dedicated repository,
  see the [documentation](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html#on-debian-and-related-linux-distributions)

- from AUR (arch linux), a package is available in the Arch User Repository,
  see the [documentation](https://jasmin-lang.readthedocs.io/en/stable/misc/installation_guide.html#on-arch-linux)

- with nix
  ```
  nix-env -iA nixpkgs.jasmin-compiler
  ```

- with opam
  ```
  opam install jasmin
  ```

## Getting support

The [Formosa-Crypto Zulip Chat](https://formosa-crypto.zulipchat.com/) is meant for anybody interested in high-assurance cryptography using EasyCrypt, Jasmin, and related tools.

## License

Jasmin is free software. All files in this distribution are, unless specified
otherwise, licensed under the [MIT license](LICENSE).
The documentation (under `docs/`) is licensed separately from the
compiler, under the [CC-BY 4.0](docs/LICENSE).
