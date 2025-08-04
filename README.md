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

- with nix
  ```
  nix-env -iA nixpkgs.jasmin-compiler
  ```

- with opam
  ```
  opam install jasmin
  ```

- with APT (debian, ubuntu), a package is available in a dedicated repository, see the [documentation](https://jasmin-lang.readthedocs.io/en/latest/misc/installation_instructions.html#debian-packages)

- from source, see the [documentation](https://jasmin-lang.readthedocs.io/en/latest/misc/installation_instructions.html)

## Getting support

The [Formosa-Crypto Zulip Chat](https://formosa-crypto.zulipchat.com/) is meant for anybody interested in high-assurance cryptography using EasyCrypt, Jasmin, and related tools.

## License

Jasmin is free software. All files in this distribution are, unless specified
otherwise, licensed under the [MIT license](LICENSE).
The documentation (under `docs/`) is licensed separately from the
compiler, under the [CC-BY 4.0](docs/LICENSE).
