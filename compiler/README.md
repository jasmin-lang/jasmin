# Jasmin Compiler

More information about this compiler (build instructions in particular) can be
found on the online [wiki](https://github.com/jasmin-lang/jasmin/wiki).

The Jasmin compiler is free software. All files in this distribution are, by
default, licensed under the [MIT license](LICENSE). The exceptions are given
below.

The files `src/puf.ml` and `src/puf.mli` are distributed under the terms of the
GNU Library General Public License version 2.1, with the special exception on
linking described in file [`src/LICENSE.puf`](src/LICENSE.puf).

The files `src/UnionFindBasic.ml`, and `src/UnionFindBasic.mli` are distributed
under the terms of the GNU Library General Public License version 2, with the
special exception on linking described in file [`src/LICENSE.ufb`](src/LICENSE.ufb).

The contents of the `src/CIL` directory are extracted from Coq files from several sources:

 -  the Coq standard library (LGPL 2.1 only, see [`src/CIL/LICENSE.coq`](src/CIL/LICENSE.coq))
 -  the Mathematical Components library (CēCILL-B, see [`src/CIL/LICENSE.mathcomp`](src/CIL/LICENSE.mathcomp))
 -  the coqword library (MIT, see [`src/CIL/LICENSE.coqword`](src/CIL/LICENSE.coqword))
 -  the Jasmin coq source files (MIT, the [same license](LICENSE) as the rest of the compiler).

 The files `src/uint63.mli`, `src/uint63_31.ml`, and `src/uint63_63.ml` have
 been adapted from the source code of Coq and are distributed under the terms of
 the GNU Lesser General Public License Version 2.1 (see
 [`src/CIL/LICENSE.coq`](src/CIL/LICENSE.coq)).

## Tests

## Easycrypt extraction tests

Extraction is tested in two ways:

1. Easycrypt validation tests: the extraction is passed through easycrypt, with
   the results stored in `tests/results/extraction`. They can be run using

   ```sh
   make check CHECKCATS="x86-64-extraction arm-m4-extraction"
   ```

2. Check equality (up to whitespace) against reference extracted files in
   `tests/results.expected/extraction_ref`. The results are stored in
   `tests/results/extraction_ref`. These tests are run with

   ```sh
   make check CHECKCATS="x86-64-extraction-ref arm-m4-extraction-ref"
   ```

   For these tests, the reference extract files can be "promoted" using

   ```sh
   make promote-extraction
   ```

   This copies the results of the last test run
   (`tests/results/extraction_ref`) to be the new reference files
   (`tests/results.expected/extraction_ref`).
