(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see CIL/LICENSE.coq file for the text of the license) *)
(************************************************************************)

type t = int

let _ = assert (Sys.word_size = 64)

let maxuint63 = Int64.of_string "0x7FFFFFFFFFFFFFFF"

let of_int i = i
[@@ocaml.inline always]

let equal (x : int) (y : int) = x = y
[@@ocaml.inline always]

let compares (x : int) (y : int) =
  Stdlib.Int.compare x y

let hash i = i
[@@ocaml.inline always]

let to_uint64 i = Int64.logand (Int64.of_int i) maxuint63

let to_string i = Int64.to_string (to_uint64 i)

let add x y = x + y
[@@ocaml.inline always]
