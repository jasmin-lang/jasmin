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

let to_uint64 i = Int64.logand (Int64.of_int i) maxuint63

let of_int i = i
[@@ocaml.inline always]

let hash i = i
[@@ocaml.inline always]

let to_string i = Int64.to_string (to_uint64 i)

    (* logical shift *)
let l_sl x y =
  if 0 <= y && y < 63 then x lsl y else 0

let l_sr x y =
  if 0 <= y && y < 63 then x lsr y else 0

let l_and x y = x land y
[@@ocaml.inline always]

let l_or x y = x lor y
[@@ocaml.inline always]

let add x y = x + y
[@@ocaml.inline always]

let sub x y = x - y
[@@ocaml.inline always]

let le (x : int) (y : int) =
  (x lxor 0x4000000000000000) <= (y lxor 0x4000000000000000)
[@@ocaml.inline always]

let equal (x : int) (y : int) = x = y
[@@ocaml.inline always]

let compares (x : int) (y : int) =
  Stdlib.Int.compare x y
