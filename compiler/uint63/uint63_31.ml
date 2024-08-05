(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see CIL/LICENSE.coq file for the text of the license) *)
(************************************************************************)

(* Invariant: the msb should be 0 *)
type t = Int64.t

let _ = assert (Sys.word_size = 32)

let maxuint63 = 0x7FFF_FFFF_FFFF_FFFFL

let mask63 i = Int64.logand i maxuint63

let of_int i = mask63 (Int64.of_int i)

let to_int2 i = (Int64.to_int (Int64.shift_right_logical i 31), Int64.to_int i)

let hash i =
  let (h,l) = to_int2 i in
  h * 65599 + l

let equal (x : t) y = x = y

let compares x y = Int64.(compare (shift_left x 1) (shift_left y 1))

let to_string = Int64.to_string

let add x y = mask63 (Int64.add x y)
