(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see CIL/LICENSE.coq file for the text of the license) *)
(************************************************************************)

type t

val of_int : int -> t
val equal      : t -> t -> bool
val compares : t -> t -> int

val hash : t -> int
val to_string : t -> string

val add     : t -> t -> t
