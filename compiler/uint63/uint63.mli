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

val hash : t -> int
val to_string : t -> string

val l_sl    : t -> t -> t
val l_sr    : t -> t -> t
val l_and   : t -> t -> t
val l_or    : t -> t -> t

val add     : t -> t -> t
val sub     : t -> t -> t

val equal      : t -> t -> bool
val le      : t -> t -> bool

val compares : t -> t -> int
