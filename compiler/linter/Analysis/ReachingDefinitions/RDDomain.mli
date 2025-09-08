(**
Reaching definition domain. For more informations see :
- https://en.wikipedia.org/wiki/Reaching_definition
- Principles of Program Analysis - Nielson, Nielson & Hankin (2006) (chapter 2.1.2)

This module implements a reaching definition domain for Jasmin programs.
Domain are represented as a map that associate a set of instructions to each variable.
*)

open Jasmin
open Utils
open Prog

(**
domain type
*)
type t = Siloc.t Mv.t

(**
empty domain
*)
val empty : t

val add : Sv.t -> Location.i_loc -> t -> t

val join :t -> t -> t

val included : t -> t -> bool

val forget : var -> t -> t

val pp : Format.formatter -> Location.i_loc * t -> unit
