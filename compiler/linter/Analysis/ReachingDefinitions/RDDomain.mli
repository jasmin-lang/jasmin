(**
Reaching definition domain. For more informations see :
- https://en.wikipedia.org/wiki/Reaching_definition
- Principles of Program Analysis - Nielson, Nielson & Hankin (2006) (chapter 2.1.2)

This module implements a reaching definition domain for Jasmin programs.
Domain are represented as a map that associate a set of instructions to each variable.
We also define a default value for each variable (notated as (v,?) in Nielson, Nielson & Hankin) representing a variable that is not initialized in the body of the function (see [Types.Iloc]).
*)

open Jasmin.Prog
open Types

(**
domain type
*)
type t = Iloc.SIloc.t Mv.t

(**
empty domain
*)
val empty : t

val add : Sv.t -> Iloc.t -> t -> t

val join :t -> t -> t

val included : t -> t -> bool

val forget : var -> t -> t

val pp : Format.formatter -> Jasmin.Location.i_loc * t -> unit
