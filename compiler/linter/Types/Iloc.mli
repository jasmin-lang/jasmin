(**
Extended Location.i_loc type using a default value to describe an instruction that is not part of the function.

If follows description of instruction introduced in "Principle of Program Analysis" by Nielson, Nielson and Hankin.

*)

type t =
| Default
| Instruction of Jasmin.Location.i_loc

val compare : t -> t -> int

val pp : Format.formatter -> t -> unit

module SIloc : Set.S with type elt = t