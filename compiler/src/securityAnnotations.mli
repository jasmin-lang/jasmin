type simple_level = Public | Secret | Named of Prog.Name.t
type level = { normal : simple_level; speculative : simple_level }
type typ = Msf | Direct of level | Indirect of { ptr : level; value : level }
type signature

val get_nth_argument : int -> signature -> typ option
val get_nth_result : int -> signature -> typ option

module PP : sig
  val signature : Format.formatter -> signature -> unit
end

module Parse : sig
  val string : string -> signature option
end
