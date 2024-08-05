type simple_level = Public | Secret | Named of Prog.Name.t
type level = { normal : simple_level; speculative : simple_level }
type typ = Msf | Direct of level | Indirect of { ptr : level; value : level }
type signature = { arguments : typ list; results : typ list }

val public : level
val transient : level
val secret : level
val get_nth_argument : int -> signature -> typ option
val get_nth_result : int -> signature -> typ option
val get_sct_signature : Annotations.annotations -> signature option

module PP : sig
  val simple_level : simple_level Utils.pp
  val level : level Utils.pp
  val typ : typ Utils.pp
  val signature : signature Utils.pp
end

module Parse : sig
  val simple_level : simple_level Angstrom.t
  val level : level Angstrom.t
  val typ : typ Angstrom.t
  val signature : signature Angstrom.t
  val string : string -> signature option
end
