type simple_level = Public | Secret | Named of Prog.Name.t
type 'typ signature_gen = { arguments : 'typ list; results : 'typ list }

val get_nth_argument : int -> 'typ signature_gen -> 'typ option
val get_nth_result : int -> 'typ signature_gen -> 'typ option

module SCT : sig
  type level = { normal : simple_level; speculative : simple_level }

  type typ =
    | Msf
    | Direct of level
    | Indirect of { ptr : level; value : level }

  type signature = typ signature_gen

  val public : level
  val transient : level
  val secret : level
  val get_signature : Annotations.annotations -> signature option

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
end

module CT : sig
  (* The min of the level, the empty list means that it is unspecified ie "_" *)
  type typ = simple_level list
  type signature = typ signature_gen

  val public : simple_level
  val secret : simple_level
  val get_signature : Annotations.annotations -> signature option

  module PP : sig
    val simple_level : simple_level Utils.pp
    val typ : typ Utils.pp
    val signature : signature Utils.pp
  end

  module Parse : sig
    val simple_level : simple_level Angstrom.t
    val typ : typ Angstrom.t
    val signature : signature Angstrom.t
    val string : string -> signature option
  end
end

module SCT2CT : sig
  val typ : SCT.typ -> CT.typ
  val signature : SCT.signature -> CT.signature
end
