module Vl : sig
  type t

  val public    : t
  val secret    : t

  val is_public    : t -> bool
  val is_secret    : t -> bool

  val constants   : t list
  val is_constant : t -> bool

  val to_string : t -> string
  val pp : Format.formatter -> t -> unit

end

module Svl : Set.S with type elt = Vl.t
module Mvl : Map.S with type key = Vl.t
module Hvl : Hashtbl.S with type key = Vl.t

module Lvl : sig

  type t
  val vlevel : t -> Vl.t
  val successors : t -> t list

  val equal : t -> t -> bool
  val le    : t -> t -> bool

  exception Unsat of (t list * t * t)
  val add_le : t -> t -> unit
  val iter : (t -> unit) -> t -> unit

  val is_public    : t -> bool
  val is_secret    : t -> bool

  val pp : Format.formatter -> t -> unit

end

module C : sig
  type constraints

  val init : unit -> constraints

  val public    : constraints -> Lvl.t
  val secret    : constraints -> Lvl.t

  val fresh : ?name:string -> constraints -> Lvl.t

  val pp_debug : Format.formatter -> constraints -> unit
  val pp       : Format.formatter -> constraints -> unit

  val simplify : constraints -> unit
  val prune    : constraints -> Lvl.t list -> unit
  val optimize : constraints -> tomax:Lvl.t list -> tomin:Lvl.t list -> unit
  val clone    : constraints -> constraints -> (Lvl.t -> Lvl.t)
  val is_instance : (Lvl.t -> Lvl.t) -> constraints -> constraints -> bool

end

module VlPairs : sig
  type t = Lvl.t * Lvl.t
  val add_le : t -> t -> unit
  val add_le_speculative : Lvl.t -> t -> unit
  val normalise : t -> t
end
