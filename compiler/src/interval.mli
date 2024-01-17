type interval = { min : Z.t; max : Z.t }
type t = interval

val size : t -> Z.t
val pp_interval : ?closed:bool -> Format.formatter -> t -> unit
