type interval = { min : int; max : int }
type t = interval

val pp_interval : ?closed:bool -> Format.formatter -> interval -> unit
