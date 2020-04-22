type interval = { min : int; max : int }
type t = interval

val size : t -> int 
val pp_interval : ?closed:bool -> Format.formatter -> t -> unit
