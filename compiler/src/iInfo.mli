type t
val dummy : t

val mk : Location.i_loc -> unit -> Syntax.annotations -> t
val split : t -> Location.i_loc * unit * Syntax.annotations
