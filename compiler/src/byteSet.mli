open Interval

type t
val empty  : t
val is_empty : t -> bool

val memi   : int -> t -> bool
val mem    : interval -> t -> bool
val subset : t -> t -> bool

val full   : interval -> t
val add    : interval -> t -> t
val remove : interval -> t -> t
val inter  : t -> t -> t
val union  : t -> t -> t

val pp : Format.formatter -> t -> unit
