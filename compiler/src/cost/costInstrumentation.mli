open Prog

val instrument : unit prog -> (Name.t * var) list * unit prog
