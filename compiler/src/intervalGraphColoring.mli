open Prog

type graph = (int * int) Mv.t
type color = var
type coloring = color Mv.t

val solve : int -> graph -> coloring
