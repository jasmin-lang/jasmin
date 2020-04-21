open Prog

type graph = (int * int) Mv.t
type color = int
type coloring = color Mv.t

val solve : graph -> coloring
