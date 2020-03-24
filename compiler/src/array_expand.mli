open Prog

val vstack : var

val arrexp_func : 'info func -> 'info func

type ptr_kind =
  | Pstack of int
  | Pregptr of var 
  | Pstkptr of int

val stk_alloc_func : 
  'info func -> var array ->
   (var * ptr_kind) list * int * ptr_kind array

val init_glob : 'info prog ->
      Ssralg.GRing.ComRing.sort list * (Prog.var * int) list
