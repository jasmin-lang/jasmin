open Prog

val arrexp_func : 'info func -> 'info func
val arrexp_prog : 'info prog -> 'info prog

val stk_alloc_func : 'info func -> (var * int) list * int * 'info func

val stk_alloc_prog : 'info prog -> ((var * int) list * int * 'info func) list
