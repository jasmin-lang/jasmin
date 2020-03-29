open Prog

val vstack : var

val arrexp_func : 'info func -> 'info func

type param_info = { 
  pp_ptr      : var;
  pp_writable : bool;
  pp_align    : Wsize.wsize;
}

type ptr_kind =
  | Pstack of int * Wsize.wsize
  | Pregptr of var 
  | Pstkptr of int

val stk_alloc_func : 
  'info func -> var array ->
   param_info option list * int option list * 
   (var * ptr_kind) list * int * ptr_kind array

val init_glob : 'info prog ->
      Ssralg.GRing.ComRing.sort list * (Prog.var * (int * Wsize.wsize)) list
