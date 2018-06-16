(* -------------------------------------------------------------------- *)
exception InvalidRegSize of Type.wsize

(* -------------------------------------------------------------------- *)
val mangle : string -> string

(* -------------------------------------------------------------------- *)
val pp_instr : string -> Format.formatter -> X86_sem.asm -> unit

val pp_prog  : 
  'info Conv.coq_tbl -> 
  Format.formatter -> Expr.glob_decl list * X86_sem.xprog -> unit
