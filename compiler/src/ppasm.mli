open Wsize
(* -------------------------------------------------------------------- *)
exception InvalidRegSize of wsize

(* -------------------------------------------------------------------- *)
val mangle : string -> string

(* -------------------------------------------------------------------- *)
val pp_instr : string -> Format.formatter -> X86_sem.asm -> unit

val pp_prog  : 
  'info Conv.coq_tbl -> 
  Format.formatter -> X86_sem.xprog -> unit
