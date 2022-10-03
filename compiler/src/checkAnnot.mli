val check_stack_size : (Expr.stk_fun_extra * _ Prog.func) list -> unit
(** Check the stacksize, stackallocsize & stackalign annotations, if any *)

val check_no_for_loop : _ Prog.prog -> unit
(** Check that no for loop remain. *)

val check_no_inline_instr : _ Prog.prog -> unit
(** Check that no “inline”-annotated instruction remain. *)
