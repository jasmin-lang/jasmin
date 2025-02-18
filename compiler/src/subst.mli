open Prog

(* apply a substitution within a function *)
val gsubst_func : (?loc:L.t -> 'ty1 -> 'ty2) -> ('ty1 ggvar -> ('sop1, 'sop2, 'ty2) gexpr) -> ('sop1, 'sop2, 'ty1, 'info, 'asm) gfunc -> ('sop1, 'sop2, 'ty2, 'info, 'asm) gfunc

(* apply a substitution within a function *)
val subst_func : ('ty gvar_i -> ('sop1, 'sop2, 'ty) gexpr) -> ('sop1, 'sop2, 'ty, 'info, 'asm) gfunc -> ('sop1, 'sop2, 'ty, 'info, 'asm) gfunc

(* replace parameter by their definition everywhere in the program *)
val remove_params : ('info, 'asm) pprog -> (E.sop1, E.sop2, 'info, 'asm) prog

(* rename all variable using fresh variables *)
val clone_func : ('sop1, 'sop2, 'info, 'asm) func -> ('sop1, 'sop2, 'info, 'asm) func

val extend_iinfo : L.i_loc -> ('sop1, 'sop2, 'info, 'asm) func -> ('sop1, 'sop2, 'info, 'asm) func
(* ---------------------------------------------------------------- *)
(* Perform a substitution of variable by variable                   *)

type vsubst = var Mv.t

val vsubst_v : vsubst -> var -> var

val vsubst_vi : vsubst -> var_i -> var_i

val vsubst_e  : vsubst -> ('sop1, 'sop2) expr  -> ('sop1, 'sop2) expr
val vsubst_es : vsubst -> ('sop1, 'sop2) exprs -> ('sop1, 'sop2) exprs

val vsubst_lval  : vsubst -> ('sop1, 'sop2) lval  -> ('sop1, 'sop2) lval
val vsubst_lvals : vsubst -> ('sop1, 'sop2) lvals -> ('sop1, 'sop2) lvals

val vsubst_i : vsubst -> ('sop1, 'sop2, 'info, 'asm) instr -> ('sop1, 'sop2, 'info, 'asm) instr
val vsubst_c : vsubst -> ('sop1, 'sop2, 'info, 'asm) stmt  -> ('sop1, 'sop2, 'info, 'asm) stmt

val vsubst_func : vsubst -> ('sop1, 'sop2, 'info, 'asm) func -> ('sop1, 'sop2, 'info, 'asm) func
