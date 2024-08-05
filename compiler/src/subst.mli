open Prog

(* apply a substitution within a function *)
val gsubst_func : (?loc:L.t -> 'ty1 -> 'ty2) -> ('ty1 ggvar -> 'ty2 gexpr) -> ('ty1, 'info, 'asm) gfunc -> ('ty2, 'info, 'asm) gfunc

(* apply a substitution within a function *)
val subst_func : ('ty gvar_i -> 'ty gexpr) -> ('ty, 'info, 'asm) gfunc -> ('ty, 'info, 'asm) gfunc

(* replace parameter by their definition everywhere in the program *)
val remove_params : ('info, 'asm) pprog -> ('info, 'asm) prog

(* rename all variable using fresh variables *)
val clone_func : ('info, 'asm) func -> ('info, 'asm) func

val extend_iinfo : L.i_loc -> ('info, 'asm) func -> ('info, 'asm) func
(* ---------------------------------------------------------------- *)
(* Perform a substitution of variable by variable                   *)

type vsubst = var Mv.t

val vsubst_v : vsubst -> var -> var

val vsubst_vi : vsubst -> var_i -> var_i

val vsubst_e  : vsubst -> expr  -> expr
val vsubst_es : vsubst -> exprs -> exprs

val vsubst_lval  : vsubst -> lval  -> lval
val vsubst_lvals : vsubst -> lvals -> lvals

val vsubst_i : vsubst -> ('info, 'asm) instr -> ('info, 'asm) instr
val vsubst_c : vsubst -> ('info, 'asm) stmt  -> ('info, 'asm) stmt

val vsubst_func : vsubst -> ('info, 'asm) func -> ('info, 'asm) func
