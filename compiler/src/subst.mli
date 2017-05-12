open Prog

(* apply a substitution within a function *)
val gsubst_func : ('ty1 -> 'ty2) -> ('ty1 gvar_i -> 'ty2 gexpr) -> ('ty1, 'info) gfunc -> ('ty2, 'info) gfunc

(* replace parameter by their definition everywhere in the program *)
val remove_params : 'info pprog -> 'info prog

(* rename all variable using fresh variables *)
val clone_func : 'info func -> 'info func

(* ---------------------------------------------------------------- *)
(* Perform a substitution of variable by variable                   *) 

type vsubst = var Mv.t 

val vsubst_v : vsubst -> var -> var 

val vsubst_vi : vsubst -> var_i -> var_i 
  
val vsubst_e  : vsubst -> expr  -> expr 
val vsubst_es : vsubst -> exprs -> exprs 

val vsubst_lval  : vsubst -> lval  -> lval 
val vsubst_lvals : vsubst -> lvals -> lvals 

val vsubst_i : vsubst -> 'info instr -> 'info instr
val vsubst_c : vsubst -> 'info stmt  -> 'info stmt

val vsubst_func : vsubst -> 'info func -> 'info func
