open Prog

(* apply a substitution within a function *)
val subst_func : ('ty1 gvar_i -> 'ty2 gexpr) -> ('ty1, 'info) gfunc -> ('ty2, 'info) gfunc

(* replace parameter by their definition everywhere in the program *)
val remove_params : 'info pprog -> 'info prog

(* rename all variable using fresh variables *)
val clone_func : 'info func -> 'info func
