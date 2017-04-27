open Prog

(* replace parameter by their definition everywhere in the program *)
val remove_params : 'info pprog -> 'info prog

(* rename all variable using fresh variables *)
val clone_func : 'info func -> 'info func
