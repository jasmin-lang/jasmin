open Prog

val get_declaration_sites : ('info, 'asm) func -> Sv.t Utils.Miloc.t
(** Computes for each instruction the set of variables to declare before it. *)
