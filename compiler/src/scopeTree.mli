open Prog

val get_declaration_sites : ('info, 'asm) pfunc -> Spv.t Utils.Miloc.t
(** Computes for each instruction the set of variables to declare before it. *)
