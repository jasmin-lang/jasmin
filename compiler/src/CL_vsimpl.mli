open ToCL
open Prog

module Cfg : sig
  type node

  val prog_of_cfg : node -> CL.Instr.instr list
  val cfg_of_prog_rev : CL.Instr.instr list -> node

end

module GhostVector : sig

  val get_unfolded_vector_namei: Prog.var -> int -> string

  (* val unfold_ghosts_epre: (Prog.var * CL.ty) list -> CL.I.epred list -> CL.I.epred list *)
  (* val unfold_ghosts_rpred: (string * (Prog.var * CL.ty)) list -> CL.R.rpred list -> CL.R.rpred list *)
  val unfold_vghosts_rpred: (Prog.var * CL.ty) list -> CL.R.rpred list -> CL.R.rpred list
  val unfold_vghosts_epred: (Prog.var * CL.ty) list -> CL.I.epred list -> CL.I.epred list

  (* val unfold_vector: (Prog.var * CL.ty) list -> (string * CL.Instr.lval) list * CL.Instr.instr list *)
  val unfold_vectors: (Prog.var * CL.ty) list -> CL.Instr.lval list * CL.Instr.instr list

end

module SimplVector: sig

  val simpl_cfg: Cfg.node -> Cfg.node

end
