open ToCL
open Prog

module Cfg : sig
  type node

  val prog_of_cfg : node -> CL.Instr.instr list
  val cfg_of_prog_rev : CL.Instr.instr list -> node

end

module GhostVector : sig
  val get_unfolded_vector_namei: Prog.var -> int -> string
  val unfold_vghosts_rpred: (Prog.var * CL.ty) list -> CL.R.rpred list -> CL.R.rpred list * CL.tyvar list
  val unfold_vghosts_epred: (Prog.var * CL.ty) list -> CL.I.epred list -> CL.I.epred list * CL.tyvar list
  val unfold_cfg_clauses: CL.Instr.instr list -> (Prog.var * CL.ty) list -> CL.Instr.instr list
  val unfold_vectors: (Prog.var * CL.ty) list -> (Prog.var * CL.ty) list -> (Prog.var * CL.ty)list * CL.Instr.instr list * CL.Instr.instr list
end

module SimplVector: sig
  val get_clause_vars: CL.I.epred list -> CL.R.rpred list -> CL.tyvar list
  val simpl_cfg: Cfg.node -> CL.tyvar list -> Cfg.node
end
