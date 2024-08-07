open ToCL

module Cfg : sig
  type node

  val prog_of_cfg : node -> CL.Instr.instr list
  val cfg_of_prog_rev : CL.Instr.instr list -> node

end

module SimplVector: sig

  val simpl_cfg: Cfg.node -> Cfg.node

end
