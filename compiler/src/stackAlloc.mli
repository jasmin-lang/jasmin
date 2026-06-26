val apply_ret_annot : (Obj.t -> Obj.t list -> Obj.t list) -> FInfo.t -> FInfo.t
  (** Apply a function (operating on lists) on the [ret_annot] part of [FInfo.t].
      The signature is inherited from Rocq, hence the ugly [Obj.t]. *)

module StackAlloc (Arch: Arch_full.Arch) : sig

  val memory_analysis :
    (Stack_alloc.sub_region -> Compiler_util.pp_error) ->
    (Format.formatter -> Compiler_util.pp_error -> unit) ->
    debug:bool ->
    (Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op, Arch.extra_op) Arch_extra.extended_op Expr._uprog -> Compiler.stack_alloc_oracles

end
