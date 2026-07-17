val apply_ret_annot : bool list -> FInfo.t -> FInfo.t
  (** Selects a subset of the [ret_annot] part of [FInfo.t]. *)

module StackAlloc (Arch: Arch_full.Arch) : sig

  val memory_analysis :
    (Stack_alloc.sub_region -> Compiler_util.pp_error) ->
    (Format.formatter -> Compiler_util.pp_error -> unit) ->
    debug:bool ->
    Utils.callee_saved_strategy ->
    Arch.extended_op Expr._uprog -> Compiler.stack_alloc_oracles

end
