module StackAlloc (Arch: Arch_full.Arch) : sig

  val memory_analysis :
    (unit Conv.coq_tbl -> Format.formatter -> Compiler_util.pp_error -> unit) ->
    debug:bool ->
    unit Conv.coq_tbl -> (Arch.reg, Arch.regx, Arch.xreg, Arch.rflag, Arch.cond, Arch.asm_op, Arch.extra_op) Arch_extra.extended_op Expr._uprog -> Compiler.stack_alloc_oracles

end
