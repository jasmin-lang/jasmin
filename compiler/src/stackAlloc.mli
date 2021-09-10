val memory_analysis :
  (unit Conv.coq_tbl -> Format.formatter -> Compiler_util.pp_error_loc -> unit) ->
  debug:bool -> unit Conv.coq_tbl -> 
  Expr._uprog -> Compiler.stack_alloc_oracles
