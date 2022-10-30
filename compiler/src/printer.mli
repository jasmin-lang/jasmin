open Prog

val ws_of_ws : Annotations.wsize -> Wsize.wsize

val pp_warning_msg :  Format.formatter -> Compiler_util.warning_msg -> unit
val pp_err : debug:bool -> Conv.coq_tbl ->
             Format.formatter -> Compiler_util.pp_error -> unit

val pp_print_X : Format.formatter -> Z.t -> unit

val pp_pvar  : Format.formatter -> pvar -> unit
val pp_ptype : Format.formatter -> pty -> unit
val pp_plval : Format.formatter -> pexpr glval -> unit
val pp_pexpr : Format.formatter -> pexpr -> unit
val pp_pprog : ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
               Format.formatter -> ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) pprog -> unit

val pp_var   : debug:bool -> Format.formatter -> var -> unit

val string_of_combine_flags : Expr.combine_flags -> string

val pp_expr  : debug:bool -> Format.formatter -> expr -> unit
val pp_lval  : debug:bool -> Format.formatter -> lval -> unit

val pp_instr : debug:bool ->
               ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
               Format.formatter -> ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) instr -> unit

val pp_stmt  : debug:bool ->
               ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
               Format.formatter -> ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) stmt  -> unit

val pp_ifunc : debug:bool -> (Format.formatter -> 'info -> unit) ->
               ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
               Format.formatter -> ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) func -> unit

val pp_func  : debug:bool ->
               ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
               Format.formatter -> ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) func -> unit

val pp_iprog : debug:bool -> (Format.formatter -> 'info -> unit) ->
               ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
               Format.formatter -> ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) prog -> unit

val pp_prog  : debug:bool ->
               ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
               Format.formatter -> ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) prog -> unit

val pp_to_save : debug:bool -> Conv.coq_tbl ->
                 Format.formatter -> Var0.Var.var * BinNums.coq_Z -> unit
val pp_saved_stack : debug:bool -> Conv.coq_tbl ->
                     Format.formatter -> Expr.saved_stack -> unit
val pp_return_address : debug:bool -> Conv.coq_tbl ->
                        Format.formatter -> Expr.return_address_location -> unit

val pp_sprog : debug:bool ->
               Conv.coq_tbl ->
               ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op Sopn.asmOp ->
               Format.formatter -> ('info, ('reg, 'regx, 'xreg, 'rflag, 'cond, 'asm_op, 'extra_op) Arch_extra.extended_op) sprog -> unit

