val pp_string0 : Format.formatter -> char list -> unit
val pp_wsize : Format.formatter -> Wsize.wsize -> unit
val string_of_signess : Wsize.signedness -> string
val string_of_op1 : Expr.sop1 -> string
val string_of_op2 : Expr.sop2 -> string
val pp_opn : 'asm Sopn.asmOp -> Format.formatter -> 'asm Sopn.sopn -> unit
val pp_syscall : BinNums.positive Syscall_t.syscall_t -> string
val pp_bool : Format.formatter -> bool -> unit
val pp_kind : Format.formatter -> Prog.v_kind -> unit
val pp_btype : Format.formatter -> Prog.base_ty -> unit

val pp_gtype :
  (Format.formatter -> 'size -> unit) ->
  Format.formatter ->
  'size Prog.gty ->
  unit

val pp_arr_access :
  (Format.formatter -> 'a -> unit) ->
  (Format.formatter -> 'b -> unit) ->
  (Format.formatter -> 'c -> unit) ->
  Format.formatter ->
  Warray_.arr_access ->
  Wsize.wsize ->
  'a ->
  'b ->
  'c option ->
  unit

val pp_len : Format.formatter -> int -> unit
val pp_ty : Format.formatter -> Prog.ty -> unit
val pp_datas : Format.formatter -> Ssralg.GRing.ComRing.sort list -> unit
val pp_var : Conv.coq_tbl -> Format.formatter -> Var0.Var.var -> unit
val pp_var_i : Conv.coq_tbl -> Format.formatter -> Expr.var_i -> unit
