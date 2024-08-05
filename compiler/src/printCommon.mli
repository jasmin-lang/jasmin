val escape : string -> string
(** replace dots & columns by underscores *)

val pp_wsize : Format.formatter -> Wsize.wsize -> unit
val pp_aligned : Format.formatter -> Memory_model.aligned -> unit
val string_of_signess : Wsize.signedness -> string
val string_of_velem : Wsize.signedness -> Wsize.wsize -> Wsize.velem -> string
val string_of_op1 : Expr.sop1 -> string
val string_of_op2 : Expr.sop2 -> string
val pp_opn :
  Wsize.wsize -> 'asm Sopn.asmOp -> Format.formatter -> 'asm Sopn.sopn -> unit
val pp_syscall : BinNums.positive Syscall_t.syscall_t -> string
val pp_bool : Format.formatter -> bool -> unit
val pp_kind : Format.formatter -> Wsize.v_kind -> unit
val pp_btype : Format.formatter -> Prog.base_ty -> unit

val pp_gtype :
  (Format.formatter -> 'size -> unit) ->
  Format.formatter ->
  'size Prog.gty ->
  unit

val pp_arr_access :
  'var Utils.pp ->
  'expr Utils.pp ->
  Format.formatter ->
  Memory_model.aligned ->
  Warray_.arr_access ->
  Wsize.wsize ->
  'var ->
  'expr ->
  unit

val pp_arr_slice :
  'var Utils.pp ->
  'expr Utils.pp ->
  'len Utils.pp ->
  Format.formatter ->
  Warray_.arr_access ->
  Wsize.wsize ->
  'var ->
  'expr ->
  'len ->
  unit

val pp_len : Format.formatter -> int -> unit
val pp_ty : Format.formatter -> Prog.ty -> unit
val pp_datas : Format.formatter -> Ssralg.GRing.ComRing.sort list -> unit
val pp_var : Format.formatter -> Var0.Var.var -> unit
val pp_var_i : Format.formatter -> Expr.var_i -> unit
