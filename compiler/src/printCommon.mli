val escape : string -> string
(** replace dots & columns by underscores *)

val pp_wsize : Format.formatter -> Wsize.wsize -> unit
val string_of_signess : Wsize.signedness -> string
val string_of_velem : Wsize.signedness -> Wsize.wsize -> Wsize.velem -> string
val string_of_op1 : debug:bool -> Operators.sop1 -> string
val string_of_op2 : Operators.sop2 -> string

val pp_opn :
  Wsize.wsize ->
  Wsize.wsize -> 'asm Sopn.asmOp -> Format.formatter -> 'asm Sopn.sopn -> unit

val pp_syscall : (Wsize.wsize * BinNums.coq_N) Syscall_t.syscall_t -> string
val pp_bool : Format.formatter -> bool -> unit
val pp_kind : Format.formatter -> Wsize.v_kind -> unit
val pp_btype : ?w:Wsize.signedness -> Format.formatter -> Prog.base_ty -> unit

val pp_gtype :
  ?w:Wsize.signedness ->
  (Format.formatter -> 'size -> unit) ->
  Format.formatter ->
  'size Prog.gty ->
  unit

val non_default_wsize : 'len Prog.gvar -> Wsize.wsize -> Wsize.wsize option

val pp_mem_access :
  'expr Utils.pp ->
  Format.formatter ->
  Memory_model.aligned ->
  Wsize.wsize option ->
  'expr ->
  unit

val pp_arr_access :
  'var Utils.pp ->
  'len Prog.gexpr Utils.pp ->
  Format.formatter ->
  Memory_model.aligned ->
  Warray_.arr_access ->
  Wsize.wsize option ->
  'var ->
  'len Prog.gexpr ->
  unit

val pp_arr_slice :
  'var Utils.pp ->
  'len Prog.gexpr Utils.pp ->
  'len Utils.pp ->
  Format.formatter ->
  Warray_.arr_access ->
  Wsize.wsize option ->
  'var ->
  'len Prog.gexpr ->
  'len ->
  unit

val pp_len : Format.formatter -> int -> unit
val pp_ty : Format.formatter -> Prog.ty -> unit
val pp_datas : Format.formatter -> Word0.word list -> unit
val pp_var : Format.formatter -> Var0.Var.var -> unit
val pp_var_i : Format.formatter -> Expr.var_i -> unit

type priority
(** Priority levels of operators *)

type associativity = Left | NoAssoc | Right  (** Associativity of operators *)

val associativity : priority -> associativity
(** Associativity of a priority level *)

val priority_min : priority
(** Minimal priority level *)

val priority_of_op1 : Operators.sop1 -> priority
(** Priority level of unary operators *)

val priority_of_op2 : Operators.sop2 -> priority
(** Priority level of binary operators *)

val priority_ternary : priority
(** Priority level of the ternary “_ ? _ : _” operator *)

val optparent :
  Format.formatter ->
  priority ->
  associativity ->
  priority ->
  ('a, Format.formatter, unit) format ->
  'a
(** Print within optional enclosing parentheses. *)
