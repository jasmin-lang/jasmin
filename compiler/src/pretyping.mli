type tyerror

exception TyError of Location.t * tyerror

val pp_tyerror : Format.formatter -> tyerror -> unit

module Env : sig
  type 'asm env

  val empty : 'asm env
  val decls : 'asm env -> (unit, 'asm) Prog.pmod_item list
  val add_from : 'asm env -> string * string -> 'asm env
  val dependencies : 'asm env -> string list list

  val enter_file :
    'asm env ->
    Annotations.pident option ->
    Location.t option ->
    string ->
    ('asm env * string) option

  val exit_file : 'asm env -> 'asm env

  module Funs : sig
    val push : 'asm env -> (unit, 'asm) Prog.pfunc -> Prog.pty list -> 'asm env

    val find :
      Annotations.symbol ->
      'asm env ->
      ((unit, 'asm) Prog.pfunc * Prog.pty list) option
  end

  module Exec : sig
    val push :
      Location.t -> Prog.funname -> (Z.t * Z.t) list -> 'asm env -> 'asm env

    val get :
      'asm env -> (Prog.funname * (Z.t * Z.t) list) Location.located list
  end
end

val tt_ws : Annotations.wsize -> Wsize.wsize
val tt_prim : 'op Sopn.asmOp -> Annotations.symbol Location.located -> 'op

type ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info = {
  pd : Wsize.wsize;
  asmOp :
    ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.sopn Sopn.asmOp;
  known_implicits : (CoreIdent.Name.t * string) list;
  flagnames : CoreIdent.Name.t list;
}

val tt_item :
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env ->
  Syntax.pitem Location.located ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env

val tt_param :
  Wsize.wsize -> 'asm Env.env -> 'a -> Syntax.pparam -> 'asm Env.env

val tt_fundef :
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env ->
  Location.t ->
  Syntax.pfundef ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env

val tt_global :
  Wsize.wsize -> 'asm Env.env -> 'a -> Syntax.pglobal -> 'asm Env.env

val tt_fun :
  'asm Env.env ->
  Annotations.symbol Location.located ->
  (unit, 'asm) Prog.pfunc * Prog.pty list

val tt_program :
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env ->
  string ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env
  * (unit, ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op) Prog.pmod_item
    list
  * Syntax.pprogram

val tt_file :
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env ->
  Annotations.pident option ->
  Location.t option ->
  string ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env * Syntax.pprogram
