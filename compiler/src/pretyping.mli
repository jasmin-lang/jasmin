val prim_string : 'asm Sopn.asmOp -> (string * 'asm Sopn.prim_constructor) list

type tyerror

exception TyError of Location.t * tyerror

val pp_tyerror : Format.formatter -> tyerror -> unit

module Env : sig
  type 'asm env

  val empty : 'asm env
  val decls : 'asm env -> (unit, 'asm) Prog.pmod_item list
  val add_from : 'asm env -> string * string -> 'asm env
  val dependencies : 'asm env -> string list list

  module Exec : sig
    val push :
      Location.t -> Prog.funname -> (Z.t * Z.t) list -> 'asm env -> 'asm env

    val get :
      'asm env -> (Prog.funname * (Z.t * Z.t) list) Location.located list
  end
end

val tt_ws : Annotations.wsize -> Wsize.wsize

val tt_item :
  Wsize.wsize ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.sopn Sopn.asmOp ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env ->
  Syntax.pitem Location.located ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env

val tt_program :
  Wsize.wsize ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.sopn Sopn.asmOp ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env ->
  string ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env
  * (unit, ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op) Prog.pmod_item
    list
  * Syntax.pprogram

val tt_file :
  Wsize.wsize ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.sopn Sopn.asmOp ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env ->
  Annotations.pident option ->
  Location.t option ->
  string ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env * Syntax.pprogram
