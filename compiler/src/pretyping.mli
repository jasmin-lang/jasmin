type tyerror

exception TyError of Location.t * tyerror

val pp_tyerror : Format.formatter -> tyerror -> unit

type fun_sig = { fs_tin : Prog.epty list ; fs_tout : Prog.epty list }

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
    val push : 'asm env -> (unit, 'asm) Prog.pfunc -> fun_sig -> 'asm env

    val find :
      Annotations.symbol ->
      'asm env ->
      ((unit, 'asm) Prog.pfunc * fun_sig) option
  end

  module Exec : sig
    val push :
      Location.t -> Prog.funname -> (Z.t * Z.t) list -> 'asm env -> 'asm env

    val get :
      'asm env -> (Prog.funname * (Z.t * Z.t) list) Location.located list
  end
end

val tt_prim : 'asm Sopn.asmOp -> Annotations.symbol Location.located -> 'asm

val tt_item :
  'asm Prog.arch_info ->
  'asm Env.env ->
  Syntax.pitem Location.located ->
  'asm Env.env

val tt_param :
  Wsize.wsize -> 'asm Env.env -> 'a -> Syntax.pparam -> 'asm Env.env

val tt_fundef :
  'asm Prog.arch_info ->
  'asm Env.env ->
  Location.t ->
  Syntax.pfundef ->
  'asm Env.env

val tt_global :
  Wsize.wsize -> 'asm Env.env -> 'a -> Syntax.pglobal -> 'asm Env.env

val tt_fun :
  'asm Env.env ->
  Annotations.symbol Location.located ->
  (unit, 'asm) Prog.pfunc * fun_sig

val tt_program :
  'asm Prog.arch_info ->
  'asm Env.env ->
  string ->
  'asm Env.env
  * (unit, 'asm) Prog.pmod_item
    list
  * Syntax.pprogram

val tt_file :
  'asm Prog.arch_info ->
  'asm Env.env ->
  Annotations.pident option ->
  Location.t option ->
  string ->
  'asm Env.env * Syntax.pprogram
