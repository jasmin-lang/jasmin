open Utils
module F = Format
module A = Annotations
module L = Location
module S = Syntax
module P = Prog
module W = Wsize

type typattern = TPBool | TPInt | TPWord | TPArray

type sop

type tyerror =
  | UnknownVar          of A.symbol
  | UnknownFun          of A.symbol
  | InvalidType         of P.pty * typattern
  | TypeMismatch        of P.pty pair
  | NoOperator          of sop * P.pty list
  | InvalidOperator     of sop
  | NoReturnStatement   of P.funname * int
  | InvalidReturnStatement of P.funname * int * int
  | InvalidArgCount     of int * int
  | InvalidLvalCount    of int * int
  | DuplicateFun        of A.symbol * L.t
  | DuplicateAlias      of A.symbol * P.pty L.located * P.pty L.located
  | TypeNotFound        of A.symbol
  | InvalidTypeAlias    of A.symbol * P.pty
  | InvalidCast         of P.pty pair
  | InvalidTypeForGlobal of P.pty
  | NotAPointer         of P.plval
  | GlobArrayNotWord    
  | GlobWordNotArray
  | EqOpWithNoLValue
  | CallNotAllowed
  | PrimNotAllowed
  | Unsupported         of string
  | UnknownPrim of A.symbol * string
  | PrimWrongSuffix of A.symbol * Sopn.prim_x86_suffix list
  | PtrOnlyForArray
  | WriteToConstantPointer of A.symbol
  | PackSigned
  | PackWrongWS of int
  | PackWrongPE of int
  | PackWrongLength of int * int
  | UnsupportedZeroExtend of (F.formatter -> unit)
  | InvalidZeroExtend of W.wsize * W.wsize * (F.formatter -> unit)
  | StringError of string

exception TyError of Location.t * tyerror

val tyerror : loc:Location.t -> tyerror -> exn
val pp_tyerror : F.formatter -> tyerror -> unit

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
