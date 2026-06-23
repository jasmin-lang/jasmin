open Utils
module F = Format
module A = Annotations
module L = Location
module S = Syntax
module P = Prog
module W = Wsize

type sop

type tyerror =
  | UnknownVar          of A.symbol
  | UnknownFun          of A.symbol
  | InvalidArrayType    of P.epty
  | TypeMismatch        of P.epty pair
  | NoOperator          of sop * P.epty list
  | InvalidOperator     of sop
  | NoReturnStatement   of P.funname * int
  | InvalidReturnStatement of P.funname * int * int
  | InvalidSignatureStorage of P.funname * S.pstorage * A.symbol * W.v_kind
  | InvalidArgCount     of int * int
  | InvalidLvalCount    of int * int
  | DuplicateFun        of A.symbol * L.t
  | DuplicateAlias      of A.symbol * P.epty L.located * P.epty L.located
  | DuplicateModule	of A.symbol * Mprog.modulename L.located * Mprog.modulename L.located
  | TypeNotFound        of A.symbol
  | ModuleNotFound      of A.symbol
  | InvalidTypeAlias    of A.symbol L.located option * P.epty
  | InvalidCast         of P.epty pair
  | InvalidTypeForGlobal of P.epty
  | GlobArrayNotWord
  | GlobWordNotArray
  | EqOpWithNoLValue
  | CallNotAllowed
  | PrimNotAllowed
  | Unsupported         of string
  | UnknownPrim of A.symbol * string
  | PrimWrongSuffix of A.symbol * Sopn.prim_x86_suffix list
  | PtrOnlyForArray
  | PackSigned
  | PackWrongWS of int
  | PackWrongPE of int
  | PackWrongLength of int * int
  | UnsupportedZeroExtend of (F.formatter -> unit)
  | InvalidZeroExtend of W.wsize * W.wsize * (F.formatter -> unit)
  | StringError of string

exception TyError of Location.t * tyerror

val tyerror : loc:Location.t -> tyerror -> exn
val rs_tyerror: loc:L.t -> tyerror -> 'a
val pp_tyerror : F.formatter -> tyerror -> unit
  
type 'asm pfuncsig = { 
      f_loc : L.t
    ; f_name : P.funname
    ; f_tyin : P.pty list
    ; f_tyout : P.pty list
    ; f_pfunc : (unit,'asm) P.pfunc option (* full description, if available *)
}

type fun_sig = { fs_tin : Prog.epty list ; fs_tout : Prog.epty list }

type 'asm global_bindings = {
    gb_types : (A.symbol, P.epty L.located) Map.t;
    gb_vars : (A.symbol, P.pvar * P.epty * Expr.v_scope) Map.t;
    gb_funs : (A.symbol, 'asm pfuncsig * fun_sig) Map.t;
    gb_modules: (A.symbol, A.symbol L.located) Map.t
}

module Env : sig
  type 'asm env
  type 'asm store
  
  val store : 'asm env -> 'asm store
  val bindings : 'asm store -> (A.symbol * 'asm global_bindings * bool) list * 'asm global_bindings
  val params : 'asm store -> (P.pvar, P.pexpr) Map.t

  val empty_gb : 'asm global_bindings
  val empty_store : 'asm store
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

  val enter_namespace: string L.located -> 'a store -> 'a store
  
  val merge_bindings: string * 'a global_bindings -> 'a global_bindings -> 'a global_bindings
  val update_bindings: 'asm store -> (string * 'asm global_bindings * bool) list * 'asm global_bindings -> 'asm store

  module Modules : sig
    val push : 'asm store -> A.pident -> A.symbol -> 'asm store
    val get : 'asm store -> A.pident -> ((string * 'asm global_bindings * bool) list * ((string * 'asm global_bindings * bool) list * 'asm global_bindings)) * string L.located
  end

  module Funs : sig
    val push : 'asm store -> (unit, 'asm) Prog.pfunc -> fun_sig -> ('asm store * (unit, 'asm) P.pmod_item list)
    val push_modp_fun : 'asm store -> 'asm pfuncsig -> fun_sig -> 'asm pfuncsig * 'asm store

    val find :
      Annotations.symbol ->
      'asm store ->
      ('asm pfuncsig * fun_sig) option
  end

  module Vars: sig
    val push_global   : 'asm store -> (P.pvar * P.epty * P.pexpr_ P.ggexpr ) -> ('asm store * (unit, 'asm) P.pmod_item list)
    val push_modp_global : 'a store -> P.pexpr_ CoreIdent.gvar -> P.epty -> P.pexpr_ CoreIdent.gvar * 'a store
    val push_param    : 'asm store -> (P.pvar * P.epty * P.pexpr * P.pexpr) -> ('asm store* (unit, 'asm) P.pmod_item list)
    val push_modp_param    : 'asm store -> L.t -> P.pvar -> P.epty -> P.pvar * 'asm store
    val push_local    : ?warn:bool -> 'asm store -> P.pvar * P.epty -> 'asm store
    val push_implicit : 'asm store -> P.pvar * P.epty -> 'asm store

    val find : A.symbol -> 'asm store -> (P.pvar * P.epty * Expr.v_scope) option

    val iter_locals  : (P.pvar -> unit) -> 'asm store -> unit
    val clear_locals : 'asm store -> 'asm store
  end

  module Exec : sig
    val push :
      Location.t -> Prog.funname -> (Z.t * Z.t) list -> 'asm env -> 'asm env

    val get :
      'asm env -> (Prog.funname * (Z.t * Z.t) list) Location.located list
  end
end

val qualify: string -> string -> string

val tt_type: W.wsize -> 'asm Env.store -> S.ptype -> P.epty

val tt_prim : 'op Sopn.asmOp -> Annotations.symbol Location.located -> 'op

type ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info = {
  pd : Wsize.wsize;
  asmOp :
    ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Sopn.sopn Sopn.asmOp;
  known_implicits : (CoreIdent.Name.t * string) list;
  flagnames : CoreIdent.Name.t list;
}

val f_sig: 'asm pfuncsig -> P.pty list * P.pty list


type tt_mode = [
  | `AllVar
  | `OnlyParam
  | `NoParam
  ]


val tt_expr: W.wsize ->
?mode:tt_mode ->
'asm Env.store ->
S.pexpr_r L.located ->
P.pexpr_ P.gexpr * P.pexpr_ CoreIdent.gety * P.pexpr option

val tt_typealias: ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info ->
A.pident -> S.ptype -> 'h Env.store -> 'h Env.store

val tt_item :
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env ->
  Syntax.pitem Location.located ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.env

val tt_param : W.wsize -> S.pparam -> 'asm Env.store -> 'asm Env.store * (unit, 'asm) P.pmod_item list

val tt_fundef :
 ('a, 'b, 'c, 'd, 'e, 'f, 'g) arch_info ->
L.t ->
S.pfundef ->
('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.store ->
('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op Env.store *
(unit, ('a, 'b, 'c, 'd, 'e, 'f, 'g) Arch_extra.extended_op) P.pmod_item list

val tt_global : W.wsize -> S.pglobal -> 'asm Env.store -> 'asm Env.store * (unit, 'asm) P.pmod_item list

val tt_var_global: tt_mode ->
'asm Env.store ->
string L.located -> P.pexpr_ P.ggvar * P.epty * P.pexpr option


val tt_fun : 'asm Env.store -> string L.located -> 'asm pfuncsig * fun_sig

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
