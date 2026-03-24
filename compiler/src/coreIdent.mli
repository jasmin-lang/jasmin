(* ------------------------------------------------------------------------ *)
open Utils
open Wsize

module L = Location

module Name : sig
  type t = string
end

type uid

val string_of_uid : uid -> string

(* ------------------------------------------------------------------------ *)
type base_ty =
  | Bool
  | Int              (* Unbounded integer for pexpr *)
  | U   of wsize (* U(n): unsigned n-bit integer *)
  [@@deriving compare,sexp]

type 'len gty =
  | Bty of base_ty
  | Arr of wsize * 'len (* Arr(n,de): array of n-bit integers with dim. *)
           (* invariant only Const variable can be used in expression *)
           (* the type of the expression is [Int] *)

type 'len gety =
  | ETbool
  | ETint
  | ETword of signedness option * wsize
  | ETarr  of wsize * 'len (* Arr(n,de): array of n-bit integers with dim. *)
           (* invariant only Const variable can be used in expression *)
           (* the type of the expression is [Int] *)

val u8    : 'len gty
val u16   : 'len gty
val u32   : 'len gty
val u64   : 'len gty
val u128  : 'len gty
val u256  : 'len gty
val tu    : wsize -> 'len gty
val tbool : 'len gty
val tint  : 'len gty

val etw    : wsize -> 'len gety
val etwi   : signedness -> wsize -> 'len gety
val etbool : 'len gety
val etint  : 'len gety

val gty_of_gety : 'len gety -> 'len gty

(* ------------------------------------------------------------------------ *)

type +'len gvar = private {
  v_name : Name.t;
  v_id   : uid;
  v_kind : v_kind;
  v_ty   : 'len gty;
  v_dloc : L.t;   (* location where declared *)
  v_annot : Annotations.annotations;
}

(* ------------------------------------------------------------------------ *)
module GV : sig
  val mk : Name.t -> v_kind -> 'len gty -> L.t -> Annotations.annotations -> 'len gvar

  val clone : ?dloc: L.t -> 'len gvar -> 'len gvar

  val compare : 'len gvar -> 'len gvar -> int

  val equal : 'len gvar -> 'len gvar -> bool

  val hash : 'len gvar -> int

  val is_length_var : 'len gvar -> bool

  val cast : 'len1 gvar -> 'len2 gvar
end

(* ------------------------------------------------------------------------ *)
(* Non parametrized variable                                                *)

type length =
  | Const of int (* FIXME: Z.t ? *)
  | Var of length gvar
  | Neg of length
  | Add of length * length
  | Sub of length * length
  | Mul of length * length
  | Div of signedness * length * length
  | Mod of signedness * length * length
  | Shl of length * length
  | Shr of length * length

type ty    = length gty
type var   = length gvar

val subst_al : (var -> length option) -> length -> length
val subst_ety : (var -> length option) -> length gety -> length gety
val subst_ty : (var -> length option) -> ty -> ty

module V : sig
  type t = var

  val mk : Name.t -> v_kind -> ty -> L.t -> Annotations.annotations -> var

  val clone : ?dloc: L.t -> var -> var

  val compare : var -> var -> int

  val equal : var -> var -> bool

  val hash : var -> int

  val is_length_var : var -> bool
end

(* Cident *)

module Cident : sig
  type t = var

  val tag : var -> Uint63.t
  val id_name : t -> Name.t
  val id_kind : t -> v_kind

  val spill_to_mmx : t -> bool
end

(* -------------------------------------------------------------------- *)
type funname = private {
  fn_name : Name.t;
  fn_id   : uid;
}

val funname_tag : funname -> Uint63.t

module F : sig
  val mk : Name.t -> funname

  val compare : funname -> funname -> int

  val equal : funname -> funname -> bool

  val hash : funname -> int
end

module Sf : Set.S  with type elt = funname
module Mf : Map.S  with type key = funname
module Hf : Hash.S with type key = funname
