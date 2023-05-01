(* ------------------------------------------------------------------------ *)
open Utils
open Wsize

module L = Location

module Name : sig
  type t = string
end

type uid

val int_of_uid : uid -> int

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

val u8    : 'len gty
val u16   : 'len gty
val u32   : 'len gty
val u64   : 'len gty
val u128  : 'len gty
val u256  : 'len gty
val tu    : wsize -> 'len gty
val tbool : 'len gty
val tint  : 'len gty

(* ------------------------------------------------------------------------ *)

type writable = Constant | Writable
type pointer = Direct | Pointer of writable

type reg_kind = Normal | Extra

type v_kind =
  | Const            (* global parameter  *)
  | Stack of pointer (* stack variable    *)
  | Reg   of reg_kind * pointer (* register variable *)
  | Inline           (* inline variable   *)
  | Global           (* global (in memory) constant *)

type 'len gvar = private {
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

  val clone : 'len gvar -> 'len gvar

  val compare : 'len gvar -> 'len gvar -> int

  val equal : 'len gvar -> 'len gvar -> bool

  val hash : 'len gvar -> int

  val is_glob : 'len gvar -> bool

  (* Fixme : still used *)
  val is_local : 'len gvar -> bool

end

(* ------------------------------------------------------------------------ *)
(* Non parametrized variable                                                *)

type ty    = int gty
type var   = int gvar

module V : sig
  type t = var

  val mk : Name.t -> v_kind -> ty -> L.t -> Annotations.annotations -> var

  val clone : var -> var

  val compare : var -> var -> int

  val equal : var -> var -> bool

  val hash : var -> int

  val is_glob : var -> bool

  (* Fixme : still used *)
  val is_local : var -> bool
end

(* Cident *)

module Cident : sig
  type t = var
  type name = Name.t

  val tag : var -> int
  val id_name : t -> Name.t

  val dummy : t
  val p__   : name
  val len__ : name

  module X86 : sig

    val iRAX : t
    val iRCX : t
    val iRDX : t
    val iRBX : t
    val iRSP : t
    val iRBP : t
    val iRSI : t
    val iRDI : t
    val iR8  : t
    val iR9  : t
    val iR10 : t
    val iR11 : t
    val iR12 : t
    val iR13 : t
    val iR14 : t
    val iR15 : t

    val iMM0 : t
    val iMM1 : t
    val iMM2 : t
    val iMM3 : t
    val iMM4 : t
    val iMM5 : t
    val iMM6 : t
    val iMM7 : t

    val iXMM0  : t
    val iXMM1  : t
    val iXMM2  : t
    val iXMM3  : t
    val iXMM4  : t
    val iXMM5  : t
    val iXMM6  : t
    val iXMM7  : t
    val iXMM8  : t
    val iXMM9  : t
    val iXMM10 : t
    val iXMM11 : t
    val iXMM12 : t
    val iXMM13 : t
    val iXMM14 : t
    val iXMM15 : t

    val iCF : t
    val iPF : t
    val iZF : t
    val iSF : t
    val iOF : t

  end

  module ARM : sig

    val iR00 : t
    val iR01 : t
    val iR02 : t
    val iR03 : t
    val iR04 : t
    val iR05 : t
    val iR06 : t
    val iR07 : t
    val iR08 : t
    val iR09 : t
    val iR10 : t
    val iR11 : t
    val iR12 : t
    val iLR  : t
    val iSP  : t

    val iNF  : t
    val iZF  : t
    val iCF  : t
    val iVF  : t
  end

end
