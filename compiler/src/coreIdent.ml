(* ------------------------------------------------------------------------ *)
open Utils
open Wsize

module L = Location

module Name = struct
  type t = string
end

type uid = int
let int_of_uid i = i

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

let u8   = Bty (U U8)
let u16  = Bty (U U16)
let u32  = Bty (U U32)
let u64  = Bty (U U64)
let u128 = Bty (U U128)
let u256 = Bty (U U256)
let tu ws = Bty (U ws)
let tbool = Bty Bool
let tint  = Bty Int

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


type 'len gvar = {
  v_name : Name.t;
  v_id   : uid;
  v_kind : v_kind;
  v_ty   : 'len gty;
  v_dloc : L.t;   (* location where declared *)
  v_annot : Annotations.annotations;
}



(* ------------------------------------------------------------------------ *)
module GV = struct
  let mk v_name v_kind v_ty v_dloc v_annot =
    let v_id = Uniq.gen () in
    { v_name; v_id; v_kind; v_ty; v_dloc; v_annot }

  let clone v = mk v.v_name v.v_kind v.v_ty v.v_dloc v.v_annot

  let compare v1 v2 = v1.v_id - v2.v_id

  let equal v1 v2 = v1.v_id = v2.v_id

  let hash v = v.v_id

  let is_glob v = v.v_kind = Const

  let is_local v = not (is_glob v)
end

(* ------------------------------------------------------------------------ *)
(* Non parametrized variable                                                *)

type ty    = int gty
type var   = int gvar

module V = struct
  type t = var
  include GV
end

(* Cident *)

module Cident = struct
  type t = var

  let tag (x:t) = x.v_id

  type name = Name.t

  let id_name (x: t) : name = x.v_name

  let dummy = V.mk "" (Reg(Normal,Direct)) tbool L._dummy []

  let p__ : name = "__p__"

  let len__ : name = "__len__"

  (* FIXME: can we use something else that L._dummy? *)
  let mk x k t = V.mk (CoreConv.string_of_string0 x) k t L._dummy []
  let mk_flag x = mk x (Reg(Normal,Direct)) tbool

  module X86 = struct

    open X86_decl_core

    let mk_reg  x = mk x (Reg(Normal,Direct)) (tu x86_reg_size)
    let mk_regx x = mk x (Reg(Extra, Direct)) (tu x86_reg_size)
    let mk_xreg x = mk x (Reg(Normal,Direct)) (tu x86_xreg_size)

    let reg  x = mk_reg  (string_of_register x)
    let regx x = mk_regx (string_of_regx x)
    let xreg x = mk_xreg (string_of_xmm_register x)
    let flag x = mk_flag (string_of_rflag x)

    let iRAX = reg RAX
    let iRCX = reg RCX
    let iRDX = reg RDX
    let iRBX = reg RBX
    let iRSP = reg RSP
    let iRBP = reg RBP
    let iRSI = reg RSI
    let iRDI = reg RDI
    let iR8  = reg R8
    let iR9  = reg R9
    let iR10 = reg R10
    let iR11 = reg R11
    let iR12 = reg R12
    let iR13 = reg R13
    let iR14 = reg R14
    let iR15 = reg R15

    let iMM0 = regx MM0
    let iMM1 = regx MM1
    let iMM2 = regx MM2
    let iMM3 = regx MM3
    let iMM4 = regx MM4
    let iMM5 = regx MM5
    let iMM6 = regx MM6
    let iMM7 = regx MM7

    let iXMM0  = xreg XMM0
    let iXMM1  = xreg XMM1
    let iXMM2  = xreg XMM2
    let iXMM3  = xreg XMM3
    let iXMM4  = xreg XMM4
    let iXMM5  = xreg XMM5
    let iXMM6  = xreg XMM6
    let iXMM7  = xreg XMM7
    let iXMM8  = xreg XMM8
    let iXMM9  = xreg XMM9
    let iXMM10 = xreg XMM10
    let iXMM11 = xreg XMM11
    let iXMM12 = xreg XMM12
    let iXMM13 = xreg XMM13
    let iXMM14 = xreg XMM14
    let iXMM15 = xreg XMM15

    let iCF = flag CF
    let iPF = flag PF
    let iZF = flag ZF
    let iSF = flag SF
    let iOF = flag OF

  end

  module ARM = struct
    open Arm_decl_core

    let mk_reg  x = mk x (Reg(Normal,Direct)) (tu arm_reg_size)

    let reg  x = mk_reg  (string_of_register x)
    let flag x = mk_flag (string_of_rflag x)

    let iR00 = reg R00
    let iR01 = reg R01
    let iR02 = reg R02
    let iR03 = reg R03
    let iR04 = reg R04
    let iR05 = reg R05
    let iR06 = reg R06
    let iR07 = reg R07
    let iR08 = reg R08
    let iR09 = reg R09
    let iR10 = reg R10
    let iR11 = reg R11
    let iR12 = reg R12
    let iLR  = reg LR
    let iSP  = reg SP

    let iNF  = flag NF
    let iZF  = flag ZF
    let iCF  = flag CF
    let iVF  = flag VF
  end

end
