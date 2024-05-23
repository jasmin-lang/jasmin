(* ------------------------------------------------------------------------ *)
open Utils
open Wsize

module L = Location

module Name = struct
  type t = string
end

type uid = Uint63.t
let string_of_uid = Uint63.to_string

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
    let v_id = Uint63.of_int (Uniq.gen ()) in
    { v_name; v_id; v_kind; v_ty; v_dloc; v_annot }

  let clone ?dloc v =
    mk v.v_name v.v_kind v.v_ty (Option.default v.v_dloc dloc) v.v_annot

  let compare v1 v2 = Uint63.compares v1.v_id v2.v_id

  let equal v1 v2 = Uint63.equal v1.v_id v2.v_id

  let hash v = Uint63.hash v.v_id

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

  let id_name (x: t) : Name.t = x.v_name
  let id_kind (x: t) : v_kind = x.v_kind

  let spill_to_mmx (x:t) =
    match Annot.ensure_uniq1 "spill_to_mmx" Annot.none x.v_annot with
    | Some () -> true
    | None    -> false

end

(* ------------------------------------------------------------------------ *)
(* Function name                                                            *)

type funname = {
  fn_name : Name.t;
  fn_id   : uid;
}

let funname_tag (f:funname) = f.fn_id

module F = struct
  let mk fn_name =
    { fn_name; fn_id = Uint63.of_int (Uniq.gen ()); }

  type t = funname

  let compare f1 f2 = Uint63.compares f1.fn_id f2.fn_id

  let equal f1 f2 = Uint63.equal f1.fn_id f2.fn_id

  let hash f = Uint63.hash f.fn_id
end

module Sf = Set.Make (F)
module Mf = Map.Make (F)
module Hf = Hash.Make(F)
