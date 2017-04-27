open BinNums
open BinPos
open Datatypes
open Eqtype
open Gen_map
open Ssrbool

type __ = Obj.t

type stype =
| Coq_sbool
| Coq_sint
| Coq_sarr of positive
| Coq_sword

(** val positive_beq : positive -> positive -> bool **)

let rec positive_beq x y =
  match x with
  | Coq_xI x0 ->
    (match y with
     | Coq_xI x1 -> positive_beq x0 x1
     | _ -> false)
  | Coq_xO x0 ->
    (match y with
     | Coq_xO x1 -> positive_beq x0 x1
     | _ -> false)
  | Coq_xH ->
    (match y with
     | Coq_xH -> true
     | _ -> false)

(** val stype_beq : stype -> stype -> bool **)

let rec stype_beq x y =
  match x with
  | Coq_sbool ->
    (match y with
     | Coq_sbool -> true
     | _ -> false)
  | Coq_sint ->
    (match y with
     | Coq_sint -> true
     | _ -> false)
  | Coq_sarr x0 ->
    (match y with
     | Coq_sarr x1 -> positive_beq x0 x1
     | _ -> false)
  | Coq_sword ->
    (match y with
     | Coq_sword -> true
     | _ -> false)

(** val steq_axiom : stype Equality.axiom **)

let steq_axiom x y =
  iffP (stype_beq x y) (idP (stype_beq x y))

(** val stype_eqMixin : stype Equality.mixin_of **)

let stype_eqMixin =
  { Equality.op = stype_beq; Equality.mixin_of__1 = steq_axiom }

(** val stype_eqType : Equality.coq_type **)

let stype_eqType =
  Obj.magic stype_eqMixin

(** val stype_cmp : stype -> stype -> comparison **)

let stype_cmp t0 t' =
  match t0 with
  | Coq_sbool ->
    (match t' with
     | Coq_sbool -> Eq
     | _ -> Lt)
  | Coq_sint ->
    (match t' with
     | Coq_sbool -> Gt
     | Coq_sint -> Eq
     | _ -> Lt)
  | Coq_sarr n ->
    (match t' with
     | Coq_sarr n' -> Pos.compare n n'
     | _ -> Gt)
  | Coq_sword ->
    (match t' with
     | Coq_sarr _ -> Lt
     | Coq_sword -> Eq
     | _ -> Gt)

module CmpStype =
 struct
  (** val t : Equality.coq_type **)

  let t =
    Equality.clone stype_eqType (Obj.magic stype_eqMixin) (fun x -> x)

  (** val cmp : Equality.sort -> Equality.sort -> comparison **)

  let cmp =
    Obj.magic stype_cmp
 end

module CEDecStype =
 struct
  (** val t : Equality.coq_type **)

  let t =
    Equality.clone stype_eqType (Obj.magic stype_eqMixin) (fun x -> x)

  (** val pos_dec : positive -> positive -> bool **)

  let rec pos_dec p1 p2 =
    match p1 with
    | Coq_xI p1' ->
      (match p2 with
       | Coq_xI p2' -> pos_dec p1' p2'
       | _ -> false)
    | Coq_xO p1' ->
      (match p2 with
       | Coq_xO p2' -> pos_dec p1' p2'
       | _ -> false)
    | Coq_xH ->
      (match p2 with
       | Coq_xH -> true
       | _ -> false)

  (** val eq_dec : Equality.sort -> Equality.sort -> bool **)

  let eq_dec t1 t2 =
    match Obj.magic t1 with
    | Coq_sbool ->
      (match Obj.magic t2 with
       | Coq_sbool -> true
       | _ -> false)
    | Coq_sint ->
      (match Obj.magic t2 with
       | Coq_sint -> true
       | _ -> false)
    | Coq_sarr n1 ->
      (match Obj.magic t2 with
       | Coq_sarr n2 -> pos_dec n1 n2
       | _ -> false)
    | Coq_sword ->
      (match Obj.magic t2 with
       | Coq_sword -> true
       | _ -> false)
 end

module Mt = DMmake(CmpStype)(CEDecStype)
