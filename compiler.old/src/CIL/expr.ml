open BinNums
open Datatypes
open Eqtype
open Seq
open Ssrbool
open Ssrnat
open Utils0
open Var0

type sop2 =
| Oand
| Oor
| Oadd
| Omul
| Osub
| Oeq
| Oneq
| Olt
| Ole
| Ogt
| Oge

type sopn =
| Olnot
| Oxor
| Oland
| Olor
| Olsr
| Olsl
| Oif
| Omulu
| Omuli
| Oaddcarry
| Osubcarry

(** val sop2_beq : sop2 -> sop2 -> bool **)

let rec sop2_beq x y =
  match x with
  | Oand ->
    (match y with
     | Oand -> true
     | _ -> false)
  | Oor ->
    (match y with
     | Oor -> true
     | _ -> false)
  | Oadd ->
    (match y with
     | Oadd -> true
     | _ -> false)
  | Omul ->
    (match y with
     | Omul -> true
     | _ -> false)
  | Osub ->
    (match y with
     | Osub -> true
     | _ -> false)
  | Oeq ->
    (match y with
     | Oeq -> true
     | _ -> false)
  | Oneq ->
    (match y with
     | Oneq -> true
     | _ -> false)
  | Olt ->
    (match y with
     | Olt -> true
     | _ -> false)
  | Ole ->
    (match y with
     | Ole -> true
     | _ -> false)
  | Ogt ->
    (match y with
     | Ogt -> true
     | _ -> false)
  | Oge ->
    (match y with
     | Oge -> true
     | _ -> false)

(** val sop2_eq_axiom : sop2 Equality.axiom **)

let sop2_eq_axiom x y =
  iffP (sop2_beq x y) (idP (sop2_beq x y))

(** val sop2_eqMixin : sop2 Equality.mixin_of **)

let sop2_eqMixin =
  { Equality.op = sop2_beq; Equality.mixin_of__1 = sop2_eq_axiom }

(** val sop2_eqType : Equality.coq_type **)

let sop2_eqType =
  Obj.magic sop2_eqMixin

(** val sopn_beq : sopn -> sopn -> bool **)

let rec sopn_beq x y =
  match x with
  | Olnot ->
    (match y with
     | Olnot -> true
     | _ -> false)
  | Oxor ->
    (match y with
     | Oxor -> true
     | _ -> false)
  | Oland ->
    (match y with
     | Oland -> true
     | _ -> false)
  | Olor ->
    (match y with
     | Olor -> true
     | _ -> false)
  | Olsr ->
    (match y with
     | Olsr -> true
     | _ -> false)
  | Olsl ->
    (match y with
     | Olsl -> true
     | _ -> false)
  | Oif ->
    (match y with
     | Oif -> true
     | _ -> false)
  | Omulu ->
    (match y with
     | Omulu -> true
     | _ -> false)
  | Omuli ->
    (match y with
     | Omuli -> true
     | _ -> false)
  | Oaddcarry ->
    (match y with
     | Oaddcarry -> true
     | _ -> false)
  | Osubcarry ->
    (match y with
     | Osubcarry -> true
     | _ -> false)

(** val sopn_eq_axiom : sopn Equality.axiom **)

let sopn_eq_axiom x y =
  iffP (sopn_beq x y) (idP (sopn_beq x y))

(** val sopn_eqMixin : sopn Equality.mixin_of **)

let sopn_eqMixin =
  { Equality.op = sopn_beq; Equality.mixin_of__1 = sopn_eq_axiom }

(** val sopn_eqType : Equality.coq_type **)

let sopn_eqType =
  Obj.magic sopn_eqMixin

type var_info = positive

type var_i = { v_var : Var.var; v_info : var_info }

(** val v_var : var_i -> Var.var **)

let v_var x = x.v_var

type pexpr =
| Pconst of coq_Z
| Pbool of bool
| Pcast of pexpr
| Pvar of var_i
| Pget of var_i * pexpr
| Pload of var_i * pexpr
| Pnot of pexpr
| Papp2 of sop2 * pexpr * pexpr

(** val var_i_beq : var_i -> var_i -> bool **)

let var_i_beq x1 x2 =
  let { v_var = x3; v_info = i1 } = x1 in
  let { v_var = x4; v_info = i2 } = x2 in
  (&&) (eq_op Var.var_eqType (Obj.magic x3) (Obj.magic x4))
    (eq_op pos_eqType (Obj.magic i1) (Obj.magic i2))

(** val var_i_eq_axiom : var_i Equality.axiom **)

let var_i_eq_axiom _top_assumption_ =
  let _evar_0_ = fun x xi _top_assumption_0 ->
    let _evar_0_ = fun y yi ->
      equivP ((&&) (eq_op Var.var_eqType x y) (eq_op pos_eqType xi yi))
        (andP (eq_op Var.var_eqType x y) (eq_op pos_eqType xi yi))
    in
    let { v_var = x0; v_info = x1 } = _top_assumption_0 in
    Obj.magic _evar_0_ x0 x1
  in
  let { v_var = x; v_info = x0 } = _top_assumption_ in
  Obj.magic _evar_0_ x x0

(** val var_i_eqMixin : var_i Equality.mixin_of **)

let var_i_eqMixin =
  { Equality.op = var_i_beq; Equality.mixin_of__1 = var_i_eq_axiom }

(** val var_i_eqType : Equality.coq_type **)

let var_i_eqType =
  Obj.magic var_i_eqMixin

module Eq_pexpr =
 struct
  (** val eqb : pexpr -> pexpr -> bool **)

  let rec eqb e1 e2 =
    match e1 with
    | Pconst n1 ->
      (match e2 with
       | Pconst n2 -> eq_op coq_Z_eqType (Obj.magic n1) (Obj.magic n2)
       | _ -> false)
    | Pbool b1 ->
      (match e2 with
       | Pbool b2 -> eq_op bool_eqType (Obj.magic b1) (Obj.magic b2)
       | _ -> false)
    | Pcast e3 ->
      (match e2 with
       | Pcast e4 -> eqb e3 e4
       | _ -> false)
    | Pvar x1 ->
      (match e2 with
       | Pvar x2 -> eq_op var_i_eqType (Obj.magic x1) (Obj.magic x2)
       | _ -> false)
    | Pget (x1, e3) ->
      (match e2 with
       | Pget (x2, e4) ->
         (&&) (eq_op var_i_eqType (Obj.magic x1) (Obj.magic x2)) (eqb e3 e4)
       | _ -> false)
    | Pload (x1, e3) ->
      (match e2 with
       | Pload (x2, e4) ->
         (&&) (eq_op var_i_eqType (Obj.magic x1) (Obj.magic x2)) (eqb e3 e4)
       | _ -> false)
    | Pnot e3 ->
      (match e2 with
       | Pnot e4 -> eqb e3 e4
       | _ -> false)
    | Papp2 (o1, e11, e12) ->
      (match e2 with
       | Papp2 (o2, e21, e22) ->
         (&&)
           ((&&) (eq_op sop2_eqType (Obj.magic o1) (Obj.magic o2))
             (eqb e11 e21)) (eqb e12 e22)
       | _ -> false)

  (** val eq_axiom : pexpr Equality.axiom **)

  let eq_axiom _top_assumption_ =
    let _evar_0_ = fun n1 _top_assumption_0 ->
      let _evar_0_ = fun n2 ->
        equivP (eq_op coq_Z_eqType n1 n2) (eqP coq_Z_eqType n1 n2)
      in
      let _evar_0_0 = fun _ -> ReflectF in
      let _evar_0_1 = fun _ -> ReflectF in
      let _evar_0_2 = fun _ -> ReflectF in
      let _evar_0_3 = fun _ _ -> ReflectF in
      let _evar_0_4 = fun _ _ -> ReflectF in
      let _evar_0_5 = fun _ -> ReflectF in
      let _evar_0_6 = fun _ _ _ -> ReflectF in
      (match _top_assumption_0 with
       | Pconst x -> Obj.magic _evar_0_ x
       | Pbool x -> _evar_0_0 x
       | Pcast x -> _evar_0_1 x
       | Pvar x -> _evar_0_2 x
       | Pget (x, x0) -> _evar_0_3 x x0
       | Pload (x, x0) -> _evar_0_4 x x0
       | Pnot x -> _evar_0_5 x
       | Papp2 (x, x0, x1) -> _evar_0_6 x x0 x1)
    in
    let _evar_0_0 = fun b1 _top_assumption_0 ->
      let _evar_0_0 = fun _ -> ReflectF in
      let _evar_0_1 = fun b2 ->
        equivP (eq_op bool_eqType b1 b2) (eqP bool_eqType b1 b2)
      in
      let _evar_0_2 = fun _ -> ReflectF in
      let _evar_0_3 = fun _ -> ReflectF in
      let _evar_0_4 = fun _ _ -> ReflectF in
      let _evar_0_5 = fun _ _ -> ReflectF in
      let _evar_0_6 = fun _ -> ReflectF in
      let _evar_0_7 = fun _ _ _ -> ReflectF in
      (match _top_assumption_0 with
       | Pconst x -> _evar_0_0 x
       | Pbool x -> Obj.magic _evar_0_1 x
       | Pcast x -> _evar_0_2 x
       | Pvar x -> _evar_0_3 x
       | Pget (x, x0) -> _evar_0_4 x x0
       | Pload (x, x0) -> _evar_0_5 x x0
       | Pnot x -> _evar_0_6 x
       | Papp2 (x, x0, x1) -> _evar_0_7 x x0 x1)
    in
    let _evar_0_1 = fun e1 he1 _top_assumption_0 ->
      let _evar_0_1 = fun _ -> ReflectF in
      let _evar_0_2 = fun _ -> ReflectF in
      let _evar_0_3 = fun e2 -> equivP (eqb e1 e2) (he1 e2) in
      let _evar_0_4 = fun _ -> ReflectF in
      let _evar_0_5 = fun _ _ -> ReflectF in
      let _evar_0_6 = fun _ _ -> ReflectF in
      let _evar_0_7 = fun _ -> ReflectF in
      let _evar_0_8 = fun _ _ _ -> ReflectF in
      (match _top_assumption_0 with
       | Pconst x -> _evar_0_1 x
       | Pbool x -> _evar_0_2 x
       | Pcast x -> _evar_0_3 x
       | Pvar x -> _evar_0_4 x
       | Pget (x, x0) -> _evar_0_5 x x0
       | Pload (x, x0) -> _evar_0_6 x x0
       | Pnot x -> _evar_0_7 x
       | Papp2 (x, x0, x1) -> _evar_0_8 x x0 x1)
    in
    let _evar_0_2 = fun x1 _top_assumption_0 ->
      let _evar_0_2 = fun _ -> ReflectF in
      let _evar_0_3 = fun _ -> ReflectF in
      let _evar_0_4 = fun _ -> ReflectF in
      let _evar_0_5 = fun x2 ->
        equivP (eq_op var_i_eqType x1 x2) (eqP var_i_eqType x1 x2)
      in
      let _evar_0_6 = fun _ _ -> ReflectF in
      let _evar_0_7 = fun _ _ -> ReflectF in
      let _evar_0_8 = fun _ -> ReflectF in
      let _evar_0_9 = fun _ _ _ -> ReflectF in
      (match _top_assumption_0 with
       | Pconst x -> _evar_0_2 x
       | Pbool x -> _evar_0_3 x
       | Pcast x -> _evar_0_4 x
       | Pvar x -> Obj.magic _evar_0_5 x
       | Pget (x, x0) -> _evar_0_6 x x0
       | Pload (x, x0) -> _evar_0_7 x x0
       | Pnot x -> _evar_0_8 x
       | Papp2 (x, x0, x2) -> _evar_0_9 x x0 x2)
    in
    let _evar_0_3 = fun x1 e1 _ _top_assumption_0 ->
      let _evar_0_3 = fun _ -> ReflectF in
      let _evar_0_4 = fun _ -> ReflectF in
      let _evar_0_5 = fun _ -> ReflectF in
      let _evar_0_6 = fun _ -> ReflectF in
      let _evar_0_7 = fun x2 e2 ->
        equivP ((&&) (eq_op var_i_eqType x1 x2) (eqb e1 e2))
          (andP (eq_op var_i_eqType x1 x2) (eqb e1 e2))
      in
      let _evar_0_8 = fun _ _ -> ReflectF in
      let _evar_0_9 = fun _ -> ReflectF in
      let _evar_0_10 = fun _ _ _ -> ReflectF in
      (match _top_assumption_0 with
       | Pconst x -> _evar_0_3 x
       | Pbool x -> _evar_0_4 x
       | Pcast x -> _evar_0_5 x
       | Pvar x -> _evar_0_6 x
       | Pget (x, x0) -> Obj.magic _evar_0_7 x x0
       | Pload (x, x0) -> _evar_0_8 x x0
       | Pnot x -> _evar_0_9 x
       | Papp2 (x, x0, x2) -> _evar_0_10 x x0 x2)
    in
    let _evar_0_4 = fun x1 e1 _ _top_assumption_0 ->
      let _evar_0_4 = fun _ -> ReflectF in
      let _evar_0_5 = fun _ -> ReflectF in
      let _evar_0_6 = fun _ -> ReflectF in
      let _evar_0_7 = fun _ -> ReflectF in
      let _evar_0_8 = fun _ _ -> ReflectF in
      let _evar_0_9 = fun x2 e2 ->
        equivP ((&&) (eq_op var_i_eqType x1 x2) (eqb e1 e2))
          (andP (eq_op var_i_eqType x1 x2) (eqb e1 e2))
      in
      let _evar_0_10 = fun _ -> ReflectF in
      let _evar_0_11 = fun _ _ _ -> ReflectF in
      (match _top_assumption_0 with
       | Pconst x -> _evar_0_4 x
       | Pbool x -> _evar_0_5 x
       | Pcast x -> _evar_0_6 x
       | Pvar x -> _evar_0_7 x
       | Pget (x, x0) -> _evar_0_8 x x0
       | Pload (x, x0) -> Obj.magic _evar_0_9 x x0
       | Pnot x -> _evar_0_10 x
       | Papp2 (x, x0, x2) -> _evar_0_11 x x0 x2)
    in
    let _evar_0_5 = fun e1 he1 _top_assumption_0 ->
      let _evar_0_5 = fun _ -> ReflectF in
      let _evar_0_6 = fun _ -> ReflectF in
      let _evar_0_7 = fun _ -> ReflectF in
      let _evar_0_8 = fun _ -> ReflectF in
      let _evar_0_9 = fun _ _ -> ReflectF in
      let _evar_0_10 = fun _ _ -> ReflectF in
      let _evar_0_11 = fun e2 -> equivP (eqb e1 e2) (he1 e2) in
      let _evar_0_12 = fun _ _ _ -> ReflectF in
      (match _top_assumption_0 with
       | Pconst x -> _evar_0_5 x
       | Pbool x -> _evar_0_6 x
       | Pcast x -> _evar_0_7 x
       | Pvar x -> _evar_0_8 x
       | Pget (x, x0) -> _evar_0_9 x x0
       | Pload (x, x0) -> _evar_0_10 x x0
       | Pnot x -> _evar_0_11 x
       | Papp2 (x, x0, x1) -> _evar_0_12 x x0 x1)
    in
    let _evar_0_6 = fun o1 e11 _ e12 _ _top_assumption_0 ->
      let _evar_0_6 = fun _ -> ReflectF in
      let _evar_0_7 = fun _ -> ReflectF in
      let _evar_0_8 = fun _ -> ReflectF in
      let _evar_0_9 = fun _ -> ReflectF in
      let _evar_0_10 = fun _ _ -> ReflectF in
      let _evar_0_11 = fun _ _ -> ReflectF in
      let _evar_0_12 = fun _ -> ReflectF in
      let _evar_0_13 = fun o2 e21 e22 ->
        equivP
          ((&&) ((&&) (eq_op sop2_eqType o1 o2) (eqb e11 e21)) (eqb e12 e22))
          (andP ((&&) (eq_op sop2_eqType o1 o2) (eqb e11 e21)) (eqb e12 e22))
      in
      (match _top_assumption_0 with
       | Pconst x -> _evar_0_6 x
       | Pbool x -> _evar_0_7 x
       | Pcast x -> _evar_0_8 x
       | Pvar x -> _evar_0_9 x
       | Pget (x, x0) -> _evar_0_10 x x0
       | Pload (x, x0) -> _evar_0_11 x x0
       | Pnot x -> _evar_0_12 x
       | Papp2 (x, x0, x1) -> Obj.magic _evar_0_13 x x0 x1)
    in
    let rec f = function
    | Pconst z -> Obj.magic _evar_0_ z
    | Pbool b -> Obj.magic _evar_0_0 b
    | Pcast p0 -> _evar_0_1 p0 (f p0)
    | Pvar v -> Obj.magic _evar_0_2 v
    | Pget (v, p0) -> Obj.magic _evar_0_3 v p0 (f p0)
    | Pload (v, p0) -> Obj.magic _evar_0_4 v p0 (f p0)
    | Pnot p0 -> _evar_0_5 p0 (f p0)
    | Papp2 (s, p0, p1) -> Obj.magic _evar_0_6 s p0 (f p0) p1 (f p1)
    in f _top_assumption_

  (** val eqMixin : pexpr Equality.mixin_of **)

  let eqMixin =
    { Equality.op = eqb; Equality.mixin_of__1 = eq_axiom }

  module Exports =
   struct
    (** val eqType : Equality.coq_type **)

    let eqType =
      Obj.magic eqMixin
   end
 end

type lval =
| Lnone of var_info
| Lvar of var_i
| Lmem of var_i * pexpr
| Laset of var_i * pexpr

(** val lval_beq : lval -> lval -> bool **)

let lval_beq x1 x2 =
  match x1 with
  | Lnone i1 ->
    (match x2 with
     | Lnone i2 -> eq_op pos_eqType (Obj.magic i1) (Obj.magic i2)
     | _ -> false)
  | Lvar x3 ->
    (match x2 with
     | Lvar x4 -> eq_op var_i_eqType (Obj.magic x3) (Obj.magic x4)
     | _ -> false)
  | Lmem (x3, e1) ->
    (match x2 with
     | Lmem (x4, e2) ->
       (&&) (eq_op var_i_eqType (Obj.magic x3) (Obj.magic x4))
         (eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2))
     | _ -> false)
  | Laset (x3, e1) ->
    (match x2 with
     | Laset (x4, e2) ->
       (&&) (eq_op var_i_eqType (Obj.magic x3) (Obj.magic x4))
         (eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2))
     | _ -> false)

(** val lval_eq_axiom : lval Equality.axiom **)

let lval_eq_axiom _top_assumption_ =
  let _evar_0_ = fun i1 _top_assumption_0 ->
    let _evar_0_ = fun i2 ->
      equivP (eq_op pos_eqType i1 i2) (eqP pos_eqType i1 i2)
    in
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun _ _ -> ReflectF in
    let _evar_0_2 = fun _ _ -> ReflectF in
    (match _top_assumption_0 with
     | Lnone x -> Obj.magic _evar_0_ x
     | Lvar x -> _evar_0_0 x
     | Lmem (x, x0) -> _evar_0_1 x x0
     | Laset (x, x0) -> _evar_0_2 x x0)
  in
  let _evar_0_0 = fun x1 _top_assumption_0 ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = fun x2 ->
      equivP (eq_op var_i_eqType x1 x2) (eqP var_i_eqType x1 x2)
    in
    let _evar_0_2 = fun _ _ -> ReflectF in
    let _evar_0_3 = fun _ _ -> ReflectF in
    (match _top_assumption_0 with
     | Lnone x -> _evar_0_0 x
     | Lvar x -> Obj.magic _evar_0_1 x
     | Lmem (x, x0) -> _evar_0_2 x x0
     | Laset (x, x0) -> _evar_0_3 x x0)
  in
  let _evar_0_1 = fun x1 e1 _top_assumption_0 ->
    let _evar_0_1 = fun _ -> ReflectF in
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun x2 e2 ->
      equivP
        ((&&) (eq_op var_i_eqType x1 x2)
          (eq_op Eq_pexpr.Exports.eqType e1 e2))
        (andP (eq_op var_i_eqType x1 x2)
          (eq_op Eq_pexpr.Exports.eqType e1 e2))
    in
    let _evar_0_4 = fun _ _ -> ReflectF in
    (match _top_assumption_0 with
     | Lnone x -> _evar_0_1 x
     | Lvar x -> _evar_0_2 x
     | Lmem (x, x0) -> Obj.magic _evar_0_3 x x0
     | Laset (x, x0) -> _evar_0_4 x x0)
  in
  let _evar_0_2 = fun x1 e1 _top_assumption_0 ->
    let _evar_0_2 = fun _ -> ReflectF in
    let _evar_0_3 = fun _ -> ReflectF in
    let _evar_0_4 = fun _ _ -> ReflectF in
    let _evar_0_5 = fun x2 e2 ->
      equivP
        ((&&) (eq_op var_i_eqType x1 x2)
          (eq_op Eq_pexpr.Exports.eqType e1 e2))
        (andP (eq_op var_i_eqType x1 x2)
          (eq_op Eq_pexpr.Exports.eqType e1 e2))
    in
    (match _top_assumption_0 with
     | Lnone x -> _evar_0_2 x
     | Lvar x -> _evar_0_3 x
     | Lmem (x, x0) -> _evar_0_4 x x0
     | Laset (x, x0) -> Obj.magic _evar_0_5 x x0)
  in
  (match _top_assumption_ with
   | Lnone x -> Obj.magic _evar_0_ x
   | Lvar x -> Obj.magic _evar_0_0 x
   | Lmem (x, x0) -> Obj.magic _evar_0_1 x x0
   | Laset (x, x0) -> Obj.magic _evar_0_2 x x0)

(** val lval_eqMixin : lval Equality.mixin_of **)

let lval_eqMixin =
  { Equality.op = lval_beq; Equality.mixin_of__1 = lval_eq_axiom }

(** val lval_eqType : Equality.coq_type **)

let lval_eqType =
  Obj.magic lval_eqMixin

type dir =
| UpTo
| DownTo

(** val dir_beq : dir -> dir -> bool **)

let rec dir_beq x y =
  match x with
  | UpTo ->
    (match y with
     | UpTo -> true
     | DownTo -> false)
  | DownTo ->
    (match y with
     | UpTo -> false
     | DownTo -> true)

(** val dir_eq_axiom : dir Equality.axiom **)

let dir_eq_axiom x y =
  iffP (dir_beq x y) (idP (dir_beq x y))

(** val dir_eqMixin : dir Equality.mixin_of **)

let dir_eqMixin =
  { Equality.op = dir_beq; Equality.mixin_of__1 = dir_eq_axiom }

(** val dir_eqType : Equality.coq_type **)

let dir_eqType =
  Obj.magic dir_eqMixin

type range = (dir * pexpr) * pexpr

type instr_info = positive

(** val dummy_iinfo : positive **)

let dummy_iinfo =
  Coq_xH

type assgn_tag =
| AT_keep
| AT_rename
| AT_inline

(** val assgn_tag_beq : assgn_tag -> assgn_tag -> bool **)

let rec assgn_tag_beq x y =
  match x with
  | AT_keep ->
    (match y with
     | AT_keep -> true
     | _ -> false)
  | AT_rename ->
    (match y with
     | AT_rename -> true
     | _ -> false)
  | AT_inline ->
    (match y with
     | AT_inline -> true
     | _ -> false)

(** val assgn_tag_eq_axiom : assgn_tag Equality.axiom **)

let assgn_tag_eq_axiom x y =
  iffP (assgn_tag_beq x y) (idP (assgn_tag_beq x y))

(** val assgn_tag_eqMixin : assgn_tag Equality.mixin_of **)

let assgn_tag_eqMixin =
  { Equality.op = assgn_tag_beq; Equality.mixin_of__1 = assgn_tag_eq_axiom }

(** val assgn_tag_eqType : Equality.coq_type **)

let assgn_tag_eqType =
  Obj.magic assgn_tag_eqMixin

type funname = positive

type inline_info =
| InlineFun
| DoNotInline

(** val inline_info_beq : inline_info -> inline_info -> bool **)

let rec inline_info_beq x y =
  match x with
  | InlineFun ->
    (match y with
     | InlineFun -> true
     | DoNotInline -> false)
  | DoNotInline ->
    (match y with
     | InlineFun -> false
     | DoNotInline -> true)

(** val inline_info_eq_axiom : inline_info Equality.axiom **)

let inline_info_eq_axiom x y =
  iffP (inline_info_beq x y) (idP (inline_info_beq x y))

(** val inline_info_eqMixin : inline_info Equality.mixin_of **)

let inline_info_eqMixin =
  { Equality.op = inline_info_beq; Equality.mixin_of__1 =
    inline_info_eq_axiom }

(** val inline_info_eqType : Equality.coq_type **)

let inline_info_eqType =
  Obj.magic inline_info_eqMixin

type instr_r =
| Cassgn of lval * assgn_tag * pexpr
| Copn of lval list * sopn * pexpr list
| Cif of pexpr * instr list * instr list
| Cfor of var_i * range * instr list
| Cwhile of pexpr * instr list
| Ccall of inline_info * lval list * funname * pexpr list
and instr =
| MkI of instr_info * instr_r

type fundef = { f_iinfo : instr_info; f_params : var_i list;
                f_body : instr list; f_res : var_i list }

(** val f_iinfo : fundef -> instr_info **)

let f_iinfo x = x.f_iinfo

(** val f_params : fundef -> var_i list **)

let f_params x = x.f_params

(** val f_body : fundef -> instr list **)

let f_body x = x.f_body

(** val f_res : fundef -> var_i list **)

let f_res x = x.f_res

type prog = (funname * fundef) list

(** val dummy_fundef : fundef **)

let dummy_fundef =
  { f_iinfo = dummy_iinfo; f_params = []; f_body = []; f_res = [] }

(** val instr_r_beq : instr_r -> instr_r -> bool **)

let rec instr_r_beq i1 i2 =
  match i1 with
  | Cassgn (x1, tag1, e1) ->
    (match i2 with
     | Cassgn (x2, tag2, e2) ->
       (&&)
         ((&&) (eq_op assgn_tag_eqType (Obj.magic tag1) (Obj.magic tag2))
           (eq_op lval_eqType (Obj.magic x1) (Obj.magic x2)))
         (eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2))
     | _ -> false)
  | Copn (x1, o1, e1) ->
    (match i2 with
     | Copn (x2, o2, e2) ->
       (&&)
         ((&&) (eq_op (seq_eqType lval_eqType) (Obj.magic x1) (Obj.magic x2))
           (eq_op sopn_eqType (Obj.magic o1) (Obj.magic o2)))
         (eq_op (seq_eqType Eq_pexpr.Exports.eqType) (Obj.magic e1)
           (Obj.magic e2))
     | _ -> false)
  | Cif (e1, c11, c12) ->
    (match i2 with
     | Cif (e2, c21, c22) ->
       (&&)
         ((&&) (eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2))
           (all2 instr_beq c11 c21)) (all2 instr_beq c12 c22)
     | _ -> false)
  | Cfor (i3, r, c1) ->
    let (p, hi1) = r in
    let (dir1, lo1) = p in
    (match i2 with
     | Cfor (i4, r0, c2) ->
       let (p0, hi2) = r0 in
       let (dir2, lo2) = p0 in
       (&&)
         ((&&)
           ((&&)
             ((&&) (eq_op var_i_eqType (Obj.magic i3) (Obj.magic i4))
               (eq_op dir_eqType (Obj.magic dir1) (Obj.magic dir2)))
             (eq_op Eq_pexpr.Exports.eqType (Obj.magic lo1) (Obj.magic lo2)))
           (eq_op Eq_pexpr.Exports.eqType (Obj.magic hi1) (Obj.magic hi2)))
         (all2 instr_beq c1 c2)
     | _ -> false)
  | Cwhile (e1, c1) ->
    (match i2 with
     | Cwhile (e2, c2) ->
       (&&) (eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2))
         (all2 instr_beq c1 c2)
     | _ -> false)
  | Ccall (ii1, x1, f1, arg1) ->
    (match i2 with
     | Ccall (ii2, x2, f2, arg2) ->
       (&&)
         ((&&)
           ((&&) (eq_op inline_info_eqType (Obj.magic ii1) (Obj.magic ii2))
             (eq_op (seq_eqType lval_eqType) (Obj.magic x1) (Obj.magic x2)))
           (eq_op pos_eqType (Obj.magic f1) (Obj.magic f2)))
         (eq_op (seq_eqType Eq_pexpr.Exports.eqType) (Obj.magic arg1)
           (Obj.magic arg2))
     | _ -> false)

(** val instr_beq : instr -> instr -> bool **)

and instr_beq i1 i2 =
  let MkI (if1, i3) = i1 in
  let MkI (if2, i4) = i2 in
  (&&) (eq_op pos_eqType (Obj.magic if1) (Obj.magic if2)) (instr_r_beq i3 i4)

(** val instr_eq_axiom_ :
    (instr_r -> instr_r -> reflect) -> instr Equality.axiom **)

let instr_eq_axiom_ _ _top_assumption_ =
  let _evar_0_ = fun ii1 ir1 _top_assumption_0 ->
    let _evar_0_ = fun ii2 ir2 ->
      equivP
        (instr_beq (MkI ((Obj.magic ii1), ir1)) (MkI ((Obj.magic ii2), ir2)))
        (andP (eq_op pos_eqType ii1 ii2) (instr_r_beq ir1 ir2))
    in
    let MkI (x, x0) = _top_assumption_0 in Obj.magic _evar_0_ x x0
  in
  let MkI (x, x0) = _top_assumption_ in Obj.magic _evar_0_ x x0

(** val instr_r_eq_axiom : instr_r Equality.axiom **)

let instr_r_eq_axiom _top_assumption_ =
  let _evar_0_ = fun x1 t1 e1 _top_assumption_0 ->
    let _evar_0_ = fun x2 t2 e2 ->
      equivP
        ((&&) ((&&) (eq_op assgn_tag_eqType t1 t2) (eq_op lval_eqType x1 x2))
          (eq_op Eq_pexpr.Exports.eqType e1 e2))
        (idP
          ((&&)
            ((&&) (eq_op assgn_tag_eqType t1 t2) (eq_op lval_eqType x1 x2))
            (eq_op Eq_pexpr.Exports.eqType e1 e2)))
    in
    let _evar_0_0 = fun _ _ _ -> ReflectF in
    let _evar_0_1 = fun _ _ _ -> ReflectF in
    let _evar_0_2 = fun _ _top_assumption_1 ->
      let _evar_0_2 = fun _top_assumption_2 ->
        let _evar_0_2 = fun _ _ _ _ -> ReflectF in
        let (x, x0) = _top_assumption_2 in _evar_0_2 x x0
      in
      let (x, x0) = _top_assumption_1 in _evar_0_2 x x0
    in
    let _evar_0_3 = fun _ _ -> ReflectF in
    let _evar_0_4 = fun _ _ _ _ -> ReflectF in
    (match _top_assumption_0 with
     | Cassgn (x, x0, x2) -> Obj.magic _evar_0_ x x0 x2
     | Copn (x, x0, x2) -> _evar_0_0 x x0 x2
     | Cif (x, x0, x2) -> _evar_0_1 x x0 x2
     | Cfor (x, x0, x2) -> _evar_0_2 x x0 x2
     | Cwhile (x, x0) -> _evar_0_3 x x0
     | Ccall (x, x0, x2, x3) -> _evar_0_4 x x0 x2 x3)
  in
  let _evar_0_0 = fun x1 o1 e1 _top_assumption_0 ->
    let _evar_0_0 = fun _ _ _ -> ReflectF in
    let _evar_0_1 = fun x2 o2 e2 ->
      equivP
        ((&&)
          ((&&) (eq_op (seq_eqType lval_eqType) x1 x2)
            (eq_op sopn_eqType o1 o2))
          (eq_op (seq_eqType Eq_pexpr.Exports.eqType) e1 e2))
        (idP
          ((&&)
            ((&&) (eq_op (seq_eqType lval_eqType) x1 x2)
              (eq_op sopn_eqType o1 o2))
            (eq_op (seq_eqType Eq_pexpr.Exports.eqType) e1 e2)))
    in
    let _evar_0_2 = fun _ _ _ -> ReflectF in
    let _evar_0_3 = fun _ _top_assumption_1 ->
      let _evar_0_3 = fun _top_assumption_2 ->
        let _evar_0_3 = fun _ _ _ _ -> ReflectF in
        let (x, x0) = _top_assumption_2 in _evar_0_3 x x0
      in
      let (x, x0) = _top_assumption_1 in _evar_0_3 x x0
    in
    let _evar_0_4 = fun _ _ -> ReflectF in
    let _evar_0_5 = fun _ _ _ _ -> ReflectF in
    (match _top_assumption_0 with
     | Cassgn (x, x0, x2) -> _evar_0_0 x x0 x2
     | Copn (x, x0, x2) -> Obj.magic _evar_0_1 x x0 x2
     | Cif (x, x0, x2) -> _evar_0_2 x x0 x2
     | Cfor (x, x0, x2) -> _evar_0_3 x x0 x2
     | Cwhile (x, x0) -> _evar_0_4 x x0
     | Ccall (x, x0, x2, x3) -> _evar_0_5 x x0 x2 x3)
  in
  let _evar_0_1 = fun e1 c11 c12 _top_assumption_0 ->
    let _evar_0_1 = fun _ _ _ -> ReflectF in
    let _evar_0_2 = fun _ _ _ -> ReflectF in
    let _evar_0_3 = fun e2 c21 c22 ->
      equivP
        ((&&)
          ((&&) (eq_op Eq_pexpr.Exports.eqType e1 e2)
            (all2 instr_beq c11 c21)) (all2 instr_beq c12 c22))
        (idP
          ((&&)
            ((&&) (eq_op Eq_pexpr.Exports.eqType e1 e2)
              (all2 instr_beq c11 c21)) (all2 instr_beq c12 c22)))
    in
    let _evar_0_4 = fun _ _top_assumption_1 ->
      let _evar_0_4 = fun _top_assumption_2 ->
        let _evar_0_4 = fun _ _ _ _ -> ReflectF in
        let (x, x0) = _top_assumption_2 in _evar_0_4 x x0
      in
      let (x, x0) = _top_assumption_1 in _evar_0_4 x x0
    in
    let _evar_0_5 = fun _ _ -> ReflectF in
    let _evar_0_6 = fun _ _ _ _ -> ReflectF in
    (match _top_assumption_0 with
     | Cassgn (x, x0, x1) -> _evar_0_1 x x0 x1
     | Copn (x, x0, x1) -> _evar_0_2 x x0 x1
     | Cif (x, x0, x1) -> Obj.magic _evar_0_3 x x0 x1
     | Cfor (x, x0, x1) -> _evar_0_4 x x0 x1
     | Cwhile (x, x0) -> _evar_0_5 x x0
     | Ccall (x, x0, x1, x2) -> _evar_0_6 x x0 x1 x2)
  in
  let _evar_0_2 = fun x1 _top_assumption_0 ->
    let _evar_0_2 = fun _top_assumption_1 ->
      let _evar_0_2 = fun dir1 lo1 hi1 c1 _top_assumption_2 ->
        let _evar_0_2 = fun _ _ _ -> ReflectF in
        let _evar_0_3 = fun _ _ _ -> ReflectF in
        let _evar_0_4 = fun _ _ _ -> ReflectF in
        let _evar_0_5 = fun x2 _top_assumption_3 ->
          let _evar_0_5 = fun _top_assumption_4 ->
            let _evar_0_5 = fun dir2 lo2 hi2 c2 ->
              equivP
                ((&&)
                  ((&&)
                    ((&&)
                      ((&&) (eq_op var_i_eqType x1 x2)
                        (eq_op dir_eqType dir1 dir2))
                      (eq_op Eq_pexpr.Exports.eqType lo1 lo2))
                    (eq_op Eq_pexpr.Exports.eqType hi1 hi2))
                  (all2 instr_beq c1 c2))
                (idP
                  ((&&)
                    ((&&)
                      ((&&)
                        ((&&) (eq_op var_i_eqType x1 x2)
                          (eq_op dir_eqType dir1 dir2))
                        (eq_op Eq_pexpr.Exports.eqType lo1 lo2))
                      (eq_op Eq_pexpr.Exports.eqType hi1 hi2))
                    (all2 instr_beq c1 c2)))
            in
            let (x, x0) = _top_assumption_4 in _evar_0_5 x x0
          in
          let (x, x0) = _top_assumption_3 in _evar_0_5 x x0
        in
        let _evar_0_6 = fun _ _ -> ReflectF in
        let _evar_0_7 = fun _ _ _ _ -> ReflectF in
        (match _top_assumption_2 with
         | Cassgn (x, x0, x2) -> _evar_0_2 x x0 x2
         | Copn (x, x0, x2) -> _evar_0_3 x x0 x2
         | Cif (x, x0, x2) -> _evar_0_4 x x0 x2
         | Cfor (x, x0, x2) -> Obj.magic _evar_0_5 x x0 x2
         | Cwhile (x, x0) -> _evar_0_6 x x0
         | Ccall (x, x0, x2, x3) -> _evar_0_7 x x0 x2 x3)
      in
      let (x, x0) = _top_assumption_1 in _evar_0_2 x x0
    in
    let (x, x0) = _top_assumption_0 in _evar_0_2 x x0
  in
  let _evar_0_3 = fun e1 c1 _top_assumption_0 ->
    let _evar_0_3 = fun _ _ _ -> ReflectF in
    let _evar_0_4 = fun _ _ _ -> ReflectF in
    let _evar_0_5 = fun _ _ _ -> ReflectF in
    let _evar_0_6 = fun _ _top_assumption_1 ->
      let _evar_0_6 = fun _top_assumption_2 ->
        let _evar_0_6 = fun _ _ _ _ -> ReflectF in
        let (x, x0) = _top_assumption_2 in _evar_0_6 x x0
      in
      let (x, x0) = _top_assumption_1 in _evar_0_6 x x0
    in
    let _evar_0_7 = fun e2 c2 ->
      equivP
        ((&&) (eq_op Eq_pexpr.Exports.eqType e1 e2) (all2 instr_beq c1 c2))
        (idP
          ((&&) (eq_op Eq_pexpr.Exports.eqType e1 e2) (all2 instr_beq c1 c2)))
    in
    let _evar_0_8 = fun _ _ _ _ -> ReflectF in
    (match _top_assumption_0 with
     | Cassgn (x, x0, x1) -> _evar_0_3 x x0 x1
     | Copn (x, x0, x1) -> _evar_0_4 x x0 x1
     | Cif (x, x0, x1) -> _evar_0_5 x x0 x1
     | Cfor (x, x0, x1) -> _evar_0_6 x x0 x1
     | Cwhile (x, x0) -> Obj.magic _evar_0_7 x x0
     | Ccall (x, x0, x1, x2) -> _evar_0_8 x x0 x1 x2)
  in
  let _evar_0_4 = fun ii1 x1 f1 arg1 _top_assumption_0 ->
    let _evar_0_4 = fun _ _ _ -> ReflectF in
    let _evar_0_5 = fun _ _ _ -> ReflectF in
    let _evar_0_6 = fun _ _ _ -> ReflectF in
    let _evar_0_7 = fun _ _top_assumption_1 ->
      let _evar_0_7 = fun _top_assumption_2 ->
        let _evar_0_7 = fun _ _ _ _ -> ReflectF in
        let (x, x0) = _top_assumption_2 in _evar_0_7 x x0
      in
      let (x, x0) = _top_assumption_1 in _evar_0_7 x x0
    in
    let _evar_0_8 = fun _ _ -> ReflectF in
    let _evar_0_9 = fun ii2 x2 f2 arg2 ->
      equivP
        ((&&)
          ((&&)
            ((&&) (eq_op inline_info_eqType ii1 ii2)
              (eq_op (seq_eqType lval_eqType) x1 x2))
            (eq_op pos_eqType f1 f2))
          (eq_op (seq_eqType Eq_pexpr.Exports.eqType) arg1 arg2))
        (idP
          ((&&)
            ((&&)
              ((&&) (eq_op inline_info_eqType ii1 ii2)
                (eq_op (seq_eqType lval_eqType) x1 x2))
              (eq_op pos_eqType f1 f2))
            (eq_op (seq_eqType Eq_pexpr.Exports.eqType) arg1 arg2)))
    in
    (match _top_assumption_0 with
     | Cassgn (x, x0, x2) -> _evar_0_4 x x0 x2
     | Copn (x, x0, x2) -> _evar_0_5 x x0 x2
     | Cif (x, x0, x2) -> _evar_0_6 x x0 x2
     | Cfor (x, x0, x2) -> _evar_0_7 x x0 x2
     | Cwhile (x, x0) -> _evar_0_8 x x0
     | Ccall (x, x0, x2, x3) -> Obj.magic _evar_0_9 x x0 x2 x3)
  in
  (match _top_assumption_ with
   | Cassgn (x, x0, x1) -> Obj.magic _evar_0_ x x0 x1
   | Copn (x, x0, x1) -> Obj.magic _evar_0_0 x x0 x1
   | Cif (x, x0, x1) -> Obj.magic _evar_0_1 x x0 x1
   | Cfor (x, x0, x1) -> Obj.magic _evar_0_2 x x0 x1
   | Cwhile (x, x0) -> Obj.magic _evar_0_3 x x0
   | Ccall (x, x0, x1, x2) -> Obj.magic _evar_0_4 x x0 x1 x2)

(** val instr_eq_axiom : instr Equality.axiom **)

let instr_eq_axiom =
  instr_eq_axiom_ instr_r_eq_axiom

(** val instr_eqMixin : instr Equality.mixin_of **)

let instr_eqMixin =
  { Equality.op = instr_beq; Equality.mixin_of__1 = instr_eq_axiom }

(** val instr_eqType : Equality.coq_type **)

let instr_eqType =
  Obj.magic instr_eqMixin

(** val fundef_beq : fundef -> fundef -> bool **)

let fundef_beq fd1 fd2 =
  let { f_iinfo = ii1; f_params = x1; f_body = c1; f_res = r1 } = fd1 in
  let { f_iinfo = ii2; f_params = x2; f_body = c2; f_res = r2 } = fd2 in
  (&&)
    ((&&)
      ((&&) (eq_op pos_eqType (Obj.magic ii1) (Obj.magic ii2))
        (eq_op (seq_eqType var_i_eqType) (Obj.magic x1) (Obj.magic x2)))
      (eq_op (seq_eqType instr_eqType) (Obj.magic c1) (Obj.magic c2)))
    (eq_op (seq_eqType var_i_eqType) (Obj.magic r1) (Obj.magic r2))

(** val fundef_eq_axiom : fundef Equality.axiom **)

let fundef_eq_axiom _top_assumption_ =
  let _evar_0_ = fun i1 p1 c1 r1 _top_assumption_0 ->
    let _evar_0_ = fun i2 p2 c2 r2 ->
      equivP
        ((&&)
          ((&&)
            ((&&) (eq_op pos_eqType i1 i2)
              (eq_op (seq_eqType var_i_eqType) p1 p2))
            (eq_op (seq_eqType instr_eqType) c1 c2))
          (eq_op (seq_eqType var_i_eqType) r1 r2))
        (idP
          ((&&)
            ((&&)
              ((&&) (eq_op pos_eqType i1 i2)
                (eq_op (seq_eqType var_i_eqType) p1 p2))
              (eq_op (seq_eqType instr_eqType) c1 c2))
            (eq_op (seq_eqType var_i_eqType) r1 r2)))
    in
    let { f_iinfo = x; f_params = x0; f_body = x1; f_res = x2 } =
      _top_assumption_0
    in
    Obj.magic _evar_0_ x x0 x1 x2
  in
  let { f_iinfo = x; f_params = x0; f_body = x1; f_res = x2 } =
    _top_assumption_
  in
  Obj.magic _evar_0_ x x0 x1 x2

(** val fundef_eqMixin : fundef Equality.mixin_of **)

let fundef_eqMixin =
  { Equality.op = fundef_beq; Equality.mixin_of__1 = fundef_eq_axiom }

(** val fundef_eqType : Equality.coq_type **)

let fundef_eqType =
  Obj.magic fundef_eqMixin

(** val get_fundef :
    (Equality.sort * fundef) list -> Equality.sort -> fundef option **)

let get_fundef p f =
  let pos = find (fun ffd -> eq_op pos_eqType f (fst ffd)) p in
  if leq (S pos) (size p)
  then Some (snd (nth ((Obj.magic Coq_xH), dummy_fundef) p pos))
  else None

(** val map_prog :
    (fundef -> fundef) -> (funname * fundef) list -> (funname * fundef) list **)

let map_prog f =
  map (fun f0 -> ((fst f0), (f (snd f0))))

(** val vrv_rec : Sv.t -> lval -> Sv.t **)

let vrv_rec s = function
| Lvar x -> Sv.add (Obj.magic v_var x) s
| Laset (x, _) -> Sv.add (Obj.magic v_var x) s
| _ -> s

(** val vrvs_rec : Sv.t -> lval list -> Sv.t **)

let vrvs_rec s rv =
  foldl vrv_rec s rv

(** val vrv : lval -> Sv.t **)

let vrv =
  vrv_rec Sv.empty

(** val vrvs : lval list -> Sv.t **)

let vrvs =
  vrvs_rec Sv.empty

(** val write_i_rec : Sv.t -> instr_r -> Sv.t **)

let rec write_i_rec s = function
| Cassgn (x, _, _) -> vrv_rec s x
| Copn (xs, _, _) -> vrvs_rec s xs
| Cif (_, c1, c2) -> foldl write_I_rec (foldl write_I_rec s c2) c1
| Cfor (x, _, c) -> foldl write_I_rec (Sv.add (Obj.magic v_var x) s) c
| Cwhile (_, c) -> foldl write_I_rec s c
| Ccall (_, x, _, _) -> vrvs_rec s x

(** val write_I_rec : Sv.t -> instr -> Sv.t **)

and write_I_rec s = function
| MkI (_, i0) -> write_i_rec s i0

(** val write_i : instr_r -> Sv.t **)

let write_i i =
  write_i_rec Sv.empty i

(** val write_c_rec : Sv.t -> instr list -> Sv.t **)

let write_c_rec s c =
  foldl write_I_rec s c

(** val read_e_rec : Sv.t -> pexpr -> Sv.t **)

let rec read_e_rec s = function
| Pcast e0 -> read_e_rec s e0
| Pvar x -> Sv.add (Obj.magic v_var x) s
| Pget (x, e0) -> read_e_rec (Sv.add (Obj.magic v_var x) s) e0
| Pload (x, e0) -> read_e_rec (Sv.add (Obj.magic v_var x) s) e0
| Pnot e0 -> read_e_rec s e0
| Papp2 (_, e1, e2) -> read_e_rec (read_e_rec s e2) e1
| _ -> s

(** val read_es_rec : Sv.t -> pexpr list -> Sv.t **)

let read_es_rec =
  foldl read_e_rec

(** val read_es : pexpr list -> Sv.t **)

let read_es =
  read_es_rec Sv.empty

(** val read_rv_rec : Sv.t -> lval -> Sv.t **)

let read_rv_rec s = function
| Lmem (x, e) -> read_e_rec (Sv.add (Obj.magic v_var x) s) e
| Laset (x, e) -> read_e_rec (Sv.add (Obj.magic v_var x) s) e
| _ -> s

(** val read_rv : lval -> Sv.t **)

let read_rv =
  read_rv_rec Sv.empty

(** val read_rvs_rec : Sv.t -> lval list -> Sv.t **)

let read_rvs_rec =
  foldl read_rv_rec

(** val read_i_rec : Sv.t -> instr_r -> Sv.t **)

let rec read_i_rec s = function
| Cassgn (x, _, e) -> read_rv_rec (read_e_rec s e) x
| Copn (xs, _, es) -> read_es_rec (read_rvs_rec s xs) es
| Cif (b, c1, c2) ->
  let s0 = foldl read_I_rec s c1 in
  let s1 = foldl read_I_rec s0 c2 in read_e_rec s1 b
| Cfor (_, r, c) ->
  let (p, e2) = r in
  let (_, e1) = p in
  let s0 = foldl read_I_rec s c in read_e_rec (read_e_rec s0 e2) e1
| Cwhile (e, c) -> let s0 = foldl read_I_rec s c in read_e_rec s0 e
| Ccall (_, xs, _, es) -> read_es_rec (read_rvs_rec s xs) es

(** val read_I_rec : Sv.t -> instr -> Sv.t **)

and read_I_rec s = function
| MkI (_, i0) -> read_i_rec s i0

(** val read_i : instr_r -> Sv.t **)

let read_i =
  read_i_rec Sv.empty

(** val is_const : pexpr -> coq_Z option **)

let rec is_const = function
| Pconst n -> Some n
| _ -> None

(** val is_bool : pexpr -> bool option **)

let is_bool = function
| Pbool b -> Some b
| _ -> None
