open Datatypes
open Ssrbool
open Ssrfun

type __ = Obj.t

module Equality =
 struct
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  (** val op : 'a1 mixin_of -> 'a1 rel **)

  let op x = x.op

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  (** val coq_class : coq_type -> sort mixin_of **)

  let coq_class cT =
    cT

  (** val pack : 'a1 mixin_of -> coq_type **)

  let pack c =
    Obj.magic c

  (** val clone : coq_type -> 'a1 mixin_of -> (sort -> 'a1) -> coq_type **)

  let clone _ c _ =
    pack c
 end

(** val eq_op : Equality.coq_type -> Equality.sort rel **)

let eq_op t =
  (Equality.coq_class t).Equality.op

(** val eqP : Equality.coq_type -> Equality.sort Equality.axiom **)

let eqP t =
  let _evar_0_ = fun _ a -> a in
  let { Equality.op = x; Equality.mixin_of__1 = x0 } = t in _evar_0_ x x0

(** val eqb : bool -> bool -> bool **)

let eqb b =
  addb (negb b)

(** val eqbP : bool Equality.axiom **)

let eqbP _top_assumption_ =
  let _evar_0_ = fun _top_assumption_0 ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = ReflectF in
    if _top_assumption_0 then _evar_0_ else _evar_0_0
  in
  let _evar_0_0 = fun _top_assumption_0 ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = ReflectT in
    if _top_assumption_0 then _evar_0_0 else _evar_0_1
  in
  if _top_assumption_ then _evar_0_ else _evar_0_0

(** val bool_eqMixin : bool Equality.mixin_of **)

let bool_eqMixin =
  { Equality.op = eqb; Equality.mixin_of__1 = eqbP }

(** val bool_eqType : Equality.coq_type **)

let bool_eqType =
  Obj.magic bool_eqMixin

(** val pair_eq :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    simpl_rel **)

let pair_eq t1 t2 =
  coq_SimplRel (fun u v ->
    (&&) (eq_op t1 (fst u) (fst v)) (eq_op t2 (snd u) (snd v)))

(** val pair_eqP :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    Equality.axiom **)

let pair_eqP t1 t2 _top_assumption_ =
  let _evar_0_ = fun x1 x2 _top_assumption_0 ->
    let _evar_0_ = fun y1 y2 ->
      iffP ((&&) (eq_op t1 x1 y1) (eq_op t2 x2 y2))
        (andP (eq_op t1 x1 y1) (eq_op t2 x2 y2))
    in
    let (x, x0) = _top_assumption_0 in _evar_0_ x x0
  in
  let (x, x0) = _top_assumption_ in _evar_0_ x x0

(** val prod_eqMixin :
    Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
    Equality.mixin_of **)

let prod_eqMixin t1 t2 =
  { Equality.op = (rel_of_simpl_rel (pair_eq t1 t2)); Equality.mixin_of__1 =
    (pair_eqP t1 t2) }

(** val prod_eqType :
    Equality.coq_type -> Equality.coq_type -> Equality.coq_type **)

let prod_eqType t1 t2 =
  Obj.magic prod_eqMixin t1 t2

(** val opt_eq :
    Equality.coq_type -> Equality.sort option -> Equality.sort option -> bool **)

let opt_eq t u v =
  Option.apply (fun x -> Option.apply (eq_op t x) false v) (negb (isSome v))
    u

(** val opt_eqP : Equality.coq_type -> Equality.sort option Equality.axiom **)

let opt_eqP t _top_assumption_ =
  let _evar_0_ = fun x _top_assumption_0 ->
    let _evar_0_ = fun y -> iffP (eq_op t x y) (eqP t x y) in
    let _evar_0_0 = ReflectF in
    (match _top_assumption_0 with
     | Some x0 -> _evar_0_ x0
     | None -> _evar_0_0)
  in
  let _evar_0_0 = fun _top_assumption_0 ->
    let _evar_0_0 = fun _ -> ReflectF in
    let _evar_0_1 = ReflectT in
    (match _top_assumption_0 with
     | Some x -> _evar_0_0 x
     | None -> _evar_0_1)
  in
  (match _top_assumption_ with
   | Some x -> _evar_0_ x
   | None -> _evar_0_0)

(** val option_eqMixin :
    Equality.coq_type -> Equality.sort option Equality.mixin_of **)

let option_eqMixin t =
  { Equality.op = (opt_eq t); Equality.mixin_of__1 = (opt_eqP t) }

(** val option_eqType : Equality.coq_type -> Equality.coq_type **)

let option_eqType t =
  Obj.magic option_eqMixin t
