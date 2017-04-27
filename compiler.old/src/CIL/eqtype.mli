open Datatypes
open Ssrbool
open Ssrfun

type __ = Obj.t

module Equality :
 sig
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  val op : 'a1 mixin_of -> 'a1 rel

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort mixin_of

  val pack : 'a1 mixin_of -> coq_type

  val clone : coq_type -> 'a1 mixin_of -> (sort -> 'a1) -> coq_type
 end

val eq_op : Equality.coq_type -> Equality.sort rel

val eqP : Equality.coq_type -> Equality.sort Equality.axiom

val eqb : bool -> bool -> bool

val eqbP : bool Equality.axiom

val bool_eqMixin : bool Equality.mixin_of

val bool_eqType : Equality.coq_type

val pair_eq :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
  simpl_rel

val pair_eqP :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
  Equality.axiom

val prod_eqMixin :
  Equality.coq_type -> Equality.coq_type -> (Equality.sort * Equality.sort)
  Equality.mixin_of

val prod_eqType : Equality.coq_type -> Equality.coq_type -> Equality.coq_type

val opt_eq :
  Equality.coq_type -> Equality.sort option -> Equality.sort option -> bool

val opt_eqP : Equality.coq_type -> Equality.sort option Equality.axiom

val option_eqMixin :
  Equality.coq_type -> Equality.sort option Equality.mixin_of

val option_eqType : Equality.coq_type -> Equality.coq_type
