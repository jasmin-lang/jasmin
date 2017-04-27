open Datatypes
open Nat0
open Eqtype
open Ssrbool

(** val eqn : nat -> nat -> bool **)

let rec eqn m n =
  match m with
  | O ->
    (match n with
     | O -> true
     | S _ -> false)
  | S m' ->
    (match n with
     | O -> false
     | S n' -> eqn m' n')

(** val eqnP : nat Equality.axiom **)

let eqnP n m =
  iffP (eqn n m) (idP (eqn n m))

(** val nat_eqMixin : nat Equality.mixin_of **)

let nat_eqMixin =
  { Equality.op = eqn; Equality.mixin_of__1 = eqnP }

(** val nat_eqType : Equality.coq_type **)

let nat_eqType =
  Obj.magic nat_eqMixin

(** val subn_rec : nat -> nat -> nat **)

let subn_rec =
  sub

(** val subn : nat -> nat -> nat **)

let subn =
  subn_rec

(** val leq : nat -> nat -> bool **)

let leq m n =
  eq_op nat_eqType (Obj.magic subn m n) (Obj.magic O)
