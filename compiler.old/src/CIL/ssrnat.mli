open Datatypes
open Nat0
open Eqtype
open Ssrbool

val eqn : nat -> nat -> bool

val eqnP : nat Equality.axiom

val nat_eqMixin : nat Equality.mixin_of

val nat_eqType : Equality.coq_type

val subn_rec : nat -> nat -> nat

val subn : nat -> nat -> nat

val leq : nat -> nat -> bool
