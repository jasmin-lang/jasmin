open Datatypes

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k ->
    (match m with
     | O -> n
     | S l -> sub k l)

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' ->
    (match m with
     | O -> n
     | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n m =
  match n with
  | O -> O
  | S n' ->
    (match m with
     | O -> O
     | S m' -> S (min n' m'))
