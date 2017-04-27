(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val coq_CompOpp : comparison -> comparison **)

let coq_CompOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type coq_CompareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val coq_CompareSpec2Type : comparison -> coq_CompareSpecT **)

let coq_CompareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a coq_CompSpecT = coq_CompareSpecT

(** val coq_CompSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 coq_CompSpecT **)

let coq_CompSpec2Type _ _ c =
  coq_CompareSpec2Type c
