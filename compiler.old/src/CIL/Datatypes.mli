val negb : bool -> bool

type nat =
| O
| S of nat

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val coq_CompOpp : comparison -> comparison

type coq_CompareSpecT =
| CompEqT
| CompLtT
| CompGtT

val coq_CompareSpec2Type : comparison -> coq_CompareSpecT

type 'a coq_CompSpecT = coq_CompareSpecT

val coq_CompSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 coq_CompSpecT
