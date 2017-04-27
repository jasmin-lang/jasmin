open Datatypes
open Eqtype
open Ssrbool

val size : 'a1 list -> nat

val cat : 'a1 list -> 'a1 list -> 'a1 list

val nth : 'a1 -> 'a1 list -> nat -> 'a1

val find : 'a1 pred -> 'a1 list -> nat

val eqseq :
  Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool

val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom

val seq_eqMixin : Equality.coq_type -> Equality.sort list Equality.mixin_of

val seq_eqType : Equality.coq_type -> Equality.coq_type

val mem_seq : Equality.coq_type -> Equality.sort list -> Equality.sort -> bool

type eqseq_class = Equality.sort list

val pred_of_eq_seq :
  Equality.coq_type -> eqseq_class -> Equality.sort pred_sort

val seq_predType : Equality.coq_type -> Equality.sort predType

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val iota : nat -> nat -> nat list

val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val foldl : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2

val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val flatten : 'a1 list list -> 'a1 list
