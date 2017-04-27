open BinInt
open BinNums
open BinPos
open Datatypes
open Eqtype
open Ssrbool

type ('e, 'a) result =
| Ok of 'a
| Error of 'e

module Result :
 sig
  val bind :
    ('a2 -> ('a1, 'a3) result) -> ('a1, 'a2) result -> ('a1, 'a3) result
 end

val foldM :
  ('a2 -> 'a3 -> ('a1, 'a3) result) -> 'a3 -> 'a2 list -> ('a1, 'a3) result

val fold2 :
  'a3 -> ('a1 -> 'a2 -> 'a4 -> ('a3, 'a4) result) -> 'a1 list -> 'a2 list ->
  'a4 -> ('a3, 'a4) result

val all2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool

val lex :
  ('a1 -> 'a1 -> comparison) -> ('a2 -> 'a2 -> comparison) -> ('a1 * 'a2) ->
  ('a1 * 'a2) -> comparison

val bool_cmp : bool -> bool -> comparison

val pos_eqP : positive Equality.axiom

val pos_eqMixin : positive Equality.mixin_of

val pos_eqType : Equality.coq_type

val coq_Z_eqP : coq_Z Equality.axiom

val coq_Z_eqMixin : coq_Z Equality.mixin_of

val coq_Z_eqType : Equality.coq_type
