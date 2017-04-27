open Datatypes
open Ssrfun

type __ = Obj.t

val addb : bool -> bool -> bool

val isSome : 'a1 option -> bool

type reflect =
| ReflectT
| ReflectF

val iffP : bool -> reflect -> reflect

val equivP : bool -> reflect -> reflect

type alt_spec = __alt_spec Lazy.t
and __alt_spec =
| AltTrue
| AltFalse

val altP : bool -> reflect -> alt_spec

val idP : bool -> reflect

val boolP : bool -> alt_spec

val andP : bool -> bool -> reflect

type 't pred = 't -> bool

type 't rel = 't -> 't pred

type 't simpl_rel = ('t, 't pred) simpl_fun

val coq_SimplRel : 'a1 rel -> 'a1 simpl_rel

val rel_of_simpl_rel : 'a1 simpl_rel -> 'a1 rel

type 't mem_pred = 't __mem_pred Lazy.t
and 't __mem_pred =
| Mem of 't pred

type 't predType = { topred : (__ -> 't pred);
                     predType__1 : (__ -> 't mem_pred) }

type 't pred_sort = __

val mkPredType : ('a2 -> 'a1 -> bool) -> 'a1 predType

val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort

val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred

val in_mem : 'a1 -> 'a1 mem_pred -> bool
