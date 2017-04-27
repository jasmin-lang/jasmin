open Datatypes
open Ssrfun

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val addb : bool -> bool -> bool **)

let addb = function
| true -> negb
| false -> (fun x -> x)

(** val isSome : 'a1 option -> bool **)

let isSome = function
| Some _ -> true
| None -> false

type reflect =
| ReflectT
| ReflectF

(** val iffP : bool -> reflect -> reflect **)

let iffP _ pb =
  let _evar_0_ = fun _ _ _ -> ReflectT in
  let _evar_0_0 = fun _ _ _ -> ReflectF in
  (match pb with
   | ReflectT -> _evar_0_ __ __ __
   | ReflectF -> _evar_0_0 __ __ __)

(** val equivP : bool -> reflect -> reflect **)

let equivP b pb =
  iffP b pb

type alt_spec = __alt_spec Lazy.t
and __alt_spec =
| AltTrue
| AltFalse

(** val altP : bool -> reflect -> alt_spec **)

let altP _ pb =
  let _evar_0_ = fun _ _ -> lazy AltTrue in
  let _evar_0_0 = fun _ _ -> lazy AltFalse in
  (match pb with
   | ReflectT -> _evar_0_ __ __
   | ReflectF -> _evar_0_0 __ __)

(** val idP : bool -> reflect **)

let idP = function
| true -> ReflectT
| false -> ReflectF

(** val boolP : bool -> alt_spec **)

let boolP b1 =
  altP b1 (idP b1)

(** val andP : bool -> bool -> reflect **)

let andP b1 b2 =
  if b1 then if b2 then ReflectT else ReflectF else ReflectF

type 't pred = 't -> bool

type 't rel = 't -> 't pred

type 't simpl_rel = ('t, 't pred) simpl_fun

(** val coq_SimplRel : 'a1 rel -> 'a1 simpl_rel **)

let coq_SimplRel r =
  lazy (SimplFun (fun x -> r x))

(** val rel_of_simpl_rel : 'a1 simpl_rel -> 'a1 rel **)

let rel_of_simpl_rel r x y =
  fun_of_simpl r x y

type 't mem_pred = 't __mem_pred Lazy.t
and 't __mem_pred =
| Mem of 't pred

type 't predType = { topred : (__ -> 't pred);
                     predType__1 : (__ -> 't mem_pred) }

type 't pred_sort = __

(** val mkPredType : ('a2 -> 'a1 -> bool) -> 'a1 predType **)

let mkPredType toP =
  { topred = (Obj.magic toP); predType__1 = (fun p -> lazy (Mem (fun x ->
    Obj.magic toP p x))) }

(** val pred_of_mem : 'a1 mem_pred -> 'a1 pred_sort **)

let pred_of_mem mp =
  let Mem p = Lazy.force mp in Obj.magic (fun x -> p x)

(** val mem : 'a1 predType -> 'a1 pred_sort -> 'a1 mem_pred **)

let mem pT =
  pT.predType__1

(** val in_mem : 'a1 -> 'a1 mem_pred -> bool **)

let in_mem x mp =
  Obj.magic pred_of_mem mp x
