open Datatypes
open Eqtype
open Ssrbool

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val size : 'a1 list -> nat **)

let rec size = function
| [] -> O
| _ :: s' -> S (size s')

(** val cat : 'a1 list -> 'a1 list -> 'a1 list **)

let rec cat s1 s2 =
  match s1 with
  | [] -> s2
  | x :: s1' -> x :: (cat s1' s2)

(** val nth : 'a1 -> 'a1 list -> nat -> 'a1 **)

let rec nth x0 s n =
  match s with
  | [] -> x0
  | x :: s' ->
    (match n with
     | O -> x
     | S n' -> nth x0 s' n')

(** val find : 'a1 pred -> 'a1 list -> nat **)

let rec find a = function
| [] -> O
| x :: s' -> if a x then O else S (find a s')

(** val eqseq :
    Equality.coq_type -> Equality.sort list -> Equality.sort list -> bool **)

let rec eqseq t s1 s2 =
  match s1 with
  | [] ->
    (match s2 with
     | [] -> true
     | _ :: _ -> false)
  | x1 :: s1' ->
    (match s2 with
     | [] -> false
     | x2 :: s2' -> (&&) (eq_op t x1 x2) (eqseq t s1' s2'))

(** val eqseqP : Equality.coq_type -> Equality.sort list Equality.axiom **)

let eqseqP t _top_assumption_ =
  let _evar_0_ = fun _top_assumption_0 ->
    let _evar_0_ = ReflectT in
    let _evar_0_0 = fun _ _ -> ReflectF in
    (match _top_assumption_0 with
     | [] -> _evar_0_
     | x :: x0 -> _evar_0_0 x x0)
  in
  let _evar_0_0 = fun x1 s1 iHs _top_assumption_0 ->
    let _evar_0_0 = ReflectF in
    let _evar_0_1 = fun x2 s2 ->
      let _evar_0_1 = fun _ -> iffP (eqseq t s1 s2) (iHs s2) in
      let _evar_0_2 = fun _ -> ReflectF in
      (match eqP t x1 x2 with
       | ReflectT -> _evar_0_1 __
       | ReflectF -> _evar_0_2 __)
    in
    (match _top_assumption_0 with
     | [] -> _evar_0_0
     | x :: x0 -> _evar_0_1 x x0)
  in
  let rec f = function
  | [] -> _evar_0_
  | y :: l0 -> _evar_0_0 y l0 (f l0)
  in f _top_assumption_

(** val seq_eqMixin :
    Equality.coq_type -> Equality.sort list Equality.mixin_of **)

let seq_eqMixin t =
  { Equality.op = (eqseq t); Equality.mixin_of__1 = (eqseqP t) }

(** val seq_eqType : Equality.coq_type -> Equality.coq_type **)

let seq_eqType t =
  Obj.magic seq_eqMixin t

(** val mem_seq :
    Equality.coq_type -> Equality.sort list -> Equality.sort -> bool **)

let rec mem_seq t = function
| [] -> (fun _ -> false)
| y :: s' -> let p = mem_seq t s' in (fun x -> (||) (eq_op t x y) (p x))

type eqseq_class = Equality.sort list

(** val pred_of_eq_seq :
    Equality.coq_type -> eqseq_class -> Equality.sort pred_sort **)

let pred_of_eq_seq t s =
  Obj.magic (fun x -> mem_seq t s x)

(** val seq_predType : Equality.coq_type -> Equality.sort predType **)

let seq_predType t =
  mkPredType (Obj.magic pred_of_eq_seq t)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| x :: s' -> (f x) :: (map f s')

(** val iota : nat -> nat -> nat list **)

let rec iota m = function
| O -> []
| S n' -> m :: (iota (S m) n')

(** val foldr : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldr f z0 = function
| [] -> z0
| x :: s' -> f x (foldr f z0 s')

(** val foldl : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 list -> 'a2 **)

let rec foldl f z = function
| [] -> z
| x :: s' -> foldl f (f z x) s'

(** val zip : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec zip s t =
  match s with
  | [] -> []
  | x :: s' ->
    (match t with
     | [] -> []
     | y :: t' -> (x, y) :: (zip s' t'))

(** val flatten : 'a1 list list -> 'a1 list **)

let flatten s =
  foldr cat [] s
