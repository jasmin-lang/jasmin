open BinInt
open BinNums
open BinPos
open Datatypes
open Eqtype
open Ssrbool

type ('e, 'a) result =
| Ok of 'a
| Error of 'e

module Result =
 struct
  (** val bind :
      ('a2 -> ('a1, 'a3) result) -> ('a1, 'a2) result -> ('a1, 'a3) result **)

  let bind f = function
  | Ok x -> f x
  | Error s -> Error s
 end

(** val foldM :
    ('a2 -> 'a3 -> ('a1, 'a3) result) -> 'a3 -> 'a2 list -> ('a1, 'a3) result **)

let rec foldM f acc = function
| [] -> Ok acc
| a :: la -> Result.bind (fun acc0 -> foldM f acc0 la) (f a acc)

(** val fold2 :
    'a3 -> ('a1 -> 'a2 -> 'a4 -> ('a3, 'a4) result) -> 'a1 list -> 'a2 list
    -> 'a4 -> ('a3, 'a4) result **)

let rec fold2 e f la lb r =
  match la with
  | [] ->
    (match lb with
     | [] -> Ok r
     | _ :: _ -> Error e)
  | a :: la0 ->
    (match lb with
     | [] -> Error e
     | b :: lb0 -> Result.bind (fold2 e f la0 lb0) (f a b r))

(** val all2 : ('a1 -> 'a2 -> bool) -> 'a1 list -> 'a2 list -> bool **)

let rec all2 f l1 l2 =
  match l1 with
  | [] ->
    (match l2 with
     | [] -> true
     | _ :: _ -> false)
  | a1 :: l3 ->
    (match l2 with
     | [] -> false
     | a2 :: l4 -> (&&) (f a1 a2) (all2 f l3 l4))

(** val lex :
    ('a1 -> 'a1 -> comparison) -> ('a2 -> 'a2 -> comparison) -> ('a1 * 'a2)
    -> ('a1 * 'a2) -> comparison **)

let lex cmp1 cmp2 x y =
  match cmp1 (fst x) (fst y) with
  | Eq -> cmp2 (snd x) (snd y)
  | x0 -> x0

(** val bool_cmp : bool -> bool -> comparison **)

let bool_cmp b1 b2 =
  if b1 then if b2 then Eq else Gt else if b2 then Lt else Eq

(** val pos_eqP : positive Equality.axiom **)

let pos_eqP p1 p2 =
  iffP (Pos.eqb p1 p2) (idP (Pos.eqb p1 p2))

(** val pos_eqMixin : positive Equality.mixin_of **)

let pos_eqMixin =
  { Equality.op = Pos.eqb; Equality.mixin_of__1 = pos_eqP }

(** val pos_eqType : Equality.coq_type **)

let pos_eqType =
  Equality.pack pos_eqMixin

(** val coq_Z_eqP : coq_Z Equality.axiom **)

let coq_Z_eqP p1 p2 =
  iffP (Z.eqb p1 p2) (idP (Z.eqb p1 p2))

(** val coq_Z_eqMixin : coq_Z Equality.mixin_of **)

let coq_Z_eqMixin =
  { Equality.op = Z.eqb; Equality.mixin_of__1 = coq_Z_eqP }

(** val coq_Z_eqType : Equality.coq_type **)

let coq_Z_eqType =
  Equality.pack coq_Z_eqMixin
