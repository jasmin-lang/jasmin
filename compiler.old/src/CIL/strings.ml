open Ascii
open Datatypes
open String0
open Eqtype
open Gen_map
open Ssrbool
open Utils0

type __ = Obj.t

(** val bool_beq : bool -> bool -> bool **)

let rec bool_beq x y =
  if x then y else if y then false else true

(** val ascii_beq : ascii -> ascii -> bool **)

let rec ascii_beq x y =
  let Ascii (x0, x1, x2, x3, x4, x5, x6, x7) = x in
  let Ascii (x8, x9, x10, x11, x12, x13, x14, x15) = y in
  (&&) (bool_beq x0 x8)
    ((&&) (bool_beq x1 x9)
      ((&&) (bool_beq x2 x10)
        ((&&) (bool_beq x3 x11)
          ((&&) (bool_beq x4 x12)
            ((&&) (bool_beq x5 x13)
              ((&&) (bool_beq x6 x14) (bool_beq x7 x15)))))))

(** val ascii_cmp : ascii -> ascii -> comparison **)

let ascii_cmp c c' =
  let Ascii (b1, b2, b3, b4, b5, b6, b7, b8) = c in
  let Ascii (b1', b2', b3', b4', b5', b6', b7', b8') = c' in
  (match bool_cmp b1 b1' with
   | Eq ->
     (match bool_cmp b2 b2' with
      | Eq ->
        (match bool_cmp b3 b3' with
         | Eq ->
           (match bool_cmp b4 b4' with
            | Eq ->
              (match bool_cmp b5 b5' with
               | Eq ->
                 (match bool_cmp b6 b6' with
                  | Eq ->
                    (match bool_cmp b7 b7' with
                     | Eq -> bool_cmp b8 b8'
                     | x -> x)
                  | x -> x)
               | x -> x)
            | x -> x)
         | x -> x)
      | x -> x)
   | x -> x)

(** val string_beq : string -> string -> bool **)

let rec string_beq x y =
  match x with
  | EmptyString ->
    (match y with
     | EmptyString -> true
     | String (_, _) -> false)
  | String (x0, x1) ->
    (match y with
     | EmptyString -> false
     | String (x2, x3) -> (&&) (ascii_beq x0 x2) (string_beq x1 x3))

(** val string_eqP : string Equality.axiom **)

let string_eqP x y =
  iffP (string_beq x y) (idP (string_beq x y))

(** val string_eqMixin : string Equality.mixin_of **)

let string_eqMixin =
  { Equality.op = string_beq; Equality.mixin_of__1 = string_eqP }

(** val string_eqType : Equality.coq_type **)

let string_eqType =
  Equality.pack string_eqMixin

(** val string_cmp : string -> string -> comparison **)

let rec string_cmp s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> Eq
     | String (_, _) -> Lt)
  | String (c1, s3) ->
    (match s2 with
     | EmptyString -> Gt
     | String (c2, s4) ->
       (match ascii_cmp c1 c2 with
        | Eq -> string_cmp s3 s4
        | x -> x))

module CmpString =
 struct
  (** val t : Equality.coq_type **)

  let t =
    Equality.clone string_eqType (Obj.magic string_eqMixin) (fun x -> x)

  (** val cmp : Equality.sort -> Equality.sort -> comparison **)

  let cmp =
    Obj.magic string_cmp
 end

module Ms = Mmake(CmpString)
