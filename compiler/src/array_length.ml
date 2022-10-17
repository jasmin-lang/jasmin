type t =
| Const of Z.t
| Add of t * t
| Sub of t * t
| Mul of t * t
| Var of string

let rec beq al1 al2 =
  match al1, al2 with
  | Const z1, Const z2 -> Z.equal z1 z2
  | Add (al11, al21), Add (al12, al22) -> beq al11 al12 && beq al21 al22
  | Sub (al11, al21), Sub (al12, al22) -> beq al11 al12 && beq al21 al22
  | Mul (al11, al21), Mul (al12, al22) -> beq al11 al12 && beq al21 al22
  | Var x1, Var x2 -> x1 = x2
  | _, _ -> false

let rec cmp al1 al2 =
  let open Datatypes in
  let res = compare al1 al2 in
  if res < 0 then Lt
  else if res = 0 then Eq
  else Gt
