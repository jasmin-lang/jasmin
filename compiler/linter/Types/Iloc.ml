open Jasmin.Location

type t =
| Default (* ? *)
| Instruction of i_loc (* actual instruction *)

let compare x y =
    match (x, y) with
    | Default, Default -> 0
    | Default, _ -> -1
    | _, Default -> 1
    | Instruction x, Instruction y -> Stdlib.Int.compare x.uid_loc y.uid_loc

let pp fmt = function
    | Default -> Format.fprintf fmt "?"
    | Instruction i -> Format.fprintf fmt "%a" pp_iloc_short i

module SIloc =  Set.Make (struct
  type nonrec t = t
  let compare = compare
end)
