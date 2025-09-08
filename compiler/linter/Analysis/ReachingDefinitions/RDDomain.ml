open Jasmin
open Utils
open Prog

type t = Siloc.t Mv.t

let empty : t = Mv.empty
let add xs i = Sv.fold (fun x -> Mv.add x (Siloc.singleton i)) xs
let join = Mv.union (fun _ a b -> Some (Siloc.union a b))

let included (x : t) (y : t) =
  Mv.for_all (fun x s1 -> Siloc.subset s1 (Mv.find_default Siloc.empty x y)) x

let forget x = Mv.remove x

let pp fmt ((_, d) : Location.i_loc * t) =
  Mv.iter
    (fun k v ->
      Format.fprintf fmt "%s : %a@." k.v_name
        (pp_list ", " Location.pp_iloc)
        (Siloc.elements v))
    d
