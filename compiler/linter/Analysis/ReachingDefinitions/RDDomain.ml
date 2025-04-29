open Jasmin
open Types
open Prog
open Format

module SIloc = Iloc.SIloc

type t = SIloc.t Mv.t
let empty : t = Mv.empty

let add xs i = Sv.fold (fun x -> Mv.add x (SIloc.singleton i)) xs

let join = Mv.union (fun _ a b -> Some (SIloc.union a b))

let included (x : t) (y : t) =
    Mv.for_all (fun x s1 -> SIloc.subset s1 (Mv.find_default SIloc.empty x y)) x

let forget x = Mv.remove x

let pp fmt ((_, d) : Location.i_loc * t) =
    Mv.iter
      (fun k v ->
        Format.fprintf fmt "%s : %a@." k.v_name
          (
            pp_print_seq ~pp_sep:(fun fmt () -> Format.fprintf fmt ",") Iloc.pp)
            (SIloc.to_seq v)
          )
      d
