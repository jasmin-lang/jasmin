open Utils
open Prog

type graph = (int * int) Mv.t
type color = var
type coloring = color Mv.t

type name = var

type event =
  | Start of name
  | End of name

let compare_event (dx, x) (dy, y) =
  let c = dx - dy in
  if c = 0 then
    match x, y with
    | Start _, End _ -> 1
    | End _, Start _ -> -1
    | Start a, Start b | End a, End b -> V.compare a b
  else c

let pick sz n =
  function
  | [] -> V.mk n.v_name (Stack Direct) (Arr(U8,sz)) n.v_dloc n.v_annot, []
  | c :: free -> c, free

let solve_rec sz (free, result) =
  function
  | _, Start n ->
     let c, free = pick sz n free in
     free, Mv.add n c result
  | _, End n ->
     let c = Mv.find n result in
     c :: free, result

let solve_aux sz todo =
  let _, result = List.fold_left (solve_rec sz) ([], Mv.empty) todo in
  result

let events_of_graph g =
  Mv.fold (fun n (min, max) result ->
      assert(min < max);
      (min, Start n) :: (max, End n) :: result
    )
    g []

let solve sz g =
  g |> events_of_graph |> List.sort compare_event |> (solve_aux sz)
