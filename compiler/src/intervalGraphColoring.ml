open Utils
open Prog

type graph = (int * int) Mv.t
type color = int
type coloring = color Mv.t

type name = var
type date = int

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

let pick fresh =
  function
  | [] -> fresh, fresh + 1, []
  | c :: free -> c, fresh, free

let rec solve_rec (fresh, free, result) =
  function
  | _, Start n ->
     let c, fresh, free = pick fresh free in
     fresh, free, Mv.add n c result
  | _, End n ->
     let c = Mv.find n result in
     fresh, c :: free, result

let solve_aux todo =
  let _, _, result = List.fold_left solve_rec (0, [], Mv.empty) todo in
  result

let events_of_graph g =
  Mv.fold (fun n (min, max) result ->
      if min < max
      then (min, Start n) :: (max, End n) :: result
      else result
    )
    g []

let solve g =
  g |> events_of_graph |> List.sort compare_event |> solve_aux
