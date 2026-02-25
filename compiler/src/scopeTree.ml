(** The algorithm in this module locates a suitable location for declaring each
    variable.

    The instructions of a function, represented by their location, are gathered
    in a tree that represents the nesting structure of the lexical scopes: a
    variable declared in a node is visible from all of its children, unless a
    variable with the same name is declared in between. Therefore a variable can
    be declared at the least common ancestor to all of its occurrences.

    The tree data structure that is used remembers the depth of each node to
    support the computation of least common ancestors. *)

open Utils
open Prog

type node = Location.i_loc
type nodeset = Siloc.t

module Tree : sig
  type t = private { parent : t option; depth : int; data : node }

  val root : node -> t
  val make : node -> t -> t
end = struct
  type t = { parent : t option; depth : int; data : node }

  let root ii = { parent = None; depth = 0; data = ii }
  let make ii t = { parent = Some t; data = ii; depth = 1 + t.depth }
end

let make ii = function None -> Tree.root ii | Some t -> Tree.make ii t

type tree = Tree.t Miloc.t

let parent_at_depth (d : int) (t : tree) (n : node) : node =
  assert (0 <= d);
  let open Tree in
  let rec loop n =
    if Stdlib.Int.equal d n.depth then n.data else loop (Option.get n.parent)
  in
  loop (Miloc.find n t)

let find_common_ancestor (t : tree) (nodes : nodeset) : node =
  assert (not (Siloc.is_empty nodes));
  (* Ensure all nodes in the set have the same depth *)
  let depth =
    Siloc.fold (fun n -> min (Miloc.find n t).depth) nodes Stdlib.Int.max_int
  in
  let nodes = Siloc.map (parent_at_depth depth t) nodes in
  (* Replace each node by its parent until we get a singleton *)
  let rec loop nodes =
    if Siloc.is_singleton nodes then Siloc.any nodes
    else
      nodes
      |> Siloc.map (fun n -> (Option.get (Miloc.find n t).parent).data)
      |> loop
  in
  loop nodes

(* --------------------------------------------------------------- *)
(* Compute variable occurrences in expressions and instructions *)

let variables_in_ggvar { gs; gv } (acc : Sv.t) : Sv.t =
  match gs with
  | E.Sglob -> acc
  | E.Slocal ->
      let x = L.unloc gv in
      if x.v_kind <> Const then Sv.add x acc else acc

let rec variables_in_pexpr (acc : Sv.t) (e : expr) : Sv.t =
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> acc
  | Pvar x -> variables_in_ggvar x acc
  | Pget (_, _, _, x, e) | Psub (_, _, _, x, e) ->
      variables_in_pexpr (variables_in_ggvar x acc) e
  | Pload (_, _, e) | Papp1 (_, e) -> variables_in_pexpr acc e
  | Papp2 (_, e1, e2) | Pif (_, _, e1, e2) -> variables_in_pexprs acc [ e1; e2 ]
  | PappN (_, es) -> variables_in_pexprs acc es

and variables_in_pexprs (acc : Sv.t) (es : expr list) : Sv.t =
  List.fold_left variables_in_pexpr acc es

let variables_in_plval (acc : Sv.t) : lval -> Sv.t = function
  | Lnone _ -> acc
  | Lvar x -> Sv.add (L.unloc x) acc
  | Lmem (_, _, _, e) -> variables_in_pexpr acc e
  | Laset (_, _, _, x, e) | Lasub (_, _, _, x, e) ->
      Sv.add (L.unloc x) (variables_in_pexpr acc e)

let variables_in_plvals (acc : Sv.t) : lvals -> Sv.t =
  List.fold_left variables_in_plval acc

let variables_in_instr_r : _ instr_r -> Sv.t = function
  | Cassgn (x, _, _, e) -> variables_in_pexpr (variables_in_plval Sv.empty x) e
  | Copn (xs, _, _, es) | Csyscall (xs, _, _, es) | Ccall (xs, _, _, es) ->
      variables_in_pexprs (variables_in_plvals Sv.empty xs) es
  | Cfor (x, (_, e1, e2), _) ->
      variables_in_pexprs (Sv.singleton (L.unloc x)) [ e1; e2 ]
  | Cif (e, _, _) | Cwhile (_, _, e, _, _) | Cassert (_, e) -> variables_in_pexpr Sv.empty e

(** Maps each variable to the set of nodes at which it occurs *)
let variable_occurrences (c : _ stmt) : nodeset Mv.t =
  let tbl = ref Mv.empty in
  let insert (n : node) (x : var) =
    tbl := Mv.modify_def Siloc.empty x (Siloc.add n) !tbl
  in
  iter_instr
    (fun i -> i.i_desc |> variables_in_instr_r |> Sv.iter (insert i.i_loc))
    c;
  !tbl

(* --------------------------------------------------------------- *)
(* Compute the scope tree *)

let rec tree_of_instr ((acc : tree), (t : Tree.t option)) (i : _ ginstr) :
    tree * Tree.t option =
  let t = make i.i_loc t in
  let acc = Miloc.add i.i_loc t acc in
  (tree_of_instr_r acc t i.i_desc, Some t)

and tree_of_instr_r (acc : tree) (t : Tree.t) : _ ginstr_r -> tree = function
  | Cassgn _ | Copn _ | Csyscall _ | Ccall _ | Cassert _ -> acc
  | Cfor (_, _, c) -> tree_of_stmt acc (Some t) c |> fst
  | Cif (_, c1, c2) | Cwhile (_, c1, _, _, c2) ->
      let acc, _ = tree_of_stmt acc (Some t) c1 in
      let acc, _ = tree_of_stmt acc (Some t) c2 in
      acc

and tree_of_stmt (acc : tree) (t : Tree.t option) (c : _ gstmt) :
    tree * Tree.t option =
  List.fold_left tree_of_instr (acc, t) c

(** Reverse a map from variable to nodes into the corresponding map from nodes
    to sets of variables *)
let reverse (m : node Mv.t) : Sv.t Miloc.t =
  Mv.fold (fun x n -> Miloc.modify_def Sv.empty n (Sv.add x)) m Miloc.empty

let get_declaration_sites (fd : _ func) : Sv.t Miloc.t =
  let t, last = tree_of_stmt Miloc.empty None fd.f_body in
  let occ = variable_occurrences fd.f_body in
  (* Add occurrences of returned variables at the last instruction, if any *)
  let occ =
    match last with
    | None -> occ
    | Some t ->
        List.fold_left
          (fun occ x ->
            Mv.modify_def Siloc.empty (L.unloc x) (Siloc.add t.data) occ)
          occ fd.f_ret
  in
  (* Remove function arguments as they must not be declared *)
  let occ = List.fold_left (fun occ x -> Mv.remove x occ) occ fd.f_args in
  Mv.map (find_common_ancestor t) occ |> reverse
