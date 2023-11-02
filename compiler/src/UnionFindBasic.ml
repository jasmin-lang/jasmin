(***************************************************************************)
(*                                                                         *)
(*                                 UnionFind                               *)
(*                                                                         *)
(*                       François Pottier, Inria Paris                     *)
(*                                                                         *)
(*  Copyright Inria. All rights reserved. This file is distributed under   *)
(*  the terms of the GNU Library General Public License version 2, with a  *)
(*  special exception on linking, as described in the file LICENSE.        *)
(***************************************************************************)

(* This module offers a union-find data structure based on disjoint set
   forests, with path compression and linking by rank. *)

(* -------------------------------------------------------------------------- *)

(* The rank of a vertex is the maximum length, in edges, of an uncompressed path
   that leads to this vertex. In other words, the rank of [x] is the height of
   the tree rooted at [x] that would exist if we did not perform path
   compression. *)

type rank =
  int

(* The content of a vertex is a pointer to a parent vertex (if the vertex
   has a parent) or a pair of a rank and a user value (if the vertex has no
   parent, and is thus the representative vertex for this equivalence
   class). *)

(* We make the type ['a content] mutable, and we maintain the property that
   every vertex uniquely owns its content. This allows us to update a content
   in place instead of allocating a new content and updating the vertex with
   this new content.

   We obtain the property that:
   - only [make] allocates a new vertex (a reference and a [Root] content);
   - only [union] and [merge] allocate a new edge (a [Link] content).
   [find], [get], [set], [eq] allocate no memory. *)

type 'a content =
| Link of { mutable parent : 'a elem }
| Root of { mutable rank : rank; mutable value : 'a }

(* The type ['a elem] represents a vertex in the union-find data structure. *)

and 'a elem =
  'a content ref

(* -------------------------------------------------------------------------- *)

(* [make v] creates a new root of rank zero. *)

let make (v : 'a) : 'a elem =
  ref (Root { rank = 0; value = v })

(* -------------------------------------------------------------------------- *)

(* [find x] finds the representative vertex of the equivalence class of [x].
   It does so by following the path from [x] to the root. Path compression is
   performed (on the way back) by making every vertex along the path a
   direct child of the representative vertex. No rank is altered. *)

let rec find (x : 'a elem) : 'a elem =
  match !x with
  | Root _ ->
      x
  | Link ({ parent = y } as link) ->
      let z = find y in
      if z != y then
        link.parent <- z;
      z

let is_representative (x : 'a elem) : bool =
  match !x with
  | Root _ ->
      true
  | Link _ ->
      false

(* -------------------------------------------------------------------------- *)

(* [eq x y] determines whether the vertices [x] and [y] belong in the
   same equivalence class. It does so via two calls to [find] and a
   physical equality test. As a fast path, we first test whether [x]
   and [y] are physically equal. *)

let eq (x : 'a elem) (y : 'a elem) : bool =
  x == y || find x == find y

(* -------------------------------------------------------------------------- *)

(* [get x] returns the value stored at [x]'s representative vertex. *)

let get (x : 'a elem) : 'a =
  let x = find x in
  match !x with
  | Root { value = v; _ } ->
      v
  | Link _ ->
      assert false

(* -------------------------------------------------------------------------- *)

(* [set x] updates the value stored at [x]'s representative vertex. *)

let set (x : 'a elem) (v : 'a) : unit =
  let x = find x in
  match !x with
  | Root root ->
      root.value <- v
  | Link _ ->
      assert false

(* -------------------------------------------------------------------------- *)

(* [union x y] merges the equivalence classes of [x] and [y] by installing a
   link from one root vertex to the other. *)

(* Linking is by rank: the smaller-ranked vertex is made to point to the
   larger. If the two vertices have the same rank, then an arbitrary choice
   is made, and the rank of the new root is incremented by one. *)

let union (x : 'a elem) (y : 'a elem) : 'a elem =
  let x = find x
  and y = find y in
  if x == y then x else
    match !x, !y with
    | Root ({ rank = rx; _ } as rootx), Root { rank = ry; _ } ->
        if rx < ry then begin
          x := Link { parent = y };
          y
        end else if rx > ry then begin
          y := Link { parent = x };
          x
        end else begin
          y := Link { parent = x};
          rootx.rank <- rx + 1;
          x
        end
    | Root _, Link _
    | Link _, Root _
    | Link _, Link _ ->
        assert false

(* -------------------------------------------------------------------------- *)

(* [merge] is analogous to [union], but invokes a user-specified function [f]
   to compute the new value [v] associated with the equivalence class. *)

(* The function [f] must not affect the union-find data structure by making
   re-entrant calls to [set], [union], or [merge]. There are two reasons for
   this. First, [f] may be invoked at a time when the invariant of the data
   structure is temporarily violated: in the third branch below, the rank of
   [x] has not yet been increased when [f] is invoked. Second, more seriously,
   if [f] could call, say, [union], then that could change a [Root] into a
   [Link], so the write that follows the call to [f] might change a [Link]
   back into a [Root], something that does not make any sense. Also, if [f]
   could call [set], then the write that follows the call to [f] might undo
   the effect of this [set] operation; this also does not make sense. *)

(* The tests [if v != vy then ...] and [if v != vx then ...] are intended to
   save an allocation and a write when possible. *)

(* We invoke [f] before performing any update, so that if [f] fails
   (by raising an exception), the state is unaffected. *)

let merge (f : 'a -> 'a -> 'a) (x : 'a elem) (y : 'a elem) : 'a elem =
  let x = find x
  and y = find y in
  if x == y then x else
    match !x, !y with
    | Root ({ rank = rx; value = vx } as rootx),
      Root ({ rank = ry; value = vy } as rooty) ->
        let v = f vx vy in
        if rx < ry then begin
          x := Link { parent = y };
          if v != vy then rooty.value <- v;
          y
        end else if rx > ry then begin
          y := Link { parent = x };
          if v != vx then rootx.value <- v;
          x
        end else begin
          y := Link { parent = x };
          rootx.rank <- rx + 1;
          if v != vx then rootx.value <- v;
          x
        end
    | Root _, Link _
    | Link _, Root _
    | Link _, Link _ ->
        assert false
