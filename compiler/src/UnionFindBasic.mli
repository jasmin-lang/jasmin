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

(**This module offers a union-find data structure based on disjoint set
   forests, with path compression and linking by rank. *)

(**['a elem] is the type of elements, or references. Like the type ['a ref]
   of ordinary references, this type supports the operations of creating a
   new reference, reading a reference, writing a reference, and testing
   whether two references are the same. Unlike ordinary references, this
   type also supports a form of merging: {!union} merges two references,
   making them "the same reference". *)
type 'a elem

(**[make v] creates a fresh reference and sets its content to [v]. *)
val make: 'a -> 'a elem

(**[get x] returns the current content of the reference [x]. *)
val get: 'a elem -> 'a

(**[set x v] sets the content of the reference [x] to [v]. *)
val set: 'a elem -> 'a -> unit

(**[eq x y] determines whether the references [x] and [y] are "the same
   reference". At any point in time, [eq] is an equivalence relation on
   references: it is reflexive, symmetric, and transitive. When two references
   [x] and [y] are merged by invoking [union x y], they become the same
   reference: [eq x y] becomes true, and remains forever true. *)
val eq: 'a elem -> 'a elem -> bool

(**If [eq x y] is true initially, then [union x y] has no observable effect.
   Otherwise, [union x y] merges the references [x] and [y]. In either case,
   after the call, [eq x y] is true. [union x y] returns either [x] or [y].
   The content of the reference that is returned is unchanged. The content of
   the reference that is not returned is lost. *)
val union: 'a elem -> 'a elem -> 'a elem

(**If [eq x y] is true initially, then [merge f x y] has no observable effect.
   Otherwise, [merge f x y] merges the references [x] and [y] and sets the
   content of the reference to [f vx vy], where [vx] and [vy] are the initial
   contents of the references [x] and [y]. The function [f] is {i not} allowed
   to access the union-find data structure.

   [merge f x y] is equivalent to: {[
     if not (eq x y) then
       let vx, vy = get x, get y in
       let v = f vx vy in
       set (union x y) v
   ]} *)
val merge: ('a -> 'a -> 'a) -> 'a elem -> 'a elem -> 'a elem

(**[find x] returns a representative element of [x]'s equivalence class. This
   element is chosen in an unspecified but deterministic manner, so two calls
   to [find x] must return the same result, provided no calls to [union] take
   place in between. [eq x y] is equivalent to [find x == find y]. *)
val find: 'a elem -> 'a elem

(**[is_representative x] determines whether [x] is the representative
   element of its equivalence class. It is equivalent to [find x == x]. *)
val is_representative: 'a elem -> bool
