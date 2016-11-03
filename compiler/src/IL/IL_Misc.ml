(* * Utility functions for intermediate language *)
(* ** Imports and abbreviations *)
open Core_kernel.Std
open IL_Lang

module L = ParserUtil.Lexing
module P = ParserUtil
module HT = Hashtbl
module DS = Dest.Set
module SS = String.Set
module PS = Param.Set
module VS = Var.Set

(* *** Collect variable uses
 * ------------------------------------------------------------------------ *)

(* We consider 'a[i] = e' as a use of 'a' and *)
let use_binstr _bi =
  failwith "undefined"
  (*
  function
  | Op(_,_,ss)             -> SS.union_list (List.map ~f:pvars_src ss)
  | Load(_,s,Pconst(_))    -> pvars_src s
  | Store(s1,Pconst(_),s2) -> SS.union (pvars_src s1) (pvars_src s2)
  | Comment(_)             -> SS.empty
  | Assgn(d,s,_)           ->
    SS.union (pvars_src s) (if d.d_idx<>inone then pvars_dest d else SS.empty)

  | Call(_,_,_)
  | Store(_,_,_)
  | Load(_,_,_)            -> failwith "use_binstr: unexpected basic instruction"
  *)

(*
let use_instr = function
  | Binstr(bi)        -> use_binstr bi
  | If(Fcond(fc),_,_) -> pvars_fcond fc
  | While(_,fc,_)     -> pvars_fcond fc
  | If(Pcond(_),_,_)
  | For(_,_,_,_)      -> failwith "use_instr: unexpected instruction"
*)

(* *** Collect variable definitions
 * ------------------------------------------------------------------------ *)

(*
let def_opt_dest od =
  Option.value_map ~default:SS.empty ~f:(fun s -> pvars_dest s) od
*)
(* We do not consider 'a[i] = e' as a def for 'a' since 'a[j]' (for j<>i) is not redefined *)
let def_binstr _bi =
  failwith "undefined"
  (*
  let ensure_not_aget d =
    if (d.d_idx<>inone) then failtype d.d_loc "LHS cannot be array"
  in
  match bi with
  | Assgn(d,_,_) when d.d_idx=inone->
    pvars_dest d
  | Assgn(_,_,_) ->
    SS.empty
  | Op(_,ds,_) ->
    List.iter ~f:ensure_not_aget ds;
    SS.union_list (List.map ~f:pvars_dest ds)
  | Load(d,_,Pconst(_)) ->
    ensure_not_aget d;
    pvars_dest d

  | Store(_,Pconst(_),_) -> SS.empty
  | Comment(_)           -> SS.empty

  | Call(_,_,_)
  | Store(_,_,_)
  | Load(_,_,_)          -> failwith "def_binstr: unexpected basic instruction"
  *)

(*
let def_instr = function
  | Binstr(bi)       -> def_binstr bi
  | If(Fcond(_),_,_) -> SS.empty
  | While(_,_,_)     -> SS.empty

  | If(Pcond(_),_,_)
  | For(_,_,_,_)     -> failwith "def_instr: unexpected instruction"
*)
