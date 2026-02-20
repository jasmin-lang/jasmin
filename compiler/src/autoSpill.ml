open Utils
open Prog
open Pseudo_operator

(* **************************************************************** *)

type strategy = OptIn | OptOut

let has_nospill a =
  Annotations.has_symbol "nospill" a || Annotations.has_symbol "msf" a

let has_spill = Annotations.has_symbol "spill"
let is_word = function Bty (U _) -> true | _ -> false

(** Tells whether a variable [x] is spillable, according to the given
    [strategy]. The variable must be of kind reg, of a type that is either word
    or ptr array, and annotated depending to the strategy. *)
let is_spillable strategy x =
  is_reg_kind x.v_kind
  && (is_ptr x.v_kind || is_word x.v_ty)
  &&
  match strategy with
  | OptIn -> has_spill x.v_annot
  | OptOut -> not (has_nospill x.v_annot)

let spillable strategy (s : Sv.t) : Sv.t = Sv.filter (is_spillable strategy) s

(* **************************************************************** *)

let mk_spill o s =
  let xs = Sv.elements s in
  let tys = List.map (fun x -> Conv.cty_of_ty x.v_ty) xs in
  let es = List.map (fun x -> Pvar (gkvar (L.mk_loc L._dummy x))) xs in
  Copn ([], AT_none, Sopn.Opseudo_op (Ospill (o, tys)), es)

let vars_lv = function
  | Lnone _ | Lvar _ -> Sv.empty
  | Lmem (_, _, _, e) | Laset (_, _, _, _, e) | Lasub (_, _, _, _, e) ->
      vars_e e

let vars_i = function
  | Cassgn (x, _, _, e) -> Sv.union (vars_lv x) (vars_e e)
  | Copn (xs, _, _, es) | Csyscall (xs, _, es) | Ccall (xs, _, es) ->
      List.fold Sv.union (vars_es es) (List.map vars_lv xs)
  | Cassert (_, e) -> vars_e e
  | Cfor _ | Cif _ | Cwhile _ -> assert false

let rec spill_all_i strategy i =
  let wrap i_desc = { i with i_desc; i_annot = [] } in
  let op o xs = xs |> spillable strategy |> mk_spill o |> wrap in
  match i.i_desc with
  | Cassgn _ | Copn _ | Csyscall _ | Ccall _ | Cassert _ ->
      [ op Unspill (vars_i i.i_desc); i; op Spill (assigns i.i_desc) ]
  | Cif (e, c1, c2) ->
      [
        op Unspill (vars_e e);
        {
          i with
          i_desc = Cif (e, spill_all_c strategy c1, spill_all_c strategy c2);
        };
      ]
  | Cfor (x, (d, e1, e2), c) ->
      [
        op Unspill (vars_es [ e1; e2 ]);
        { i with i_desc = Cfor (x, (d, e1, e2), spill_all_c strategy c) };
      ]
  | Cwhile (al, c1, e, ei, c2) ->
      [
        {
          i with
          i_desc =
            Cwhile
              ( al,
                spill_all_c strategy c1 @ [ op Unspill (vars_e e) ],
                e,
                ei,
                spill_all_c strategy c2 );
        };
      ]

and spill_all_c strategy c = List.concat_map (spill_all_i strategy) c

let spill_all_fd strategy fd =
  if has_nospill fd.f_annot.f_user_annot then fd
  else
    let wrap i_desc =
      { i_desc; i_loc = L.i_dummy; i_info = fd.f_info; i_annot = [] }
    in
    let op o xs =
      xs |> Sv.of_list |> spillable strategy |> mk_spill o |> wrap
    in
    let f_body =
      (op Spill fd.f_args :: spill_all_c strategy fd.f_body)
      @ [ op Unspill (List.map L.unloc fd.f_ret) ]
      |> refresh_i_loc_c
    in
    { fd with f_body }

let doit strategy (gd, fds) = (gd, List.map (spill_all_fd strategy) fds)
