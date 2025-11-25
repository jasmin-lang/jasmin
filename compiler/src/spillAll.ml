open Utils
open Prog
open Pseudo_operator

let has_nospill = Annotations.has_symbol "nospill"

let mk_spill o s =
  let xs = Sv.elements s in
  let tys = List.map (fun x -> Conv.cty_of_ty x.v_ty) xs in
  let es = List.map (fun x -> Pvar (gkvar (L.mk_loc L._dummy x))) xs in
  Copn ([], AT_none, Sopn.Opseudo_op (Ospill (o, tys)), es)

let is_word = function Bty (U _) -> true | _ -> false

let is_spillable x =
  is_reg_kind x.v_kind && is_word x.v_ty
  && not (has_nospill x.v_annot || Annotations.has_symbol "msf" x.v_annot)

let spillable (s : Sv.t) : Sv.t = Sv.filter is_spillable s

let vars_lv = function
  | Lnone _ | Lvar _ -> Sv.empty
  | Lmem (_, _, _, e) | Laset (_, _, _, _, e) | Lasub (_, _, _, _, e) ->
      vars_e e

let vars_i = function
  | Cassgn (x, _, _, e) -> Sv.union (vars_lv x) (vars_e e)
  | Copn (xs, _, _, es) | Csyscall (xs, _, es) | Ccall (xs, _, es) ->
      List.fold Sv.union (vars_es es) (List.map vars_lv xs)
  | Cfor _ | Cif _ | Cwhile _ -> assert false

let rec spill_all_i i =
  let wrap i_desc = { i with i_desc; i_annot = [] } in
  match i.i_desc with
  | Cassgn _ | Copn _ | Csyscall _ | Ccall _ ->
      [
        i.i_desc |> vars_i |> spillable |> mk_spill Unspill |> wrap;
        i;
        i.i_desc |> assigns |> spillable |> mk_spill Spill |> wrap;
      ]
  | Cif (e, c1, c2) ->
      [
        e |> vars_e |> spillable |> mk_spill Unspill |> wrap;
        { i with i_desc = Cif (e, spill_all_c c1, spill_all_c c2) };
      ]
  | Cfor (x, (d, e1, e2), c) ->
      [
        [ e1; e2 ] |> vars_es |> spillable |> mk_spill Unspill |> wrap;
        { i with i_desc = Cfor (x, (d, e1, e2), spill_all_c c) };
      ]
  | Cwhile (al, c1, e, ei, c2) ->
      [
        {
          i with
          i_desc =
            Cwhile
              ( al,
                spill_all_c c1
                @ [ e |> vars_e |> spillable |> mk_spill Unspill |> wrap ],
                e,
                ei,
                spill_all_c c2 );
        };
      ]

and spill_all_c c = List.concat_map spill_all_i c

let spill_all_fd fd =
  if has_nospill fd.f_annot.f_user_annot then fd
  else
    let wrap i_desc =
      { i_desc; i_loc = L.i_dummy; i_info = fd.f_info; i_annot = [] }
    in
    let f_body =
      (fd.f_args |> Sv.of_list |> spillable |> mk_spill Spill |> wrap)
      :: spill_all_c fd.f_body
      @ [
          fd.f_ret |> List.map L.unloc |> Sv.of_list |> spillable
          |> mk_spill Unspill |> wrap;
        ]
    in
    { fd with f_body }

let doit (gd, fds) = (gd, List.map spill_all_fd fds)
