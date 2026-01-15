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

type twins = var Hv.t
(** Each spilled variable has a twin in the stack. A [twins] remembers their
    names *)

let get_twin (m: twins) x =
  let open Wsize in
  try Hv.find m x
  with Not_found ->
    let kind =
      let ref = match x.v_kind with Reg (_, ref) -> ref | _ -> assert false in
      if Cident.spill_to_mmx x then Reg (Extra, ref) else Stack ref
    in
    let annot = Annot.consume "spill" x.v_annot in
    let y = V.mk x.v_name kind x.v_ty x.v_dloc annot in
    Hv.add m x y;
    y

let spill_x m o x =
  let y = get_twin m x in
  let s, d = match o with Unspill -> (y, x) | Spill -> (x, y) in
  let e = Pvar (gkvar (L.mk_loc L._dummy s)) in
  let lv = Lvar (L.mk_loc L._dummy d) in
  Cassgn (lv, AT_none, s.v_ty, e)

let mk_spill m o s = Sv.fold (fun x acc -> spill_x m o x :: acc) s []

let vars_lv = function
  | Lnone _ | Lvar _ -> Sv.empty
  | Lmem (_, _, _, e) | Laset (_, _, _, _, e) | Lasub (_, _, _, _, e) ->
      vars_e e

let vars_i = function
  | Cassgn (x, _, _, e) -> Sv.union (vars_lv x) (vars_e e)
  | Copn (xs, _, _, es) | Csyscall (xs, _, es) | Ccall (xs, _, es) ->
      List.fold Sv.union (vars_es es) (List.map vars_lv xs)
  | Cassert (_, e) -> vars_a e
  | Cfor _ | Cif _ | Cwhile _ -> assert false

let rec spill_all_i m strategy i =
  let wrap i_desc =
    { i with i_desc; i_loc = L.refresh_i_loc i.i_loc; i_annot = [] }
  in
  let op o xs = xs |> spillable strategy |> mk_spill m o |> List.map wrap in
  match i.i_desc with
  | Cassgn _ | Copn _ | Csyscall _ | Ccall _ | Cassert _ ->
      op Unspill (vars_i i.i_desc) @ (i :: op Spill (assigns i.i_desc))
  | Cif (e, c1, c2) ->
      op Unspill (vars_e e)
      @ [
          {
            i with
            i_desc =
              Cif (e, spill_all_c m strategy c1, spill_all_c m strategy c2);
          };
        ]
  | Cfor (x, (d, e1, e2), c) ->
      op Unspill (vars_es [ e1; e2 ])
      @ [ { i with i_desc = Cfor (x, (d, e1, e2), spill_all_c m strategy c) } ]
  | Cwhile (al, c1, e, ei, c2) ->
      [
        {
          i with
          i_desc =
            Cwhile
              ( al,
                spill_all_c m strategy c1 @ op Unspill (vars_e e),
                e,
                ei,
                spill_all_c m strategy c2 );
        };
      ]

and spill_all_c m strategy c = List.concat_map (spill_all_i m strategy) c

let spill_all_fd strategy fd =
  if has_nospill fd.f_annot.f_user_annot then fd
  else
    let twins = Hv.create 17 in
    let wrap i_desc =
      {
        i_desc;
        i_loc = L.(refresh_i_loc i_dummy);
        i_info = fd.f_info;
        i_annot = [];
      }
    in
    let op o xs =
      xs |> Sv.of_list |> spillable strategy |> mk_spill twins o
      |> List.map wrap
    in
    let f_body =
      (op Spill fd.f_args @ spill_all_c twins strategy fd.f_body)
      @ op Unspill (List.map L.unloc fd.f_ret)
    in
    { fd with f_body }

let doit strategy (gd, fds) = (gd, List.map (spill_all_fd strategy) fds)
