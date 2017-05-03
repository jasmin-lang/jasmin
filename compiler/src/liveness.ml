open Utils
open Prog

(* Updates [s_o] to hold which variables are live before a write_lval. *)
let dep_lv s_o x =
  match x with
  | Lvar x -> Sv.remove (L.unloc x) s_o
  | _      -> rvars_lv s_o x

(* Variables live before a write_lvals:
   this is tricky when a variable occurs several times,
   sometimes written, sometimes read;
   this correctly reflects the semantics which writes ℓ-values
   from left to right.
 *)
let dep_lvs s_o xs =
  List.fold_left dep_lv s_o xs

let writev_lval s = function
  | Lnone _     -> s
  | Lvar x      -> Sv.add (L.unloc x) s
  | Lmem _      -> s
  | Laset(x, _) -> Sv.add (L.unloc x) s

let writev_lvals s lvs = List.fold_left writev_lval s lvs

let rec live_i i s_o =
  let s_i, s_o, d = live_d i.i_desc s_o in
  s_i, { i_desc = d; i_loc = i.i_loc; i_info = (s_i, s_o); }

and live_d d (s_o: Sv.t) =
  match d with
  | Cblock c ->
    let s_i, c = live_c c s_o in
    s_i, s_o, Cblock c

  | Cassgn(x,t,e) ->
    let s_i = Sv.union (vars_e e) (dep_lv s_o x) in
    s_i, writev_lval s_o x, Cassgn(x,t,e)

  | Copn(xs,o,es) ->
    let s_i = Sv.union (vars_es es) (dep_lvs s_o xs) in
    s_i, writev_lvals s_o xs, Copn(xs,o,es)

  | Cif(e,c1,c2) ->
    let s1, c1 = live_c c1 s_o in
    let s2, c2 = live_c c2 s_o in
    Sv.union (vars_e e) (Sv.union s1 s2), s_o, Cif(e, c1, c2)

  | Cfor _ -> assert false (* Should have been removed before *)

  | Cwhile(c,e,c') ->
    let ve = (vars_e e) in
    let rec loop s_o =
      (* loop (c; if e then c' else exit) *)
      let s_i', c' = live_c c' s_o in
      let s_o' = Sv.union ve s_i' in
      let s_i, c = live_c c s_o' in
      if Sv.subset s_i s_o then s_o, (c,c')
      else loop (Sv.union s_i s_o) in
    let s_i, (c,c') = loop s_o in
    s_i, s_o, Cwhile(c, e, c')

  | Ccall(ii,xs,f,es) ->
    let s_i = Sv.union (vars_es es) (dep_lvs s_o xs) in
    s_i, writev_lvals s_o xs, Ccall(ii,xs,f,es)

and live_c c s_o =
  List.fold_right
    (fun i (s_o, c) ->
      let s_i, i = live_i i s_o in
      (s_i, i :: c))
    c
    (s_o, [])

let live_fd fd =
  let s_o = Sv.of_list (List.map L.unloc fd.f_ret) in
  let _, c = live_c fd.f_body s_o in
  {
    f_loc  = fd.f_loc;
    f_cc   = fd.f_cc  ;
    f_name = fd.f_name;
    f_args = fd.f_args;
    f_body = c;
    f_ret  = fd.f_ret ;
  }

let liveness prog = List.map live_fd prog

let pp_info fmt (s1, s2) =
  Format.fprintf fmt "before: %a; after %a@ "
    (Printer.pp_list " " (Printer.pp_var ~debug:true)) (Sv.elements s1)
    (Printer.pp_list " " (Printer.pp_var ~debug:true)) (Sv.elements s2)

let merge_class cf s =
  let add_conflict x cf =
    Mv.modify_opt x (fun s' -> Some (Sv.union (Sv.remove x s) (odfl Sv.empty s'))) cf
  in
  Sv.fold add_conflict s cf

let rec conflicts_i cf i =
  let (s1, s2) = i.i_info in
  let cf = merge_class cf s1 in

  match i.i_desc with
  | Cassgn _ | Copn _ | Ccall _ ->
    merge_class cf s2
  | Cblock c | Cfor( _, _, c) ->
    conflicts_c (merge_class cf s2) c
  | Cif(_, c1, c2) | Cwhile(c1, _, c2) ->
    conflicts_c (conflicts_c (merge_class cf s2) c1) c2
and conflicts_c cf c =
  List.fold_left conflicts_i cf c

let conflicts f =
  (* TODO: function arguments should conflict *)
  conflicts_c Mv.empty f.f_body
