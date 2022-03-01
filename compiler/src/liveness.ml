open Prog

(* Updates [s_o] to hold which variables are live before a write_lval. *)
let dep_lv s_o x =
  match x with
  | Lvar x -> Sv.remove (L.unloc x) s_o
  | _      -> vars_lv s_o x

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
  | Laset(_, x, _) -> Sv.add (L.unloc x) s

let writev_lvals s lvs = List.fold_left writev_lval s lvs

let is_trivial_move x e =
  match x, e with
  | Lvar x, Pvar y -> kind_i x = kind_i y
  | _              -> false

let is_move_op = function
  | Expr.Ox86(MOV _) -> true
  | _        -> false

(* When [weak] is true, the out live-set contains also the written variables. *)
let rec live_i weak i s_o =
  let s_i, s_o, d = live_d weak i.i_desc s_o in
  s_i, { i_desc = d; i_loc = i.i_loc; i_info = (s_i, s_o); }

and live_d weak d (s_o: Sv.t) =
  match d with
  | Cassgn(x, tg, ty, e) ->

    let s_i = Sv.union (vars_e e) (dep_lv s_o x) in
    let s_o =
      if weak && not (is_trivial_move x e) then writev_lval s_o x
      else s_o in
    s_i, s_o, Cassgn(x, tg, ty, e)

  | Copn(xs,t,o,es) ->
    let s_i = Sv.union (vars_es es) (dep_lvs s_o xs) in
    let s_o =
     if weak && not (is_move_op o && is_trivial_move (List.hd xs) (List.hd es))
     then writev_lvals s_o xs
     else s_o in
    s_i, s_o, Copn(xs,t,o,es)

  | Cif(e,c1,c2) ->
    let s1, c1 = live_c weak c1 s_o in
    let s2, c2 = live_c weak c2 s_o in
    Sv.union (vars_e e) (Sv.union s1 s2), s_o, Cif(e, c1, c2)

  | Cfor _ -> assert false (* Should have been removed before *)

  | Cwhile(a,c,e,c') ->
    let ve = (vars_e e) in
    let rec loop s_o =
      (* loop (c; if e then c' else exit) *)
      let s_o' = Sv.union ve s_o in
      let s_i, c = live_c weak c s_o' in
      let s_i', c' = live_c weak c' s_i in
      if Sv.subset s_i' s_o then s_i, (c,c')
      else loop (Sv.union s_i' s_o) in
    let s_i, (c,c') = loop s_o in
    s_i, s_o, Cwhile(a, c, e, c')

  | Ccall(ii,xs,f,es) ->
    let s_i = Sv.union (vars_es es) (dep_lvs s_o xs) in
    s_i, (if weak then writev_lvals s_o xs else s_o), Ccall(ii,xs,f,es)

and live_c weak c s_o =
  List.fold_right
    (fun i (s_o, c) ->
      let s_i, i = live_i weak i s_o in
      (s_i, i :: c))
    c
    (s_o, [])

let live_fd weak fd =
  let s_o = Sv.of_list (List.map L.unloc fd.f_ret) in
  let _, c = live_c weak fd.f_body s_o in
  { fd with f_body = c }

let liveness weak prog = 
  let fds = List.map (live_fd weak) (snd prog) in
  fst prog, fds

let pp_info fmt (s1, s2) =
  Format.fprintf fmt "before: %a; after %a@ "
    (Printer.pp_list " " (Printer.pp_var ~debug:true)) (Sv.elements s1)
    (Printer.pp_list " " (Printer.pp_var ~debug:true)) (Sv.elements s2)

let merge_class cf s =
  let add_conflict x cf =
    Mv.modify_def Sv.empty x (Sv.union (Sv.remove x s)) cf
  in
  Sv.fold add_conflict s cf

let rec conflicts_i cf i =
  let (s1, s2) = i.i_info in
  let cf = merge_class cf s1 in

  match i.i_desc with
  | Cassgn _ | Copn _ | Ccall _ ->
    merge_class cf s2
  | Cfor( _, _, c) ->
    conflicts_c (merge_class cf s2) c
  | Cif(_, c1, c2) | Cwhile(_, c1, _, c2) ->
    conflicts_c (conflicts_c (merge_class cf s2) c1) c2
and conflicts_c cf c =
  List.fold_left conflicts_i cf c


type conflicts = Sv.t Mv.t

let conflicts f =
  let ca = Sv.of_list f.f_args in
  let cr = Sv.of_list (List.map L.unloc f.f_ret) in
  let cf = merge_class Mv.empty ca in
  let cf = merge_class cf cr in
  conflicts_c cf f.f_body

type var_classes = conflicts * var Mv.t

let init_classes cf = cf, Mv.empty

let get_conflict (cf,_) x =
  Mv.find_default Sv.empty x cf

let rec get_repr m x =
  if Mv.mem x m then get_repr m (Mv.find x m)
  else x

let normalize_repr (_c,m) =
  Mv.mapi (fun x _ -> get_repr m x) m

exception SetSameConflict

let merge_class1 cf rx xc ry yc =
  (* ajoute x dans les conflits de y *)
  let add_conflict x y cf =
    Mv.modify_def Sv.empty y (Sv.add x) cf
  in
  let cf = Sv.fold (add_conflict rx) yc cf in
  let cf = Sv.fold (add_conflict ry) xc cf in
  let c = Sv.union xc yc in
  let cf = Mv.add rx c cf in
  let cf = Mv.add ry c cf in
  cf

(*
let pp_map fmt m =
  Mv.iter (fun v1 v2 ->
      Format.fprintf fmt "%a ----> %a@."
         (Printer.pp_var ~debug:true) v1 (Printer.pp_var ~debug:true) v2)
      m
 *)

let set_same (cf, m as cfm) x y =
  let rx = get_repr m x in
  let ry = get_repr m y in
  if V.equal rx ry then cfm
  else
    let xc = Mv.find_default Sv.empty rx cf in
    let yc = Mv.find_default Sv.empty ry cf in
    if Sv.mem rx yc then
      begin
(*        let pp_v = Printer.pp_var ~debug:true in
        Format.eprintf "map:@.%a@.@."
          pp_map m;
        Format.eprintf "x = %a --> %a; y = %a --> %a@."
           pp_v x pp_v rx pp_v y pp_v ry;
        Format.eprintf "rx = %a@."
           (Printer.pp_list " " pp_v) (Sv.elements xc);
        Format.eprintf "ry = %a@."
           (Printer.pp_list " " pp_v) (Sv.elements yc); *)
        raise SetSameConflict
      end;
    merge_class1 cf rx xc ry yc, Mv.add rx ry m
