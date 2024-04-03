open Utils
open Prog

(* Updates [s_o] to hold which variables are live before a write_lval. *)
let dep_lv s_o x =
  match x with
  | Lvar x -> Sv.remove (L.unloc x) s_o
  | _      -> vars_lv s_o x

let dep_lvs s_o xs =
  List.fold_left dep_lv s_o xs

let writev_lval s = function
  | Lnone _     -> s
  | Lvar x      -> Sv.add (L.unloc x) s
  | Lmem _      -> s
  | Laset(_, _, _, x, _)
  | Lasub(_, _, _, x, _) -> Sv.add (L.unloc x) s

let writev_lvals s lvs = List.fold_left writev_lval s lvs

(* When [weak] is true, the out live-set contains also the written variables. *)
let rec live_i weak i s_o =
  let s_i, s_o, d = live_d weak i.i_desc s_o in
  s_i, { i with i_desc = d; i_info = (s_i, s_o); }

and live_d weak d (s_o: Sv.t) =
  match d with
  | Cassgn(x, tg, ty, e) ->

    let s_i = Sv.union (vars_e e) (dep_lv s_o x) in
    let s_o =
      if weak then writev_lval s_o x
      else s_o in
    s_i, s_o, Cassgn(x, tg, ty, e)

  | Copn(xs,t,o,es) ->
    let s_i = Sv.union (vars_es es) (dep_lvs s_o xs) in
    let s_o =
     if weak
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

  | Ccall(xs,f,es) ->
    let s_i = Sv.union (vars_es es) (dep_lvs s_o xs) in
    s_i, (if weak then writev_lvals s_o xs else s_o), Ccall(xs,f,es)

  | Csyscall(xs,o,es) ->
    let s_i = Sv.union (vars_es es) (dep_lvs s_o xs) in
    s_i, (if weak then writev_lvals s_o xs else s_o), Csyscall(xs,o,es)

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

let iter_call_sites (cbf: L.i_loc -> funname -> lvals -> Sv.t * Sv.t -> unit)
                    (cbs: L.i_loc -> BinNums.positive Syscall_t.syscall_t -> lvals -> Sv.t * Sv.t -> unit)
                    (f: (Sv.t * Sv.t, 'asm) func) : unit =
  let rec iter_instr_r loc ii =
    function
    | (Cassgn _ | Copn _) -> ()
    | (Cif (_, s1, s2) | Cwhile (_, s1, _, s2)) -> iter_stmt s1; iter_stmt s2
    | Cfor (_, _, s) -> iter_stmt s
    | Ccall (xs, fn, _) ->
       cbf loc fn xs ii
    | Csyscall (xs, op, _) ->
       cbs loc op xs ii
  and iter_instr { i_loc ; i_info ; i_desc } = iter_instr_r i_loc i_info i_desc
  and iter_stmt s = List.iter iter_instr s in
  iter_stmt f.f_body

let pp_info fmt (s1, s2) =
  Format.fprintf fmt "before: %a; after %a@ "
    (pp_list " " (Printer.pp_var ~debug:true)) (Sv.elements s1)
    (pp_list " " (Printer.pp_var ~debug:true)) (Sv.elements s2)

let merge_class cf s =
  let add_conflict x cf =
    Mv.modify_def Sv.empty x (Sv.union (Sv.remove x s)) cf
  in
  Sv.fold add_conflict s cf

let rec conflicts_i cf i =
  let (s1, s2) = i.i_info in
  let cf = merge_class cf s1 in

  match i.i_desc with
  | Cassgn _ | Copn _ | Csyscall _ | Ccall _ ->
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
           (pp_list " " pp_v) (Sv.elements xc);
        Format.eprintf "ry = %a@."
           (pp_list " " pp_v) (Sv.elements yc); *)
        raise SetSameConflict
      end;
    merge_class1 cf rx xc ry yc, Mv.add rx ry m

let var_classes_merge cfm1 (_cf2, m2) =
  Mv.fold (fun x _ cfm ->
      let r = get_repr m2 x in
      set_same cfm x r
    ) m2 cfm1

let var_classes_incl (_cf1, m1) (_cf2, m2) =
  Mv.for_all (fun x y ->
      V.equal (get_repr m2 x) (get_repr m2 y)
    ) m1
