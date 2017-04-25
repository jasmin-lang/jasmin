open Prog

let read_lv s = function
  | Lvar _ -> s
  | x      -> rvars_lv s x

let dep_lv s_o x =
  match x with
  | Lvar x -> Sv.remove (L.unloc x) s_o
  | _      -> rvars_lv s_o x

(* Not sure it is correct in same variable occur multiple time in
   xs *)
let dep_lvs s_o xs =
  List.fold_left dep_lv s_o xs

let rec live_i i s_o =
  let s_i, d = live_d i.i_desc s_o in
  s_i, { i_desc = d; i_loc = i.i_loc; i_info = (s_i, s_o); }

and live_d d (s_o:Sv.t) =
  match d with
  | Cblock c ->
    let s_i, c = live_c c s_o in
    s_i, Cblock c

  | Cassgn(x,t,e) ->
    let s_i = Sv.union (vars_e e) (dep_lv s_o x) in
    s_i, Cassgn(x,t,e)

  | Copn(xs,o,es) ->
    let s_i = Sv.union (vars_es es) (dep_lvs s_o xs) in
    s_i, Copn(xs,o,es)

  | Cif(e,c1,c2) ->
    let s1, c1 = live_c c1 s_o in
    let s2, c2 = live_c c2 s_o in
    (Sv.union (vars_e e) (Sv.union s1 s2), Cif(e,c1,c2))

  | Cfor _ -> assert false (* Should have been removed before *)

  | Cwhile(e,c) ->
    let rec loop s_o =
      let s_i, c = live_c c s_o in
      if Sv.subset s_i s_o then s_o, c
      else loop (Sv.union s_i s_o) in
    let s_i, c = loop (Sv.union (vars_e e) s_o) in
    s_i, Cwhile(e,c)

  | Ccall(ii,xs,f,es) ->
    let s_i = Sv.union (vars_es es) (dep_lvs s_o xs) in
    s_i, Ccall(ii,xs,f,es)

and live_c c s_o =
  let s_o = ref s_o in
  let doi i =
    let s_i, i = live_i i !s_o in
    s_o := s_i;
    i in
  let c = List.map doi c in
  !s_o, c


let live_fd fd =
  let s_o = Sv.of_list (List.map L.unloc fd.f_ret) in
  let _, c = live_c fd.f_body s_o in
  {
    f_cc   = fd.f_cc  ;
    f_name = fd.f_name;
    f_args = fd.f_args;
    f_body = c;
    f_ret  = fd.f_ret ;
  }

let liveness prog = List.map live_fd prog
