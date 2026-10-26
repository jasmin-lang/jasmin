open Utils
open Prog

(* The positions of the parameters and of the results of a function that are
   used. *)
type used = { params : bool array; res : bool array }

(* The variables that an l-value writes, as [vrv] computes them. *)
let written = function
  | Lvar x | Laset (_, _, _, x, _) | Lasub (_, _, _, x, _) -> Sv.singleton (L.unloc x)
  | Lnone _ | Lmem _ -> Sv.empty

(* An assignment or an operator whose destinations are dead, as [dead_code]
   removes it. *)
let is_dead tg s_o xs =
  tg <> E.AT_keep
  && List.for_all
       (fun x ->
         (match x with Lmem _ -> false | _ -> true)
         && Sv.is_empty (Sv.inter (written x) s_o))
       xs

let analyse ~(protect : ('info, 'asm) func -> var -> bool)
    (fds : ('info, 'asm) func list) =
  let tbl = Hf.create 17 in
  List.iter
    (fun fd ->
      let params = Array.of_list (List.map (protect fd) fd.f_args) in
      let res =
        Array.of_list (List.map (fun x -> protect fd (L.unloc x)) fd.f_ret)
      in
      Hf.add tbl fd.f_name { params; res })
    fds;
  let changed = ref false in
  let set a i =
    if not a.(i) then (
      a.(i) <- true;
      changed := true)
  in
  let rec live_i s_o i =
    match i.i_desc with
    | Cassgn (x, tg, _, e) ->
        if is_dead tg s_o [ x ] then s_o
        else Sv.union (vars_e e) (Liveness.dep_lvs s_o [ x ])
    | Copn (xs, tg, _, es) ->
        if is_dead tg s_o xs then s_o
        else Sv.union (vars_es es) (Liveness.dep_lvs s_o xs)
    | Csyscall (xs, _, es) -> Sv.union (vars_es es) (Liveness.dep_lvs s_o xs)
    | Cassert (_, a) -> Sv.union (vars_a a) s_o
    | Cif (e, c1, c2) ->
        Sv.union (vars_e e) (Sv.union (live_c s_o c1) (live_c s_o c2))
    | Cfor (x, (_, e1, e2), c) ->
        let rec loop s =
          let s' = Sv.remove (L.unloc x) (live_c s c) in
          if Sv.subset s' s then s else loop (Sv.union s s')
        in
        Sv.union (vars_es [ e1; e2 ]) (loop s_o)
    | Cwhile (_, c, e, _, c') ->
        let rec loop s =
          let s_i = live_c (Sv.union (vars_e e) s) c in
          let s_i' = live_c s_i c' in
          if Sv.subset s_i' s then s_i else loop (Sv.union s s_i')
        in
        loop s_o
    | Ccall (xs, f, es) -> (
        match Hf.find tbl f with
        | exception Not_found ->
            Sv.union (vars_es es) (Liveness.dep_lvs s_o xs)
        | u ->
            List.iteri
              (fun j x ->
                match x with
                | Lnone _ -> ()
                | Lvar y -> if Sv.mem (L.unloc y) s_o then set u.res j
                | Lmem _ | Laset _ | Lasub _ -> set u.res j)
              xs;
            let xs = List.filteri (fun j _ -> u.res.(j)) xs in
            let es = List.filteri (fun j _ -> u.params.(j)) es in
            Sv.union (vars_es es) (Liveness.dep_lvs s_o xs))
  and live_c s_o c = List.fold_right (fun i s -> live_i s i) c s_o in
  let live_fd fd =
    let u = Hf.find tbl fd.f_name in
    let s_o =
      List.fold_left2
        (fun s x b -> if b then Sv.add (L.unloc x) s else s)
        Sv.empty fd.f_ret (Array.to_list u.res)
    in
    let s_i = live_c s_o fd.f_body in
    List.iteri (fun i x -> if Sv.mem x s_i then set u.params i) fd.f_args
  in
  let rec fixpoint () =
    changed := false;
    List.iter live_fd fds;
    if !changed then fixpoint ()
  in
  fixpoint ();
  let keep a = if Array.for_all Fun.id a then None else Some (Array.to_list a) in
  fun fn ->
    match Hf.find tbl fn with
    | u -> (keep u.params, keep u.res)
    | exception Not_found -> (None, None)
