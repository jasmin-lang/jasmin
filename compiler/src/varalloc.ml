open Utils
open Prog
open Subst
open Liveness

(* ---------------------------------------------------------------------- *)

(* remove dependency of a stack array variable
   before its first initialisation *)

let init_lval init x =
  match x with
  | Lnone _        -> init
  | Lvar x         -> Sv.add (L.unloc x) init
  | Lmem _         -> init
  | Laset(_, _, x, _) -> Sv.add (L.unloc x) init
  | Lasub(_,_,_,x,_)  -> Sv.add (L.unloc x) init

let init_lvals init xs = List.fold_left init_lval init xs

let rec rm_uninitialized_i init i =
  let (s1, s2) = i.i_info in
  let init',i_desc =
    match i.i_desc with
    | Cassgn(x, _, _, _) ->
      init_lval init x, i.i_desc
    | Copn(xs, _, _, _) | Ccall(_, xs, _, _) ->
      init_lvals init xs, i.i_desc
    | Cif(e, c1, c2) ->
      let init1, c1 = rm_uninitialized_c init c1 in
      let init2, c2 = rm_uninitialized_c init c2 in
      Sv.union init1 init2, Cif(e, c1, c2)
    | Cfor(x, d, c) ->
      let init', _ = rm_uninitialized_c init c in
      let init'', c = rm_uninitialized_c init' c in
      assert (Sv.equal init' init'');
      init', Cfor(x, d, c)
    | Cwhile(a, c1, e, c2) ->
      let init1, _ = rm_uninitialized_c init  c1 in
      let init2, _ = rm_uninitialized_c init1 c2 in
      let init1', c1 = rm_uninitialized_c init2  c1 in
      let init2', c2 = rm_uninitialized_c init1' c2 in
      assert (Sv.equal init2 init2');
      init2', Cwhile(a, c1, e, c2) in
  init', {i with i_desc;
          i_info = Sv.inter s1 init, Sv.inter s2 init' }

and rm_uninitialized_c init c =
  let init', r =
    List.fold_left (fun (init,r) i ->
      let init', i = rm_uninitialized_i init i in
      init', i::r) (init, []) c in
  init', List.rev r

let live_init_fd fd =
  let fd = live_fd true fd in
  let init = Sv.of_list fd.f_args in
  let _, f_body = rm_uninitialized_c init fd.f_body in
  { fd with f_body } 

type pointsto = Sv.t Mv.t

let expr_pointsto pt =
  function
  | Pvar x | Psub (_,_,_,x,_) ->
     let x = L.unloc x.gv in
     if is_ptr x.v_kind
     then Mv.find_default Sv.empty x pt
     else Sv.singleton x
  | Parr_init _ -> Sv.empty
  | e -> hierror "expr_pointsto: %a" (Printer.pp_expr ~debug:true) e

let pointsto_merge pt1 pt2 =
  Mv.merge (fun _x o1 o2 ->
      let s1 = odfl Sv.empty o1 in
      let s2 = odfl Sv.empty o2 in
      Some (Sv.union s1 s2)
    ) pt1 pt2

let merge_aliases_merge (cf1, pt1) (cf2, pt2) =
  (var_classes_merge cf1 cf2, pointsto_merge pt1 pt2)

(* p ≤ merge p q *)
let pointsto_incl pt1 pt2 =
  Mv.for_all (fun x s1 ->
      let s2 = Mv.find_default Sv.empty x pt2 in
      Sv.subset s1 s2
    ) pt1

let merge_aliases_incl (cf1, pt1) (cf2, pt2) =
  var_classes_incl cf1 cf2 && pointsto_incl pt1 pt2

let set_same_all cf x s =
  Sv.fold (fun y cf -> set_same cf x y) s cf

let merge_aliases_assgn ((cf, pt) as acc) lv e =
  match lv with
  | Lvar x when is_ptr (L.unloc x).v_kind ->
     (cf, Mv.add (L.unloc x) (expr_pointsto pt e) pt)
  | Lvar x when is_stack_array x && is_var e ->
     (set_same_all cf (L.unloc x) (expr_pointsto pt e), pt)
  | _ -> acc

let rec merge_aliases_instr get_fun acc i =
  match i .i_desc with
  | Cassgn (x, _, _, e) -> merge_aliases_assgn acc x e
  | Ccall (_, xs, fn, es) ->
     let ra =
       let f = get_fun fn in
       match f.f_cc with
       | Subroutine { returned_params } -> returned_params
       | (Internal | Export) -> assert false
     in
     List.fold_left2 (fun acc oi x ->
         match oi with
         | None -> acc
         | Some i -> merge_aliases_assgn acc x (List.nth es i))
       acc ra xs
  | Copn _ -> acc
  | Cfor _ -> assert false
  | Cif (_, s1, s2) ->
     let r1 = merge_aliases_stmt get_fun acc s1 in
     let r2 = merge_aliases_stmt get_fun acc s2 in
     merge_aliases_merge r1 r2
  | Cwhile (_, s1, _, s2) ->
     (* s1 ; while e do { s2 ; s1 } *)
     let rec loop acc =
       let r1 = merge_aliases_stmt get_fun acc s1 in
       let r2 = merge_aliases_stmt get_fun r1 s2 in
       if merge_aliases_incl r2 acc
       then r1
       else loop (merge_aliases_merge acc r2)
     in loop acc
  and merge_aliases_stmt get_fun acc s =
    List.fold_left (merge_aliases_instr get_fun) acc s

let merge_aliases get_fun (cf: Liveness.var_classes) (fd: _ Prog.func) : Liveness.var_classes =
  let pt : pointsto = Mv.empty in
  merge_aliases_stmt get_fun (cf, pt) fd.f_body
  |> fst

let alloc_stack_fd get_fun fd =
  (* collect all stack variables occuring in fd *)
  let vars = Sv.filter is_stack_var (vars_fc fd) in
  let vars = Sv.elements vars in
  (* liveness analysis *)
  let fd' = live_init_fd fd in
  let cf = conflicts fd' in

(*  Format.eprintf "liveness done@."; *)
(*  let pp_info fmt (c1, c2) =
    let pp_set fmt c = 
      Format.fprintf fmt "{%a}" 
        (Printer.pp_list ", " (Printer.pp_var ~debug:true)) (Sv.elements c) in
    Format.fprintf fmt "%a%a" pp_set c1 pp_set c2 in
  Format.eprintf "%a" (Printer.pp_ifunc ~debug:true pp_info) fd';
  let pp_var =  Printer.pp_var ~debug:true in
  Mv.iter (fun x s ->
      Format.eprintf "%a -> %a@."
        pp_var x (Printer.pp_list ", " pp_var) (Sv.elements s)) cf;
  Format.eprintf "dependency done@."; *)

  (* allocated variables *)
  let cfm = init_classes cf in
  let cfm = merge_aliases get_fun cfm fd in
  let cfm = ref cfm in
  let alloc x =
    let cx = get_conflict !cfm x in
    let test y = x.v_ty = y.v_ty && x.v_kind = y.v_kind && not (Sv.mem y cx) && 
                   try ignore(set_same !cfm x y); true
                   with SetSameConflict -> false in
    let x' = List.find test vars in
    cfm := set_same !cfm x x' in
  List.iter alloc vars;
  vsubst_func (normalize_repr !cfm) fd

