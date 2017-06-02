open Utils
open Prog
open Subst
open Liveness

(* ---------------------------------------------------------------------- *)

(* remove dependency of a stack array variable
   before its first initialisation *)

let init_lval init x =
  match x with
  | Lnone _     -> init
  | Lvar x      -> Sv.add (L.unloc x) init
  | Lmem _      -> init
  | Laset(x, _) -> Sv.add (L.unloc x) init

let init_lvals init xs = List.fold_left init_lval init xs

let rec rm_uninitialized_i init i =
  let (s1, s2) = i.i_info in
  let init',i_desc =
    match i.i_desc with
    | Cblock c ->
      let init', c = rm_uninitialized_c init c in
      init', Cblock c
    | Cassgn(x, _, _) ->
      init_lval init x, i.i_desc
    | Copn(xs, _, _) | Ccall(_, xs, _, _) ->
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
    | Cwhile(c1, e, c2) ->
      let init1, _ = rm_uninitialized_c init  c1 in
      let init2, _ = rm_uninitialized_c init1 c2 in
      let init1', c1 = rm_uninitialized_c init2  c1 in
      let init2', c2 = rm_uninitialized_c init1' c2 in
      assert (Sv.equal init2 init2');
      init2', Cwhile(c1, e, c2) in
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

let alloc_stack_fd fd =
  (* collect all stack variables occuring in fd *)
  let vars = Sv.filter (fun v -> v.v_kind = Stack) (vars_fc fd) in
  let vars = Sv.elements vars in
  (* liveness analysis *)
  let fd' = live_init_fd fd in
  let cf = conflicts fd' in

  Format.eprintf "liveness done@.";
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
  let cfm = ref (init_classes cf) in
  let alloc x =
    let cx = get_conflict !cfm x in
    let test y = x.v_ty = y.v_ty && not (Sv.mem y cx) && 
                   try ignore(set_same !cfm x y); true
                   with SetSameConflict -> false in
    let x' = List.find test vars in
    cfm := set_same !cfm x x' in
  List.iter alloc vars;
  vsubst_func (normalize_repr !cfm) fd

(* --------------------------------------------------------------------- *)

let is_same = function
  | AT_keep | AT_unroll -> false
  | AT_rename_arg | AT_rename_res | AT_phinode -> true

let set_same loc cfm x y =
  try set_same cfm x y
  with SetSameConflict ->
    hierror "at %a: cannot remove introduced assignment %a = %a"
       L.pp_loc loc
       (Printer.pp_var ~debug:true) x
       (Printer.pp_var ~debug:true) y

let rec same_i cfm i =
  match i.i_desc with
  | Cassgn (Lvar x, tag ,Pvar y) when is_same tag && kind_i x = kind_i y ->
    set_same i.i_loc cfm (L.unloc x) (L.unloc y)
  | Cassgn (_, tag, _) when is_same tag ->
    hierror "at %a: cannot remove assignment %a@\nintroduced by inlining"
        L.pp_loc i.i_loc
        (Printer.pp_instr ~debug:true) i
  | Cassgn _                            -> cfm
  | Copn (_, _, _) | Ccall (_, _, _, _) -> cfm
  | Cblock c       | Cfor( _, _, c)     -> same_c cfm c
  | Cif(_, c1, c2) | Cwhile(c1, _, c2)  -> same_c (same_c cfm c1) c2

and same_c cfm c = List.fold_left same_i cfm c

let merge_var_inline_fd fd =
(*  Format.eprintf "merge variables introduced by inlining@."; *)
  (* liveness analysis *)
  let fd' = live_fd false fd in
(*  Format.eprintf "liveness done@.";
  let pp_info fmt (c1, c2) =
    let pp_set fmt c = 
      Format.fprintf fmt "{%a}" 
        (Printer.pp_list ", " (Printer.pp_var ~debug:true)) (Sv.elements c) in
    Format.fprintf fmt "%a%a" pp_set c1 pp_set c2 in
  Format.eprintf "%a" (Printer.pp_ifunc ~debug:true pp_info) fd';
 *)

  (* compute the dependency graph *)
  let cf = conflicts fd' in
(*  let pp_var =  Printer.pp_var ~debug:true in
  Mv.iter (fun x s ->
      Format.eprintf "%a -> %a@."
        pp_var x (Printer.pp_list ", " pp_var) (Sv.elements s)) cf;
  Format.eprintf "dependency done@."; *)
  (* compute the set of variables that should be merged *)
  let cfm = same_c (init_classes cf) fd.f_body in
  let ma = normalize_repr cfm in
(*  Format.eprintf "assignment done @.";
  Mv.iter (fun x y ->
      Format.eprintf "%a -> %a@." pp_var x pp_var y) ma;
  Format.eprintf "merge variables done@."; *)
  vsubst_func ma fd

let merge_var_inline_fd fd =
  Regalloc.split_live_ranges fd
