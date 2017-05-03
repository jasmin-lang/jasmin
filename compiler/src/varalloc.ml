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
  let fd = live_fd fd in
(*  Format.eprintf "liveness done@.";
  Format.eprintf "%a@." (Printer.pp_ifunc ~debug:true pp_info) fd; *)
  let init = Sv.of_list fd.f_args in
  let _, f_body = rm_uninitialized_c init fd.f_body in
  let fd = { fd with f_body } in
(*  Format.eprintf "after rm uninitialized @.";
  Format.eprintf "%a@." (Printer.pp_ifunc ~debug:true pp_info) fd; *)
  fd

let alloc_stack_fd fd =
  (* collect all stack variables occuring in fd *)
  let vars = Sv.filter (fun v -> v.v_kind = Stack) (vars_fc fd) in
  let vars = Sv.elements vars in
  (* liveness analysis *)
  let fd' = live_init_fd fd in
(*  Format.eprintf "liveness done@."; *)
  (* compute the dependency graph *)
  let cf = conflicts fd' in
(*  let pp_var =  Printer.pp_var ~debug:true in
  Mv.iter (fun x s ->
      Format.eprintf "%a -> %a@."
        pp_var x (Printer.pp_list ", " pp_var) (Sv.elements s)) cf;
  Format.eprintf "dependency done@."; *)
  (* allocated variables *)
  let ma = ref Mv.empty in
  let alloc x =
    let cx = Mv.find_default Sv.empty x cf in
    let test y = x.v_ty = y.v_ty && not (Sv.mem y cx) in
    let x' = List.find test vars in
(*    Format.eprintf "%a allocated in %a@."
                   pp_var x pp_var x'; *)
    ma := Mv.add x x' !ma in
  List.iter alloc vars;
(*  Format.eprintf "allocation done@."; *)
  vsubst_func !ma fd

(* --------------------------------------------------------------------- *)

let is_same = function
  | AT_keep | AT_unroll -> false
  | AT_rename_arg | AT_rename_res -> true

let rec get_repr m x =
  if Mv.mem x m then get_repr m (Mv.find x m)
  else x

let normalize_repr m =
  Mv.mapi (fun x _ -> get_repr m x) m

let set_same loc (cf, m as cfm) x y =
  let rx = get_repr m (L.unloc x) in
  let ry = get_repr m (L.unloc y) in
  if V.equal rx ry then cfm
  else
    let xc = Mv.find_default Sv.empty rx cf in
    let yc = Mv.find_default Sv.empty ry cf in
    if Sv.mem ry xc then
      hierror "at %a: cannot remove introduced assignment %a = %a"
        L.pp_loc loc
        (Printer.pp_var ~debug:true) (L.unloc x)
        (Printer.pp_var ~debug:true) (L.unloc y);
(*    Format.eprintf "alloc %a in %a@."
     (Printer.pp_var ~debug:true) rx (Printer.pp_var ~debug:true) ry; *)
    merge_class cf (Sv.union xc yc), Mv.add rx ry m



let rec same_i cfm i =
  match i.i_desc with
  | Cassgn (Lvar x, tag ,Pvar y) when is_same tag && kind_i x = kind_i y ->
    set_same i.i_loc cfm x y
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
  let fd' = live_fd fd in
(*  Format.eprintf "liveness done@."; *)
  (* compute the dependency graph *)
  let cf = conflicts fd' in
(*  let pp_var =  Printer.pp_var ~debug:true in
  Mv.iter (fun x s ->
      Format.eprintf "%a -> %a@."
        pp_var x (Printer.pp_list ", " pp_var) (Sv.elements s)) cf;
  Format.eprintf "dependency done@."; *)
  (* compute the set of variables that should be merged *)
  let (_,ma) = same_c (cf,Mv.empty) fd.f_body in
  let ma = normalize_repr ma in
(*  Format.eprintf "assignment done @.";
  Mv.iter (fun x y ->
      Format.eprintf "%a -> %a@." pp_var x pp_var y) ma;
  Format.eprintf "merge variables done@."; *)
  vsubst_func ma fd

