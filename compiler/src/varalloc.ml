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
  let init = Sv.of_list fd.f_args in
  let _, f_body = rm_uninitialized_c init fd.f_body in
  { fd with f_body }

let merge_class cf s = 
  let add_conflict x cf = 
    Mv.modify_opt x (fun s' -> Some (Sv.union (Sv.remove x s) (odfl Sv.empty s'))) cf
  in
  Sv.fold add_conflict s cf 

let writev_lval s = function
  | Lnone _     -> s 
  | Lvar x      -> Sv.add (L.unloc x) s
  | Lmem _      -> s
  | Laset(x, _) -> Sv.add (L.unloc x) s

let writev_lvals s lvs = List.fold_left writev_lval s lvs 

let rec conflicts_i cf i = 
  let (s1, s2) = i.i_info in
  let cf = merge_class cf s1 in
  
  match i.i_desc with
  | Cassgn (x,_,_) ->
    merge_class cf (writev_lval s2 x)
  | Copn (xs, _, _) | Ccall (_, xs, _, _) -> 
    merge_class cf (writev_lvals s2 xs)
  | Cblock c | Cfor( _, _, c) -> 
    conflicts_c (merge_class cf s2) c
  | Cif(_, c1, c2) | Cwhile(c1, _, c2) -> 
    conflicts_c (conflicts_c (merge_class cf s2) c1) c2
and conflicts_c cf c = 
  List.fold_left conflicts_i cf c
  
let alloc_stack_fd fd =
  Format.eprintf "variable allocation@.";
  (* collect all stack variables occuring in fd *)
  let vars = Sv.filter (fun v -> v.v_kind = Stack) (vars_fc fd) in
  let vars = Sv.elements vars in
  (* liveness analysis *)
  let fd' = live_init_fd fd in
  Format.eprintf "liveness done@.";
  (* compute the dependency graph *)
  let cf = conflicts_c Mv.empty fd'.f_body in
  let pp_var =  Printer.pp_var ~debug:true in
  Mv.iter (fun x s ->
      Format.eprintf "%a -> %a@."
        pp_var x (Printer.pp_list ", " pp_var) (Sv.elements s)) cf;
  Format.eprintf "dependency done@.";
  (* allocated variables *)
  let ma = ref Mv.empty in
  let alloc x = 
    let cx = Mv.find_default Sv.empty x cf in
    let test y = x.v_ty = y.v_ty && not (Sv.mem y cx) in
    let x' = List.find test vars in
    Format.eprintf "%a allocated in %a@." 
                   pp_var x pp_var x';
    ma := Mv.add x x' !ma in
  List.iter alloc vars;
  Format.eprintf "allocation done@.";
  vsubst_func !ma fd
