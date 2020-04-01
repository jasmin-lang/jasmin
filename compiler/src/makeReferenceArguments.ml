open Utils
open Prog

let is_reg_ptr_expr e = 
  match e with
  | Pvar x -> is_reg_ptr_kind (L.unloc x.gv).v_kind
  | _      -> hierror "makeReferenceArguments: Some arguments are not variable" 

let is_reg_ptr_lval x = 
  match x with
  | Lvar x -> is_reg_ptr_kind (L.unloc x).v_kind
  | _      -> hierror "makeReferenceArguments: Some returns are not variable"

let update_func (get_sig: funname -> var list * var_i list) (f: 'info func) : 'info func =
  let rec update_instr_r =
    function
    | (Cassgn _ | Copn _) as i -> [i]
    | Cif (e, s1, s2) -> [Cif(e, update_stmt s1, update_stmt s2)]
    | Cfor(n, r, s) -> [Cfor(n, r, update_stmt s)]
    | Cwhile(a, s1, e, s2) -> [Cwhile(a, update_stmt s1, e, update_stmt s2)]
    | Ccall(ii, xs, fn, es) ->
       let params, returns = get_sig fn in
       let prologue, es =
         List.fold_left2 (fun (acc, es) p e ->
             if is_reg_ptr_kind p.v_kind && not (is_reg_ptr_expr e)
             then
               let gv = V.clone p |> L.(mk_loc _dummy) in
               Cassgn (Lvar gv, AT_none, p.v_ty, e) :: acc, 
               Pvar { gs = E.Slocal ; gv } :: es
             else acc, e :: es
           ) ([], []) params es
       in
       let epilogue, xs =
         List.fold_left2 (fun (acc, xs) p x ->
             let p = L.unloc p in
             if is_reg_ptr_kind p.v_kind && not (is_reg_ptr_lval x)
             then
               let gv = V.clone p |> L.(mk_loc _dummy) in
               Cassgn (x, AT_none, p.v_ty, Pvar (gkvar gv)) :: acc, 
               Lvar gv :: xs
             else acc, x :: xs
           ) ([], []) returns xs
       in
       epilogue @ Ccall(ii, List.rev xs, fn, List.rev es) :: prologue
  and update_instr i =
    List.rev_map (fun i_desc -> { i with i_desc })
      (update_instr_r i.i_desc)
  and update_stmt s = List.map update_instr s |> List.flatten
  in
  { f with f_body = update_stmt f.f_body }

let doit (p: 'info prog) : 'info prog =
  let (globs, funcs) = p in
  let get_sig =
    let tbl : (var list * var_i list) Hf.t = Hf.create 17 in
    List.iter (fun f -> Hf.add tbl f.f_name (f.f_args, f.f_ret)) funcs;
    fun fn -> Hf.find tbl fn
  in
  let funcs = List.map (update_func get_sig) funcs in
  (globs, funcs)
