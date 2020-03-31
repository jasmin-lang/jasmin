open Utils
open Prog

let update_func (get_sig: funname -> var list) (f: 'info func) : 'info func =
  let rec update_instr_r =
    function
    | (Cassgn _ | Copn _) as i -> [i]
    | Cif (e, s1, s2) -> [Cif(e, update_stmt s1, update_stmt s2)]
    | Cfor(n, r, s) -> [Cfor(n, r, update_stmt s)]
    | Cwhile(a, s1, e, s2) -> [Cwhile(a, update_stmt s1, e, update_stmt s2)]
    | Ccall(ii, xs, fn, es) ->
       let params = get_sig fn in
       let prologue, es =
         List.fold_left2 (fun (acc, es) p e ->
             if is_reg_ptr_kind p.v_kind
             then
               (* TODO: don’t do it if e is already a var *)
               let gv = V.clone p |> L.(mk_loc _dummy) in
               Cassgn (Lvar gv, AT_none, p.v_ty, e) :: acc, Pvar { gs = E.Slocal ; gv } :: es
             else acc, e :: es
           ) ([], []) params es
       in
       Ccall(ii, xs, fn, List.rev es) :: prologue
  and update_instr i =
    List.rev_map (fun i_desc -> { i with i_desc })
      (update_instr_r i.i_desc)
  and update_stmt s = List.map update_instr s |> List.flatten
  in
  { f with f_body = update_stmt f.f_body }

let doit (p: 'info prog) : 'info prog =
  let (globs, funcs) = p in
  let get_sig =
    let tbl : var list Hf.t = Hf.create 17 in
    List.iter (fun f -> Hf.add tbl f.f_name f.f_args) funcs;
    fun fn -> Hf.find tbl fn
  in
  let funcs = List.map (update_func get_sig) funcs in
  (globs, funcs)
