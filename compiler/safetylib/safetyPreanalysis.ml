open Jasmin
open Utils
open Prog

open SafetyUtils

(*---------------------------------------------------------------*)
(* Unique Variable Names *)
      
(* Information attached to instructions. *)
type minfo = { i_instr_number : int; }

module MkUniq : sig

  val mk_uniq : (unit, 'asm) func -> (unit, 'asm) prog -> ((minfo, 'asm) func * (minfo, 'asm) prog)

end = struct
  let uniq_i_nb =
    let cpt = ref 0 in
    (fun () ->
      let r = !cpt in
      incr cpt;
      r)
  
  let ht_uniq = Hashtbl.create ~random:false 16

  let htv = Hashtbl.create ~random:false 16

  let rec mk_gv v = v ^ "##g"

  and mk_glob fn ((x,value) : global_decl) = (mk_v fn x, value)

  and mk_globs fn (globs : global_decl list) = List.map (mk_glob fn) globs

  and mk_f f_decl =
    { f_decl with
      f_args = List.map (mk_v f_decl.f_name.fn_name) f_decl.f_args;
      f_body = mk_stmt f_decl.f_name.fn_name f_decl.f_body;
      f_ret = List.map (mk_v_loc f_decl.f_name.fn_name) f_decl.f_ret }

  and mk_v fn v =
    let short_name v = v.v_name ^ "." ^ (string_of_uid v.v_id) in
    let long_name v =
      if Config.sc_var_append_fun_name ()
      then (short_name v) ^ "#" ^ fn
      else short_name v
    in

      if Hashtbl.mem htv (short_name v, fn) then
        Hashtbl.find htv (short_name v, fn)
      else if Hashtbl.mem ht_uniq v.v_name then
        let nv = V.mk (long_name v) v.v_kind v.v_ty v.v_dloc v.v_annot in
        let () = Hashtbl.add htv (short_name v, fn) nv in
        nv
      else
        let () = Hashtbl.add ht_uniq v.v_name () in
        let () = Hashtbl.add htv (short_name v, fn) v in
        v

  and mk_v_loc fn v = L.mk_loc (L.loc v) (mk_v fn (L.unloc v))

  and mk_gvar fn v = { gv = mk_v_loc fn v.gv; gs = v.gs; }

  and mk_lval fn lv = match lv with
    | Lnone _ -> lv
    | Lvar v -> Lvar (mk_v_loc fn v)
    | Lmem (al, ws,ty,e) -> Lmem (al, ws, mk_v_loc fn ty, mk_expr fn e)
    | Laset (al,acc,ws,v,e) -> Laset (al,acc,ws, mk_v_loc fn v, mk_expr fn e)
    | Lasub (acc,ws,len,v,e) -> Lasub (acc,ws,len, mk_v_loc fn v, mk_expr fn e)

  and mk_range fn (dir, e1, e2) = (dir, mk_expr fn e1, mk_expr fn e2)

  and mk_lvals fn lvs = List.map (mk_lval fn) lvs

  and mk_instr fn st = {
      st with
      i_desc = mk_instr_r fn st.i_desc;
      i_info = { i_instr_number = uniq_i_nb ();};
    }

  and mk_instr_r fn st = match st with
    | Cassgn (lv, tag, ty, e) ->
      Cassgn (mk_lval fn lv, tag, ty, mk_expr fn e)
    | Copn (lvls, tag, opn, exprs) ->
      Copn (mk_lvals fn lvls, tag, opn, mk_exprs fn exprs)
    | Csyscall (lvls, o, exprs) ->
        Csyscall(mk_lvals fn lvls, o, mk_exprs fn exprs)
    | Cif (e, st, st') ->
      Cif (mk_expr fn e, mk_stmt fn st, mk_stmt fn st')
    | Cfor (v, r, st) ->
      Cfor (mk_v_loc fn v, mk_range fn r, mk_stmt fn st)
    | Ccall (lvs, c_fn, es) ->
      Ccall (mk_lvals fn lvs, c_fn, mk_exprs fn es)
    | Cwhile (a, st1, e, st2) ->
      Cwhile (a, mk_stmt fn st1, mk_expr fn e, mk_stmt fn st2)

  and mk_stmt fn instrs = List.map (mk_instr fn) instrs

  and mk_expr fn expr = match expr with
    | Pconst _ | Pbool _ | Parr_init _ -> expr
    | Pvar v -> Pvar (mk_gvar fn v)
    | Pget (al, acc, ws, v, e) -> Pget (al, acc, ws, mk_gvar fn v, mk_expr fn e)
    | Psub (acc, ws, len, v, e) ->
      Psub (acc, ws, len, mk_gvar fn v, mk_expr fn e)
    | Pload (al, ws, v, e) -> Pload (al, ws, mk_v_loc fn v, mk_expr fn e)
    | Papp1 (op, e) -> Papp1 (op, mk_expr fn e)
    | Papp2 (op, e1, e2) -> Papp2 (op, mk_expr fn e1, mk_expr fn e2)
    | PappN (op,es) -> PappN (op, List.map (mk_expr fn) es)
    | Pif (ty, e, el, er)  ->
      Pif (ty, mk_expr fn e, mk_expr fn el, mk_expr fn er)

  and mk_exprs fn exprs = List.map (mk_expr fn) exprs

  let mk_uniq main_decl ((glob_decls, fun_decls) : (unit, 'asm) prog) =
    Hashtbl.clear ht_uniq;
    Hashtbl.clear htv;

    let m_decl = mk_f main_decl in
    (m_decl,
     (* We use the main function to prefix global variables. *)
     (mk_globs main_decl.f_name.fn_name glob_decls,
      List.map mk_f fun_decls))

end


(****************)
(* Pre Analysis *)
(****************)

module Pa : sig

  type dp = Sv.t Mv.t

  type cfg = Sf.t Mf.t

  (* - pa_dp: for each variable, contains the set of variables that can modify
              it. Some dependencies are ignored depending on some heuristic.
     - pa_cfg: control-flow graph, where an entry f -> [f1;...;fn] means that 
     f calls f1, ..., fn *)
  type pa_res = { pa_dp : dp;
                  pa_cfg : cfg;
                  while_vars : Sv.t;
                  if_conds : expr list }

  val dp_v : dp -> var -> Sv.t
  val pa_make : ('info, X86_extra.x86_extended_op) func -> ('info, X86_extra.x86_extended_op) prog option -> pa_res

  val print_dp  : Format.formatter -> dp -> unit
  val print_cfg : Format.formatter -> cfg -> unit

end = struct
  (* For each variable, we compute the set of variables that can modify it.
     Some dependencies are ignored depending on some heuristic we have. *)
  type dp = Sv.t Mv.t

  type cfg = Sf.t Mf.t

  type pa_res = { pa_dp : dp;
                  pa_cfg : cfg;
                  while_vars : Sv.t;
                  if_conds : expr list }

  let dp_v dp v = Mv.find_default Sv.empty v dp

  let add_dep dp v v' ct =
    Mv.add v (Sv.union (Sv.singleton v') (Sv.union ct (dp_v dp v))) dp

  let cfg_v cfg f = Mf.find_default Sf.empty f cfg

  let add_call cfg f f' =
    Mf.add f (Sf.union (Sf.singleton f') (cfg_v cfg f)) cfg

  (* Dependency heuristic for variable assignment *)
  let rec app_expr dp v e ct = match e with
    | Pconst _ -> dp
    | Pbool _ -> dp
    | Parr_init _ -> dp
    | Pvar v' -> begin match v'.gs with
        | Expr.Sglob  -> dp (* We ignore global variables  *)
        | Expr.Slocal -> match (L.unloc v'.gv).v_ty with
          | Bty _ -> add_dep dp v (L.unloc v'.gv) ct
          | Arr _ -> dp end

    | Pget _ -> dp  (* We ignore array loads  *)
    | Psub _ -> dp  (* We ignore sub-array copies  *)

    (* We ignore loads for v, but we compute dependencies of v' in ei *)
    | Pload (_, _,v',ei) -> app_expr dp (L.unloc v') ei ct

    | Papp1 (_,e1) -> app_expr dp v e1 ct
    | Papp2  (_,e1,e2) -> app_expr (app_expr dp v e1 ct) v e2 ct
    | PappN (_,es) -> List.fold_left (fun dp e -> app_expr dp v e ct) dp es
    | Pif (_,b,e1,e2) ->
      app_expr (app_expr (app_expr dp v b ct) v e1 ct) v e2 ct

  (* State while building the dependency graph:
     - dp : dependency graph
     - cfg : control-flow graph: 
             f -> [f1;...;fn] means that f calls f1, ..., fn
     - f_done : already analized functions
     - ct : variables in the context (for an example, look at the Cif case) *)
  type pa_st = { dp : dp;
                 cfg : cfg;
                 while_vars : Sv.t;
                 if_conds : expr list;
                 f_done : Ss.t;
                 ct : Sv.t }

  (* Compute the list of variables occuring in an expression, while updating
     the state during memory loads. *)
  let expr_vars st e =
    let rec aux (acc,st) = function
      | Pconst _ | Pbool _ | Parr_init _ | Pget _ | Psub _ -> acc, st

      | Pvar v' ->
        begin
          match v'.gs with
          | Expr.Sglob -> acc, st
          | Expr.Slocal -> match (L.unloc v'.gv).v_ty with
            | Bty _ -> (L.unloc v'.gv) :: acc, st
            | Arr _ -> acc, st
        end

      (* We ignore loads for v, but we compute dependencies of v' in ei *)
      | Pload (_, _,v',ei) ->
        let dp = app_expr st.dp (L.unloc v') ei st.ct in
        acc, { st with dp = dp }

      | Papp1 (_,e1) -> aux (acc,st) e1
      | Papp2  (_,e1,e2) -> aux (aux (acc,st) e1) e2
      | PappN (_,es) -> List.fold_left aux (acc,st) es
      | Pif (_,b,e1,e2) -> aux (aux (aux (acc,st) e1) e2) b in

    aux ([],st) e

  (* Compute the list of variables occuring in an expression. *)
  let expr_vars_smpl acc e =
    let aux_v acc v = match (L.unloc v).v_ty with
        | Bty _ -> (L.unloc v) :: acc
        | Arr _ -> acc in
    
    let aux_gv acc v = match v.gs with
      | Expr.Sglob -> acc
      | Expr.Slocal -> aux_v acc v.gv in
    
    let rec aux acc = function
      | Pconst _ | Pbool _ | Parr_init _ | Pget _ | Psub _ -> acc

      | Pvar v' -> aux_gv acc v'
      (* We ignore loads for v, but we compute dependencies of v' in ei *)
      | Pload (_, _,v',ei) -> aux (aux_v acc v') ei

      | Papp1 (_,e1) -> aux acc e1
      | Papp2  (_,e1,e2) -> aux (aux acc e1) e2
      | PappN (_,es) -> List.fold_left aux acc es
      | Pif (_,b,e1,e2) -> aux (aux (aux acc e1) e2) b in

    aux acc e

  let st_merge st1 st2 ct =
    let mdp = Mv.merge (fun _ osv1 osv2 ->
        let sv1,sv2 = Option.default Sv.empty osv1, Option.default Sv.empty osv2 in
        Sv.union sv1 sv2 |> Option.some) in
    let mcfg = Mf.merge (fun _ osf1 osf2 -> 
        let sf1,sf2 = Option.default Sf.empty osf1, Option.default Sf.empty osf2 in
        Sf.union sf1 sf2 |> Option.some) in
    { dp = mdp st1.dp st2.dp;
      cfg = mcfg st1.cfg st2.cfg;
      while_vars = Sv.union st1.while_vars st2.while_vars;
      f_done = Ss.union st1.f_done st2.f_done;
      if_conds = List.rev_append st1.if_conds st2.if_conds;
      ct = ct }

  let set_ct ct st = { st with ct = ct }

  let rec find_arg v vs es = match vs, es with
    | [],_ | _, [] -> assert false
    | v' :: vs', e' :: es' -> if v' = v then e' else find_arg v vs' es'

  let pa_expr st v e = { st with dp = app_expr st.dp v e st.ct }

  let pa_lv st lv e = match lv with
    | Lnone _ | Laset _ | Lasub _ -> st   (* We ignore array stores *)
    | Lvar v -> pa_expr st (L.unloc v) e

    (* For memory stores, we are only interested in v and ei *)
    | Lmem (_, _, v, ei) -> pa_expr st (L.unloc v) ei


  let rec flag_mem_lvs v = function
    | [] -> false
    | Lnone _ :: t | Lmem _ :: t | Laset _ :: t | Lasub _ :: t -> flag_mem_lvs v t
    | Lvar v' :: t -> v = L.unloc v' || flag_mem_lvs v t

  let print_flag_set_from v r loc =
    debug(fun () -> Format.eprintf "flag %a set from %a (at %a)@."
             (Printer.pp_var ~debug:false) v
             (pp_list (Printer.pp_var ~debug:false)) r
             L.pp_sloc loc)
       
  exception Flag_set_from_failure
  (* Try to find the left variable of the last assignment(s) where the flag 
     v was set. *)
  let rec pa_flag_setfrom v = function
    | [] -> None
    | i :: t -> let i_opt = pa_flag_setfrom_i v i in
      if Option.is_none i_opt then pa_flag_setfrom v t else i_opt
  
  and pa_flag_setfrom_i v i = match i.i_desc with
    | Cassgn _ -> None

    | Copn (lvs, _, Sopn.Oasm (Arch_extra.BaseOp (_, X86_instr_decl.CMP _)), es) ->
      if flag_mem_lvs v lvs then
        let rs = List.fold_left expr_vars_smpl [] es in
        print_flag_set_from v rs i.i_loc.L.base_loc;
        Some rs
      else None

    | Copn (lvs, _, _, _) ->
      if flag_mem_lvs v lvs then
        match List.last lvs with
        | Lnone _ -> raise Flag_set_from_failure
        | Lvar r ->
          let ru = L.unloc r in
          print_flag_set_from v [ru] i.i_loc.L.base_loc;
          Some [ru]
        | _ -> assert false
      else None

    | Cif (_, c1, c2) ->
      begin match pa_flag_setfrom v c1, pa_flag_setfrom v c2 with
        | None, None -> None
        | Some r1, Some r2 ->
          if r1 = r2 then Some r1 else raise Flag_set_from_failure
        | None, Some _ | Some _, None -> raise Flag_set_from_failure end

    | Cfor (_, _, c) ->
      pa_flag_setfrom v (List.rev c)

    | Cwhile (_, c1, _, c2) ->
      pa_flag_setfrom v (List.rev_append c1 (List.rev c2))
        
    | Ccall (lvs, _, _) | Csyscall(lvs, _, _) ->
      if flag_mem_lvs v lvs then raise Flag_set_from_failure else None
      
  let rec pa_instr fn (prog : ('info, 'asm) prog option) st instr =
    match instr.i_desc with
    | Cassgn (lv, _, _, e) -> pa_lv st lv e

    | Copn (lvs, _, _, es) | Csyscall(lvs, _, es) -> List.fold_left (fun st lv ->
        List.fold_left (fun st e -> pa_lv st lv e) st es) st lvs

    | Cif (b, c1, c2) ->
      let vs,st = expr_vars st b in 
      let st = { st with if_conds = b :: st.if_conds } in

      let st' =
        if Config.sc_flow_dep () then
          { st with ct = Sv.union st.ct (Sv.of_list vs) }
        else st in

      (* Note that we reset the context after the merge *)
      st_merge (pa_stmt fn prog st' c1) (pa_stmt fn prog st' c2) st.ct

    | Cfor (_, _, c) ->
      (* We ignore the loop index, since we do not use widening for loops. *)
      pa_stmt fn prog st c

    | Cwhile (_, c1, _, c2) when has_annot "bounded" instr ->
      (* Ignore the loop condition, as this loop will be fully unrolled at analysis time. *)
      let st = pa_stmt fn prog st c1 in
      let st = pa_stmt fn prog st c2 in
      st

    | Cwhile (_, c1, b, c2) ->
      let vs,st = expr_vars st b in

      let st' =
        if Config.sc_flow_dep () then
          { st with ct = Sv.union st.ct (Sv.of_list vs) }
        else st in

      let bdy_rev = List.rev_append c1 (List.rev c2) in
      let flags_setfrom = List.fold_left (fun flags_setfrom v -> match v.v_ty with
          | Bty Bool ->
            let new_f =
              match pa_flag_setfrom v bdy_rev with
              | exception Flag_set_from_failure | None -> Sv.empty
              | Some r -> Sv.of_list r in
            Sv.union flags_setfrom new_f             
          | _ -> flags_setfrom) Sv.empty vs
      in

      let while_vars = Sv.union st'.while_vars (Sv.of_list vs) in
      let while_vars = 
        if Config.sc_while_flags_setfrom_dep ()
        then Sv.union while_vars flags_setfrom
        else while_vars in
      
      let st' = { st' with while_vars = while_vars } in

      (* Again, we reset the context after the merge *)
      pa_stmt fn prog st' (List.append c1 c2)
      |> set_ct st.ct

    | Ccall (lvs, fn', es) ->   
      let st = { st with cfg = add_call st.cfg fn fn' } in
      let f_decl = get_fun_def (oget prog) fn' |> oget in

      let st =
        if Ss.mem fn'.fn_name st.f_done then st
        else pa_func prog st fn' in

      let st = List.fold_left2 (fun st lv ret ->
          pa_lv st lv (Pvar { gv = ret; gs = Expr.Slocal; } ))
          st lvs f_decl.f_ret in

      List.fold_left2 pa_expr st f_decl.f_args es 

  and pa_func (prog : ('info, 'asm) prog option) st fn =
    let f_decl = get_fun_def (oget prog) fn |> oget in
    let st = { st with f_done = Ss.add fn.fn_name st.f_done } in
    pa_stmt fn prog st f_decl.f_body

  and pa_stmt fn (prog : ('info, 'asm) prog option) st instrs =
    List.fold_left (pa_instr fn prog) st instrs
                                  
  let print_dp fmt dp =
    Format.fprintf fmt "@[<v 2>Dependency heuristic graph:@;%a@]@."
      (pp_list (fun fmt (v, sv) -> Format.fprintf fmt "@[<hov 4>%a <-- %a@]"
                   (Printer.pp_var ~debug:true) v
                   (pp_list ( Printer.pp_var ~debug:true))
                   (List.sort V.compare (Sv.elements sv))))
      (List.sort (fun (v,_) (v',_) -> V.compare v v')
         (Mv.bindings dp))

  let print_while_vars fmt while_vars =
    Format.fprintf fmt "@[<v 2>While variables:@;%a@]@."
      (pp_list (fun fmt v -> Format.fprintf fmt "@[<hov 4>%a@]"
                   (Printer.pp_var ~debug:true) v))        
      (List.sort (fun v v' -> V.compare v v')
         (Sv.to_list while_vars))

  
  let print_cfg fmt cfg =
    Format.fprintf fmt "@[<v 2>Control-flow graph:@;%a@]@."
      (pp_list (fun fmt (f, fs) -> Format.fprintf fmt "@[<hov 4>%a --> %a@]"
                   pp_string f.fn_name
                   (pp_list (fun fmt x -> pp_string fmt x.fn_name))
                   (List.sort F.compare (Sf.elements fs))))
      (List.sort (fun (v,_) (v',_) -> F.compare v v') (Mf.bindings cfg))

  let pa_make func (prog : ('info, 'asm) prog option) =
    let st = { dp = Mv.empty;
               cfg = Mf.empty;
               while_vars = Sv.empty;
               f_done = Ss.empty;
               if_conds = [];
               ct = Sv.empty } in
    let st = pa_stmt func.f_name prog st func.f_body in

    debug (fun () -> Format.eprintf "%a" print_dp st.dp);
    debug (fun () -> Format.eprintf "%a" print_while_vars st.while_vars);
    debug (fun () -> Format.eprintf "%a" print_cfg st.cfg);

    { pa_dp = st.dp;
      pa_cfg = st.cfg;
      while_vars = st.while_vars;
      if_conds = List.sort_uniq Stdlib.compare st.if_conds }
end


(* Flow-sensitive Pre-Analysis *)
module FSPa : sig    
  val fs_pa_make : Wsize.wsize -> X86_extra.x86_extended_op Sopn.asmOp -> ('info, X86_extra.x86_extended_op) func -> (unit, X86_extra.x86_extended_op) func * Pa.pa_res
end = struct
  exception Fcall
  let rec collect_vars_e sv = function
    | Pconst _ | Pbool _ | Parr_init _ -> sv
    | Pvar v ->
      begin
        match v.gs with
        | Expr.Sglob -> sv
        | Expr.Slocal -> Sv.add (L.unloc v.gv) sv
      end
    | Pget (_,_, _, v, e)   -> collect_vars_e (Sv.add (L.unloc v.gv) sv) e
    | Psub (_,_,_, v, e) -> collect_vars_e (Sv.add (L.unloc v.gv) sv) e
    | Pload (_, _, v, e) -> collect_vars_e (Sv.add (L.unloc v) sv) e
    | Papp1 (_,e) -> collect_vars_e sv e
    | Papp2 (_,e1,e2) -> collect_vars_es sv [e1;e2]
    | PappN (_, el)  -> collect_vars_es sv el
    | Pif (_, e1, e2, e3) -> collect_vars_es sv [e1;e2;e3]
  and collect_vars_es sv es = List.fold_left collect_vars_e sv es

  let collect_vars_lv sv = function
    | Lnone _ -> sv
    | Lvar v -> Sv.add (L.unloc v) sv
    | Laset (_,_,_, v, e) | Lasub (_,_,_, v, e) | Lmem (_, _, v, e) ->
      collect_vars_e (Sv.add (L.unloc v) sv) e

  let collect_vars_lvs sv = List.fold_left collect_vars_lv sv
      
  let rec collect_vars_i sv i = match i.i_desc with
    | Cif (e, st1, st2)
    | Cwhile (_,st1,e,st2) ->
      let sv = collect_vars_is sv st1 in
      let sv = collect_vars_is sv st2 in
      collect_vars_e sv e
    | Cfor (v,(_,e1,e2),st) ->
      let sv = collect_vars_is (Sv.add (L.unloc v) sv) st in
      collect_vars_es sv [e1;e2]
    | Copn (lvs, _, _, es) | Csyscall(lvs, _, es) ->
      let sv = collect_vars_lvs sv lvs in
      collect_vars_es sv es
    | Cassgn (lv, _, _, e) ->
      let sv = collect_vars_lv sv lv in
      collect_vars_e sv e
    | Ccall _ -> raise Fcall

  and collect_vars_is sv is = List.fold_left collect_vars_i sv is


  let check_uniq_names sv =
    Sv.for_all (fun v -> not (Sv.exists (fun v' ->
        v.v_id <> v'.v_id && v.v_name = v'.v_name) sv)) sv
    
  let fs_pa_make pd asmOp (f : ('info, 'asm) func) =
    let sv = Sv.of_list f.f_args in
    let vars = try collect_vars_is sv f.f_body with
      | Fcall ->
        raise (Failure "Flow-sensitive packing error: some sub-procedures are \
                        not inlined.\n\
                        Maybe you are not at the correct compilation pass?");
    in
    (* We make sure that variable are uniquely defined by their names. *)
    assert (check_uniq_names vars);
     
    let ssa_f = Ssa.split_live_ranges false f in
    debug (fun () ->
        Format.eprintf "SSA transform of %s:@;%a"
          f.f_name.fn_name
          (Printer.pp_func ~debug:true pd asmOp) ssa_f);
    (* Remark: the program is not used by [Pa], since there are no function
       calls in [f]. *)
    let dp = Pa.pa_make ssa_f None in
    ssa_f, dp

end


(**************************)
(* Pre-Analysis Functions *)
(**************************)

(* Reflexive and transitive closure. *)
let trans_closure (dp : Pa.dp) =
  let f dp =
    Mv.map (fun sv ->
        Sv.fold (fun v' s ->
            Sv.union s (Pa.dp_v dp v'))
          sv sv) dp in
  
  fpt f (Mv.equal Sv.equal) dp

(* Add variables where [sv_ini] flows to. *)
let flow_to (dp : Pa.dp) (sv_ini : Sv.t) =
    Mv.fold (fun v sv acc ->
        if Sv.disjoint sv acc then acc
        else Sv.add v acc
      ) dp sv_ini

(* Add variables flowing to [sv_ini]. *)
let flowing_to (dp : Pa.dp) (sv_ini : Sv.t) =
    Mv.fold (fun v sv acc ->
        if Sv.mem v acc then acc
        else Sv.union acc sv
    ) dp sv_ini
