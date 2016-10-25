(* * Compilation and source-to-source transformations on IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Util
open Arith
open IL_Lang
open IL_Utils
open IL_Interp

module X64 = Asm_X64
module MP  = MParser
module HT  = Hashtbl
module IT  = IL_Typing

(* ** Partially evaluate dimension and parameter-expressions
 * ------------------------------------------------------------------------ *)

let peval_param pmap _ p =
  match Map.find pmap p with
  | Some(x) -> Pconst(x)
  | None    -> failwith_ "peval_patom: parameter %s undefined" p

let peval_patom pmap lmap pa =
  match pa with
  | Pparam(p) -> peval_param pmap lmap p
  | Pdest(d) as v ->
    assert (d.d_idx=inone);
    begin match Map.find lmap d.d_name with
    | Some (Vu64 x) -> Pconst(x)
    | Some(_)       -> failwith_ "peval_pexpr: variable %s of wrong type" d.d_name
    | None          -> Patom(v)
    end

let peval_pexpr_g peval_atom pmap lmap ce =
  let rec go = function
    | Pbinop(o,e1,e2) ->
      begin match go e1, go e2 with
      | Pconst c1, Pconst c2 ->
        Pconst(eval_pbinop o c1 c2)
      | e1,e2 -> Pbinop(o,e1,e2)
      end
    | Patom(a) -> peval_atom pmap lmap a
    | Pconst(_) as e -> e
  in
  go ce

let peval_pexpr pmap lmap = peval_pexpr_g peval_patom pmap lmap

let peval_dexpr pmap lmap = peval_pexpr_g peval_param pmap lmap

let peval_pcond pmap lmap cc =
  let rec go = function
    | Ptrue              -> Ptrue
    | Pnot(ic)           ->
      begin match go ic with
      | Ptrue   -> Pnot(Ptrue)
      | Pnot(c) -> c
      | c       -> Pnot(c)
      end
    | Pand(cc1,cc2)      ->
      begin match go cc1, go cc2 with
      | Ptrue,      Ptrue       -> Ptrue
      | Pnot(Ptrue),_
      | _          ,Pnot(Ptrue) -> Pnot(Ptrue)
      | c1, c2                  -> Pand(c1,c2)
      end
    | Pcmp(cco,ce1,ce2) ->
      begin match peval_pexpr pmap lmap ce1, peval_pexpr pmap lmap ce2 with
      | Pconst(c1), Pconst(c2) ->
        if eval_pcondop cco c1 c2 then Ptrue else Pnot(Ptrue)
      | e1,         e2         -> Pcmp(cco,e1,e2)
      end
  in
  go cc

(* ** Inline function calls
 * ------------------------------------------------------------------------ *)
(* *** Summary
Inline function call C[x = f(a);]
1. define f' as f renamed away from context C
2. return C[f'.arg := a; f'.body; x := f'.ret] where := is an assignemt
   that will be compiled away and used as an equality-constraint
   in the stack-slot/register allocation.
*)
(* *** Code *)

let rec inline_call func_map suffix c info fname ds ss =
  let ssuffix = "_"^string_of_int !c^(String.make (suffix + 1) '_') in
  let func = map_find_exn func_map pp_string fname in
  let fdef = match func.f_def with
    | Def d -> d
    | Undef | Py _ -> failwith_ "cannot inline calls in undefined function %s" fname
  in
  let ret_ss =
    List.map2_exn
      ~f:(fun n (s,t) -> Src(mk_dest_name (n^ssuffix) t s))
      fdef.fd_ret func.f_ret_ty
  in
  let arg_ds = List.map ~f:(fun (s,n,t) -> mk_dest_name (n^ssuffix) t s) func.f_args in
  let stmt = rename_stmt (fun s -> s^ssuffix) fdef.fd_body in
  let stmt = inline_calls_stmt func_map suffix c stmt in
  (List.map2_exn ~f:(fun d s -> mk_base_instr info (Assgn(d,s,Eq))) arg_ds ss)
  @ stmt
  @ (List.map2_exn ~f:(fun d s -> mk_base_instr info (Assgn(d,s,Eq))) ds ret_ss)

and inline_calls_base_instr func_map (suffix : int) c info bi =
  match bi with
  | Call(fn,ds,ss) ->
    incr c;
    [ { i_val = Binstr(Comment(fsprintf "START Call: %a" pp_base_instr bi)); i_info = info} ]
    @ inline_call func_map suffix c info fn ds ss
    @ [ { i_val = Binstr(Comment(fsprintf "END Call: %a" pp_base_instr bi)); i_info = info} ]

  | bi -> [ { i_val = Binstr(bi); i_info = info} ]

and inline_calls_instr func_map (suffix : int) c (li : 'info instr_info_t) =
  let ilc_s = inline_calls_stmt func_map suffix c in
  let instrs =
    match li.i_val with
    | If(c,s1,s2)    -> [{ li with i_val = If(c,ilc_s s1, ilc_s s2)}]
    | For(c,lb,ub,s) -> [{ li with i_val = For(c,lb,ub,ilc_s s)}]
    | Binstr(bi)     -> inline_calls_base_instr func_map suffix c li.i_info bi
    | While(wt,fc,s) -> [{ li with i_val = While(wt,fc,ilc_s s)}]
  in
  instrs

and inline_calls_stmt func_map (suffix : int) c (s : 'info stmt_t) : 'info stmt_t =
  List.concat_map ~f:(inline_calls_instr func_map suffix c) s

let inline_calls_fun func_map (fname : string) =
  let func = map_find_exn func_map pp_string fname in
  let fdef = match func.f_def with
    | Def d -> d
    | Undef | Py _ -> failwith_ "cannot inline calls in undefined function %s" fname
  in
  let used_vars = pvars_func func in
  let suffix =
    find_min (fun i ->
      Set.exists used_vars
        ~f:(fun s -> not (String.is_suffix s ~suffix:(String.make (i+1) '_'))))
  in
  let c = ref 0 in
  if fdef.fd_decls<>None then failwith_ "inline decls before inlining functions";
  let stmt = inline_calls_stmt func_map suffix c fdef.fd_body in
  let func = { func with f_def = Def { fdef with fd_body = stmt } } in
  Map.add func_map ~key:fname ~data:func

let inline_calls_modul (modul : 'info modul_t) fname : 'info modul_t =
  let func_map =
    String.Map.of_alist_exn (List.map ~f:(fun f -> (f.f_name,f)) modul.m_funcs)
  in
  let func_map = inline_calls_fun func_map fname in
  { modul with m_funcs = Map.data func_map}

(* ** Macro expansion: loop unrolling, if, ...
 * ------------------------------------------------------------------------ *)
(* *** Summary
Given values for parameters, perform the following unfolding:
1. evaluate pexpr/dexpr in dimensions and ranges
2. unfold loops and if-then-else
3. evaluate pexpr in indexing
Assumes that there are no function calls in the macro-expanded function.
*)
(* *** Code *)

let inst_ty pmap ty =
  match ty with
  | Bool     -> Bool
  | U64      -> U64
  | Arr(dim) -> Arr(peval_dexpr pmap String.Map.empty dim)

let inst_dest pmap lmap d =
  let g idx =
    match idx with
    | Inone -> Some(inone)
    | Iconst(pe) ->
      begin match peval_pexpr pmap lmap pe with
      | Pconst(_) as pc -> Some(mk_Iconst pc)
      | _ -> assert false
      end
    | Ireg(_) -> None
  in
  let f n idx (t,s) =
    (n,idx,(inst_ty pmap t,s))
  in
  let idx = dest_map_idx_t g f d.d_idx in
  let (t,s) = d.d_decl in
  { d with d_idx  = idx;
           d_decl = (inst_ty pmap t,s); }

let inst_src pmap lmap = function
  | Src(d)  -> Src(inst_dest pmap lmap d)
  | Imm(pe) -> Imm(peval_pexpr pmap lmap pe)

let inst_base_instr pmap lmap bi =
  let inst_p = peval_pexpr pmap lmap in
  let inst_d = inst_dest  pmap lmap in
  let inst_s = inst_src   pmap lmap in
  match bi with
  | Op(o,ds,ss)     -> Op(o,List.map ~f:inst_d ds,List.map ~f:inst_s ss)
  | Assgn(d,s,t)    -> Assgn(inst_d d,inst_s s,t)
  | Load(d,s,pe)    -> Load(inst_d d,inst_s s,inst_p pe)
  | Store(s1,pe,s2) -> Store(inst_s s1,inst_p pe,inst_s s2)
  | Comment(_)      -> bi
  | Call(_)         -> failwith "inline calls before macro expansion"

let macro_expand_stmt pmap (stmt : 'info stmt_t) =
  let spaces indent = String.make indent ' ' in
  let s_of_cond c = if c then "if" else "else" in
  let comment_if s indent cond ic =
    fsprintf "%s%s %s %a" (spaces indent) s (s_of_cond cond) pp_pcond ic
  in
  let comment_while s indent iv lb_ie ub_ie =
    fsprintf "%s%s for %s in %a..%a" s (spaces indent) iv pp_pexpr lb_ie pp_pexpr ub_ie
  in
  let bicom info c = mk_base_instr info (Comment(c)) in

  let rec expand indent lmap li =
    let info = li.i_info in
    let me_s s = List.concat_map s ~f:(expand (indent + 2) lmap) in
    match li.i_val with

    | Binstr(binstr) -> [mk_base_instr info (inst_base_instr pmap lmap binstr)]

    | While(wt,fc,st) ->
      [ { li with i_val = While(wt,fc,me_s st) } ]

    | If(Fcond(ic),st1,st2) ->
      [ { li with i_val = If(Fcond(ic),me_s st1,me_s st2) } ]

    | If(Pcond(ic),st1,st2) ->
      (* F.printf "\n%s %a\n%!" (spaces indent) pp_pcond ic; *)
      let cond = eval_pcond_exn pmap lmap ic in
      let st = if cond then st1 else st2 in
      if st=[] then [] else (
          [bicom info (comment_if "START: " indent cond ic)]
        @ (List.concat_map ~f:(fun bi -> (expand (indent + 2) lmap bi)) st)
        @ [bicom info (comment_if "END:   " indent cond ic)]
      )

    | For(iv,lb_ie,ub_ie,stmt) ->
      (* F.printf "\n%s %a .. %a\n%!" (spaces indent) pp_pexpr lb_ie pp_pexpr ub_ie;  *)
      let lb  = eval_pexpr_exn pmap lmap lb_ie in
      let ub  = eval_pexpr_exn pmap lmap ub_ie in
      assert (U64.compare lb ub <= 0);
      let body_for_v v =
          [bicom info (fsprintf "%s%s = %s" (spaces (indent+2)) iv.d_name (U64.to_string v))]
        @ (List.concat_map stmt ~f:(expand (indent + 2) (Map.add lmap ~key:iv.d_name ~data:(Vu64 v))))
      in
        [bicom info (comment_while "START:" indent iv.d_name lb_ie ub_ie)]
      @ List.concat_map (list_from_to ~first:lb ~last:ub) ~f:body_for_v
      @ [bicom info (comment_while "END:" indent iv.d_name lb_ie ub_ie)]
  in
  List.concat_map ~f:(expand 0 String.Map.empty) stmt

let macro_expand_fundef pmap (fdef : 'info fundef_t) =
  if fdef.fd_decls<>None then failwith_ "inline decls before macro expanding";
  { fdef with
    fd_body  = macro_expand_stmt pmap fdef.fd_body
  ; fd_ret   = fdef.fd_ret
  }

let macro_expand_func pmap (func : 'info func_t) =
  let inst_t = inst_ty pmap in
  let fdef = match func.f_def with
    | Def fd -> Def(macro_expand_fundef pmap fd)
    | Undef  -> Undef
    | Py(s)  -> Py(s)
  in
  { f_name      = func.f_name
  ; f_call_conv = func.f_call_conv
  ; f_args      = List.map func.f_args ~f:(fun (s,n,ty) -> (s,n,inst_t ty))
  ; f_def       = fdef
  ; f_ret_ty    = List.map func.f_ret_ty ~f:(fun (s,ty) -> (s,inst_t ty))
  }

let macro_expand_modul pvar_map (modul : 'info modul_t) fname =
  List.iter modul.m_params
    ~f:(fun (n,_) -> if not (Map.mem pvar_map n)
                     then failwith_ "parameter %s not given for expand" n);
  map_fun modul fname ~f:(macro_expand_func pvar_map)

(* ** Expand array assignments *)
(* *** Summary
Replace array assignments 'a = b;' where a, b : u64[n] by
'a[0] = b[0]; ...; a[n-1] = b[n-1];'
FIXME: Would it be easier to replace this by 'for' and perform the
       step before macro-expansion?
*)
(* *** Code *)

let array_assign_expand_stmt stmt =
  let rec expand li =
    let exp_s s = List.concat_map s ~f:expand in
    match li.i_val with
    | Binstr(Op(_,_,_))
    | Binstr(Comment(_))
    | Binstr(Load(_,_,_))
    | Binstr(Store(_,_,_))
    | Binstr(Assgn(_,Imm(_),_)) -> [li]

    | If(Pcond(_),_,_) -> failwith "array expansion expects macro-if expanded"
    | For(_,_,_,_)     -> failwith "array expansion expects macro-for expanded"
    | Binstr(Call(_))  -> failwith "array expansion expects calls are expanded"
    | While(wt,fc,stmt) ->
      [ { li with i_val = While(wt,fc,exp_s stmt) } ]
    
    | If(Fcond(_) as c,s1,s2) ->
      [ { li with i_val = If(c,exp_s s1,exp_s s2) } ]
 
    | Binstr(Assgn(d,Src(s),t)) ->
      let (td,_) = d.d_decl in
      let (ts,_) = s.d_decl in
      begin match d.d_idx, s.d_idx, td, ts with
      | Inone, Inone, Arr(Pconst(ub1)), Arr(Pconst(ub2)) ->
        assert (U64.equal ub1 ub2);
        let mk_assgn i =
          let d = {d with d_idx = mk_Iconst(Pconst i)} in
          let s = Src({s with d_idx = mk_Iconst(Pconst i)}) in
          { li with i_val = Binstr(Assgn(d,s,t)) }
        in
        List.map ~f:mk_assgn (list_from_to ~first:U64.zero ~last:ub1)
      | _ -> [li]
      end
  in
  List.concat_map ~f:expand stmt

let array_assign_expand_fundef fdef =
  { fdef with fd_body  = array_assign_expand_stmt fdef.fd_body }

let array_assign_expand_func func =
  map_fundef ~err_s:"expand array assignments" ~f:array_assign_expand_fundef func

let array_assign_expand_modul modul fname =
  map_fun modul fname ~f:array_assign_expand_func

(* ** Expand arrays *)
(* *** Summary
Replace register arrays by individual registers. For stack arrays,
do the same unless there are array gets with non-constant indexes.
Assumes that there no function calls in the macro-expanded function
and that all inline-loops and ifs have been expanded.
*)
(* *** Code *)

let keep_arrays_non_const_index fdef =
  let dests = dests_fundef fdef in
  let non_const_arrays = ref SS.empty in
  let classify_arrays d = 
    (* if d.d_oidx<>None then F.printf "array: %a\n" pp_dest d; *)
    match d.d_idx with
    | Inone -> ()
    | Iconst(Pconst(_)) -> ()
    | Ireg(di) ->
      non_const_arrays := SS.add !non_const_arrays d.d_name;
      let (_,s) = d.d_decl in
      let (_,si) = di.d_decl in
      begin match s, si with
      | Stack, Reg -> ()
      | _, _ ->
        failwith_
          ("%s: array %s (%s) with non-constant indexes requires stack storage, "
           ^^"index %s (%s) must have reg storage")
          "array expansion"
          d.d_name (string_of_storage s)
          di.d_name (string_of_storage si)
      end
    | Iconst(pe) ->
      failwith_ "%s: the parameter-expression %a cannot be used as index"
        "array expansion" pp_pexpr pe
  in
  DS.elements dests |> List.iter ~f:classify_arrays;
  !non_const_arrays


let array_expand_stmt keep_arrays unique_suffix stmt =
  let rename_var name u =
    fsprintf "%s_%a_%s" name pp_uint64 u unique_suffix
  in
  let update_decl ((t,s) as d) =
    match t with
    | U64 | Bool     -> d
    | Arr(Pconst(_)) -> (U64,s)
    | Arr(_) -> failwith "array expansion: impossible, array bounds are not constants"
  in
  let ren name idx decl =
    if not (SS.mem keep_arrays name) then
      match idx with
      | Inone             -> name, idx, decl
      | Ireg(_)           -> name, idx, decl
      | Iconst(Pconst(u)) -> rename_var name u, inone, update_decl decl
      | Iconst(pe)        ->
        failwith_ "%s: the parameter-expression %a cannot be used as index"
          "array_expand_stmt" pp_pexpr pe
    else
      name,idx,decl
  in
  dest_map_stmt_t (fun _ -> None) ren stmt

let array_expand_fundef fdef =
  if fdef.fd_decls<>None then failwith_ "array expand: expected empty decls";
  let fresh_suffix = fresh_suffix_fundef fdef "arr" in
  let keep_arrays = keep_arrays_non_const_index fdef in
  let body = array_expand_stmt keep_arrays fresh_suffix fdef.fd_body in
  { fdef with
    fd_body = body;
    fd_decls = None
  }

(* FIXME: we assume this is an extern function, hence all arguments and
          returned values must have type u64 *)
let array_expand_func func =
  map_fundef ~err_s:"expand arrays" ~f:array_expand_fundef func

let array_expand_modul modul fname =
  map_fun modul fname ~f:array_expand_func

(* ** Local SSA *)
(* *** Summary
*)
(* *** Code *)

(* **** Maintain renaming info *)

module RNI = struct
  type t = {
    map     : int       String.Table.t; (* no entry = never defined *)
    unused  : int       String.Table.t; (* smallest unused index    *)
    changed : Int.Set.t String.Table.t; (* indexes for initial vars *)
  }

  let mk () = {
    map     = String.Table.create ();
    unused  = String.Table.create ();
    changed = String.Table.create ();
  }

  let map_get rn_info name =
    HT.find rn_info name |> Option.value ~default:0

  let changed_add rn_info name idx =
    HT.change rn_info.changed name
      ~f:(function | None    -> Some(Int.Set.singleton idx)
                   | Some is -> Some(Set.add is idx))

  let changed_remove rn_info name idx =
    HT.change rn_info.changed name
      ~f:(function | None    -> assert false
                   | Some is -> Some(Set.remove is idx))

  let map_modify rn_info name =
    let max_idx = HT.find rn_info.unused name |> Option.value ~default:1 in
    HT.set rn_info.map    ~key:name ~data:max_idx;
    HT.set rn_info.unused ~key:name ~data:(succ max_idx);
    changed_add rn_info name max_idx

  let mk_reg_name name idx =
    fsprintf "%s_%i" name idx

  let rename rn_info name =
    let idx = map_get rn_info.map name in
    mk_reg_name name idx

end

(* **** Synchronize renaming for do-while *)

let rn_map_dowhile_update ~old:rn_map_enter rn_info =
  let mapping = String.Table.create () in
  let correct = ref [] in
  let handle_changed ~key:name ~data:new_idx =
    let old_idx = RNI.map_get rn_map_enter name in
    if old_idx<>new_idx then (
      let old_name = RNI.mk_reg_name name old_idx in
      let new_name = RNI.mk_reg_name name new_idx in
      (* F.printf "rename  %s to %s\n"  new_name old_name; *)
      HT.add_exn mapping ~key:new_name ~data:old_name;
      RNI.changed_remove rn_info name new_idx;
      correct := (name,old_idx)::!correct
    )
  in
  HT.iteri rn_info.RNI.map ~f:handle_changed;
  List.iter !correct ~f:(fun (s,idx) -> HT.set rn_info.RNI.map ~key:s ~data:idx);
  mapping

(* **** Synchronize renaming for if *)

let rn_map_if_update rn_info ~rn_if ~rn_else =
  let changed_if   = String.Table.create () in
  let changed_else = String.Table.create () in
  (* populate given maps with changes *)
  let handle_changed _s changed ~key:name ~data:new_idx =
    let old_idx = RNI.map_get rn_info.RNI.map name in
    if old_idx<>new_idx then (
      (* F.printf "changed %s: '%s' from %i to %i\n" s name old_idx new_idx; *)
      HT.set changed ~key:name ~data:();
    ) else (
      (* F.printf "unchanged %s: '%s'\n" s name;  *)
    )
  in
  HT.iteri rn_if   ~f:(handle_changed "if"   changed_if);
  HT.iteri rn_else ~f:(handle_changed "else" changed_else);
  let changed =
    SS.union
      (SS.of_list @@ HT.keys changed_if)
      (SS.of_list @@ HT.keys changed_else)
  in
  (* from new name to old name *)
  let mapping_if_names   = String.Table.create () in
  let mapping_else_names = String.Table.create () in
  (* make renamings consistent for defs that are active when leaving the two branches
     NOTE: we could make this more precise by restricting this to live defs *)
  let merge name =
    (* if a given name has been changed in both, then we choose the higher index *)
    match HT.mem changed_if name, HT.mem changed_else name with
    | false, false -> assert false
    (* defs for name in both, choose larger index from else *)
    | true, true ->
      let idx_if   = RNI.map_get rn_if   name in
      let idx_else = RNI.map_get rn_else name in
      assert (idx_else > idx_if);
      let name_if   = RNI.mk_reg_name name idx_if   in
      let name_else = RNI.mk_reg_name name idx_else in
      (* F.printf "rename %s to %s in if (use else name)\n" name_if name_else; *)
      HT.set mapping_if_names ~key:name_if ~data:name_else;
      (* update rn_map for statements following if-then-else *)
      HT.set rn_info.RNI.map ~key:name ~data:idx_else;
      RNI.changed_remove rn_info name idx_if
    (* def only in if-branch, rename if-def with old name *)
    | true, false ->
      let idx_if    = RNI.map_get rn_if          name in
      let idx_enter = RNI.map_get rn_info.RNI.map name in
      assert (idx_if<>idx_enter);
      let name_if    = RNI.mk_reg_name name idx_if    in
      let name_enter = RNI.mk_reg_name name idx_enter in
      (* F.printf "rename %s to %s in if (use enter name)\n"  name_if name_enter; *)
      HT.set mapping_if_names ~key:name_if ~data:name_enter;
      RNI.changed_remove rn_info name idx_if
    (* def only in else-branch, rename if-def with old name *)
    | false, true ->
      let idx_else  = RNI.map_get rn_else        name in
      let idx_enter = RNI.map_get rn_info.RNI.map name in
      assert (idx_else<>idx_enter);
      let name_else    = RNI.mk_reg_name name idx_else in
      let name_enter = RNI.mk_reg_name name idx_enter  in
      (* F.printf "rename %s to %s in else (use enter name)\n"  name_else name_enter; *)
      HT.set mapping_else_names ~key:name_else ~data:name_enter;
      RNI.changed_remove rn_info name idx_else
  in
  SS.iter changed ~f:merge;
  mapping_if_names, mapping_else_names

let rec local_ssa_instr rn_info linstr =
  let rename = RNI.rename rn_info in
  let instr' =
    match linstr.i_val with

    | Binstr(bi) ->
      (* rename RHS *)
      (* FIXME: how to treat arr[i] = 5? *)
      let bi = rename_base_instr ~rn_type:UseOnly rename bi in
      (* update renaming map and rename LHS *)
      let def_vars = def_binstr bi in
      SS.iter def_vars ~f:(fun s -> RNI.map_modify rn_info s);
      let bi = rename_base_instr ~rn_type:DefOnly rename bi in
      Binstr(bi)

    | If(Fcond(fc),s1,s2) ->
      let rn_map_if   = HT.copy rn_info.RNI.map in
      let rn_map_else = HT.copy rn_info.RNI.map in
      let fc = rename_fcond rename fc in
      let s1 = local_ssa_stmt { rn_info with RNI.map=rn_map_if   } s1 in
      let s2 = local_ssa_stmt { rn_info with RNI.map=rn_map_else } s2 in
      let rn_sync_if, rn_sync_else =
        rn_map_if_update rn_info ~rn_if:rn_map_if ~rn_else:rn_map_else
      in
      let rn rns s = HT.find rns s |> Option.value ~default:s in
      let s1 = rename_stmt (rn rn_sync_if)   s1 in
      let s2 = rename_stmt (rn rn_sync_else) s2 in
      If(Fcond(fc),s1,s2)
      
    | While(DoWhile,fc,s) ->
      let rn_map_enter = HT.copy rn_info.RNI.map in
      let s = local_ssa_stmt rn_info s in
      (* rename fc with the rn_map for leave *)
      let fc = rename_fcond rename fc in
      (* make last def-index coincide with def-index from entering *)
      let rn_sync = rn_map_dowhile_update ~old:rn_map_enter rn_info in
      let rn s = HT.find rn_sync s |> Option.value ~default:s in
      let fc = rename_fcond rn fc in
      let s  = rename_stmt rn s in
      While(DoWhile,fc,s)
      
    | While(WhileDo,_fc,_s) ->
      failwith "INCOMPLETE"

    | If(Pcond(_),_,_)
    | For(_,_,_,_)     -> failwith "local SSA transformation: unexpected instruction"
  in
  { linstr with i_val = instr' }

and local_ssa_stmt rn_map stmt =
  List.map ~f:(local_ssa_instr rn_map) stmt

let local_ssa_fundef fdef =
  if fdef.fd_decls<>None then failwith_ "local ssa: expected empty decls";
  let rn_info = RNI.mk () in
  let body = local_ssa_stmt rn_info fdef.fd_body in
  let ret = List.map fdef.fd_ret ~f:(RNI.rename rn_info) in
  { fdef with fd_body = body; fd_ret = ret;}

let local_ssa_func func =
  let func = map_fundef ~err_s:"apply local SSA transformation" ~f:local_ssa_fundef func in
  { func with f_args = List.map ~f:(fun (s,n,t) -> (s,RNI.mk_reg_name n 0,t)) func.f_args }

let local_ssa_modul modul fname =
  map_fun modul fname ~f:local_ssa_func

(* ** Strip comments
 * ------------------------------------------------------------------------ *)

let strip_comments_modul modul fname =
  concat_map_modul modul fname
    ~f:(fun _pos -> function Binstr(Comment _) -> [] | i -> [i])
