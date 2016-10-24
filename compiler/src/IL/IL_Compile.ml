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

let rec inline_call func_map suffix c loc fname ds ss =
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
  (List.map2_exn ~f:(fun d s -> mk_base_instr loc (Assgn(d,s,Eq))) arg_ds ss)
  @ stmt
  @ (List.map2_exn ~f:(fun d s -> mk_base_instr loc (Assgn(d,s,Eq))) ds ret_ss)

and inline_calls_base_instr func_map (suffix : int) c loc bi =
  match bi with
  | Call(fn,ds,ss) ->
    incr c;
    [ L.{ l_val = Binstr(Comment(fsprintf "START Call: %a" pp_base_instr bi)); l_loc = loc} ]
    @ inline_call func_map suffix c loc fn ds ss
    @ [ L.{ l_val = Binstr(Comment(fsprintf "END Call: %a" pp_base_instr bi)); l_loc = loc} ]

  | bi -> [ L.{ l_val = Binstr(bi); l_loc = loc} ]

and inline_calls_instr func_map (suffix : int) c (li : instr_t L.located) =
  let ilc_s = inline_calls_stmt func_map suffix c in
  let instrs =
    match li.L.l_val with
    | If(c,s1,s2)    -> [{ li with L.l_val = If(c,ilc_s s1, ilc_s s2)}]
    | For(c,lb,ub,s) -> [{ li with L.l_val = For(c,lb,ub,ilc_s s)}]
    | Binstr(bi)     -> inline_calls_base_instr func_map suffix c li.L.l_loc bi
    | While(wt,fc,s) -> [{ li with L.l_val = While(wt,fc,ilc_s s)}]
  in
  instrs

and inline_calls_stmt func_map (suffix : int) c (s : stmt_t) : stmt_t =
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

let inline_calls_modul (modul : modul_t) (fname : string) : modul_t =
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

let macro_expand_stmt pmap (stmt : stmt_t) =
  let spaces indent = String.make indent ' ' in
  let s_of_cond c = if c then "if" else "else" in
  let comment_if s indent cond ic =
    fsprintf "%s%s %s %a" (spaces indent) s (s_of_cond cond) pp_pcond ic
  in
  let comment_while s indent iv lb_ie ub_ie =
    fsprintf "%s%s for %s in %a..%a" s (spaces indent) iv pp_pexpr lb_ie pp_pexpr ub_ie
  in
  let bicom loc c = mk_base_instr loc (Comment(c)) in

  let rec expand indent lmap li =
    let loc = li.L.l_loc in
    let me_s s = List.concat_map s ~f:(expand (indent + 2) lmap) in
    match li.L.l_val with

    | Binstr(binstr) -> [mk_base_instr loc (inst_base_instr pmap lmap binstr)]

    | While(wt,fc,st) ->
      [ { li with L.l_val = While(wt,fc,me_s st) } ]

    | If(Fcond(ic),st1,st2) ->
      [ { li with L.l_val = If(Fcond(ic),me_s st1,me_s st2) } ]

    | If(Pcond(ic),st1,st2) ->
      (* F.printf "\n%s %a\n%!" (spaces indent) pp_pcond ic; *)
      let cond = eval_pcond_exn pmap lmap ic in
      let st = if cond then st1 else st2 in
      if st=[] then [] else (
          [bicom loc (comment_if "START: " indent cond ic)]
        @ (List.concat_map ~f:(fun bi -> (expand (indent + 2) lmap bi)) st)
        @ [bicom loc (comment_if "END:   " indent cond ic)]
      )

    | For(iv,lb_ie,ub_ie,stmt) ->
      (* F.printf "\n%s %a .. %a\n%!" (spaces indent) pp_pexpr lb_ie pp_pexpr ub_ie;  *)
      let lb  = eval_pexpr_exn pmap lmap lb_ie in
      let ub  = eval_pexpr_exn pmap lmap ub_ie in
      assert (U64.compare lb ub <= 0);
      let body_for_v v =
          [bicom loc (fsprintf "%s%s = %s" (spaces (indent+2)) iv.d_name (U64.to_string v))]
        @ (List.concat_map stmt ~f:(expand (indent + 2) (Map.add lmap ~key:iv.d_name ~data:(Vu64 v))))
      in
        [bicom loc (comment_while "START:" indent iv.d_name lb_ie ub_ie)]
      @ List.concat_map (list_from_to ~first:lb ~last:ub) ~f:body_for_v
      @ [bicom loc (comment_while "END:" indent iv.d_name lb_ie ub_ie)]
  in
  List.concat_map ~f:(expand 0 String.Map.empty) stmt

let macro_expand_fundef pmap (fdef : fundef_t) =
  if fdef.fd_decls<>None then failwith_ "inline decls before macro expanding";
  { fdef with
    fd_body  = macro_expand_stmt pmap fdef.fd_body
  ; fd_ret   = fdef.fd_ret
  }

let macro_expand_func pmap (func : func_t) =
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

let macro_expand_modul pvar_map (modul : modul_t) fname =
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
    let _loc = li.L.l_loc in
    match li.L.l_val with
    | Binstr(Op(_,_,_))
    | Binstr(Comment(_))
    | Binstr(Load(_,_,_))
    | Binstr(Store(_,_,_))
    | Binstr(Assgn(_,Imm(_),_)) -> [li]

    | If(Pcond(_),_,_) -> failwith "array expansion expects macro-if expanded"
    | For(_,_,_,_)     -> failwith "array expansion expects macro-for expanded"
    | Binstr(Call(_))  -> failwith "array expansion expects calls are expanded"
    | While(wt,fc,stmt) ->
      [ L.{ li with l_val = While(wt,fc,exp_s stmt) } ]
    
    | If(Fcond(_) as c,s1,s2) ->
      [ L.{ li with l_val = If(c,exp_s s1,exp_s s2) } ]
 
    | Binstr(Assgn(d,Src(s),t)) ->
      let (td,_) = d.d_decl in
      let (ts,_) = s.d_decl in
      begin match d.d_idx, s.d_idx, td, ts with
      | Inone, Inone, Arr(Pconst(ub1)), Arr(Pconst(ub2)) ->
        assert (U64.equal ub1 ub2);
        let mk_assgn i =
          let d = {d with d_idx = mk_Iconst(Pconst i)} in
          let s = Src({s with d_idx = mk_Iconst(Pconst i)}) in
          { li with L.l_val = Binstr(Assgn(d,s,t)) }
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
    match linstr.L.l_val with

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
  { linstr with L.l_val = instr' }

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

(* ** Register liveness
 * ------------------------------------------------------------------------ *)

(* *** Liveness information definitions *)

module LI = struct 
  (* hashtable that holds the CFG and the current liveness information *)
  type t = {
    use         : SS.t      Pos.Table.t;
    def         : SS.t      Pos.Table.t;
    succ        : Pos.Set.t Pos.Table.t;
    pred        : Pos.Set.t Pos.Table.t;
    live_before : SS.t      Pos.Table.t;
    live_after  : SS.t      Pos.Table.t;
    str         : string    Pos.Table.t;
  }

  let mk () =
    { use         = Pos.Table.create ()
    ; def         = Pos.Table.create ()
    ; succ        = Pos.Table.create ()
    ; pred        = Pos.Table.create ()
    ; str         = Pos.Table.create ()
    ; live_before = Pos.Table.create ()
    ; live_after  = Pos.Table.create () }

  let enter_fun_pos  = [-1]
  let return_fun_pos = [-2]

  let get_use linfo pos = hashtbl_find_exn linfo.use pp_pos pos 
  let get_def linfo pos = hashtbl_find_exn linfo.def pp_pos pos
  let get_str linfo pos = hashtbl_find_exn linfo.str pp_pos pos
  let get_pred linfo pos =
    Pos.Table.find linfo.pred pos |> Option.value ~default:Pos.Set.empty
  let get_succ linfo pos =
    Pos.Table.find linfo.succ pos |> Option.value ~default:Pos.Set.empty
  let get_live_before linfo pos =
    Pos.Table.find linfo.live_before pos |> Option.value ~default:SS.empty
  let get_live_after linfo pos =
    Pos.Table.find linfo.live_after pos |> Option.value ~default:SS.empty

  let add_succ linfo ~pos ~succ =
    Pos.Table.change linfo.succ pos
      ~f:(function | None   -> Some(Pos.Set.singleton succ)
                   | Some s -> Some(Pos.Set.add s     succ))

  let add_pred linfo ~pos ~pred =
    Pos.Table.change linfo.pred pos
      ~f:(function | None   -> Some(Pos.Set.singleton pred)
                   | Some s -> Some(Pos.Set.add s     pred))

  let pred_of_succ linfo =
    Pos.Table.iteri linfo.succ
      ~f:(fun ~key ~data ->
            Pos.Set.iter data ~f:(fun pos -> add_pred linfo ~pos ~pred:key))

  let succ_of_pred linfo =
    Pos.Table.iteri linfo.pred
      ~f:(fun ~key ~data ->
            Pos.Set.iter data ~f:(fun pos -> add_succ linfo ~pos ~succ:key))

  let pp_set_pos =
    pp_set pp_pos (fun s -> List.sort ~cmp:compare_pos (Pos.Set.to_list s))

  let pp_pos_table pp_data fmt li_ss =
    List.iter
      (List.sort ~cmp:(fun a b -> compare_pos (fst a) (fst b))
         (Pos.Table.to_alist li_ss))
      ~f:(fun (key,data) ->
            F.fprintf fmt "%a -> %a; " pp_pos key pp_data data)

  let pp fmt li =
    F.fprintf fmt
      "use: %a\ndef: %a\nsucc: %a\npred: %a\nlive_before: %a\nlive_after: %a\n"
      (pp_pos_table pp_set_string) li.use
      (pp_pos_table pp_set_string) li.def
      (pp_pos_table pp_set_pos)    li.succ
      (pp_pos_table pp_set_pos)    li.pred
      (pp_pos_table pp_set_string) li.live_before
      (pp_pos_table pp_set_string) li.live_after

  let string_of_instr = function
    | Binstr(bi)          -> fsprintf "%a"               pp_base_instr bi
    | If(Fcond(fc),_,_)   -> fsprintf "if %a {} else {}" pp_fcond fc
    | While(WhileDo,fc,_) -> fsprintf "while %a {}"      pp_fcond fc
    | While(DoWhile,fc,_) -> fsprintf "do {} while %a;"  pp_fcond fc
    | _                   -> fsprintf "string_of_instr: unexpected instruction"

  let traverse_cfg_backward ~f linfo =
    let visited = Pos.Table.create () in
    let rec go pos =
      f pos;
      Pos.Table.set visited ~key:pos ~data:();
      Pos.Set.iter (Pos.Table.find linfo.pred pos
                       |> Option.value ~default:Pos.Set.empty)
        ~f:(fun p -> if Pos.Table.find visited p = None then go p)
    in
    go return_fun_pos

  let dump ~verbose linfo fname =
    let ctr = ref 1 in
    let visited     = Pos.Table.create () in
    let code_string = Pos.Table.create () in
    let code_id     = Pos.Table.create () in
    let node_succ   = Pos.Table.create () in
    let to_string before pos =
      fsprintf "%s%a: %s %s \\n%a"
        (if before then
            fsprintf "%a\\n"         pp_set_string (get_live_before linfo pos)

         else "")
        pp_pos pos
        (get_str linfo pos)
        (if verbose then
           fsprintf "def=%a use=%a "
              pp_set_string (get_def linfo pos)
              pp_set_string (get_use linfo pos)
         else "")
        pp_set_string (get_live_after linfo pos)
    in
    let sb = Buffer.create 256 in
    let rec collect_basic_block pos =
      match HT.find linfo.succ pos with
      | Some(ss) when false -> (* Set.length ss = 1 -> *)
        let succ_pos = Set.min_elt_exn ss in
        if not (HT.mem visited succ_pos) then (
          begin match HT.find linfo.pred succ_pos with
          | Some(ss) when Set.length ss = 1 ->
            Buffer.add_string sb "\\n";
            Buffer.add_string sb (to_string false succ_pos);
            HT.set visited ~key:succ_pos ~data:();
            collect_basic_block succ_pos
          | None | Some(_) -> pos
          end
        ) else (
          pos
        )
      | None | Some(_) -> pos
    in
    let rec go pos =
      HT.set visited ~key:pos ~data:();
      HT.set code_id ~key:pos ~data:!ctr;
      incr ctr;
      Buffer.clear sb;
      Buffer.add_string sb (to_string true pos);
      let pos' = collect_basic_block pos in
      let s = Buffer.to_bytes sb in
      HT.set code_string ~key:pos ~data:s;
      let succs =
        Pos.Table.find linfo.succ pos'
        |> Option.value ~default:Pos.Set.empty
      in
      HT.set node_succ ~key:pos ~data:succs;
      Set.iter succs
        ~f:(fun p -> if Pos.Table.find visited p = None then go p)
    in
    go enter_fun_pos;
    let g = ref G.empty in
    Pos.Table.iteri node_succ
      ~f:(fun ~key ~data ->
            let to_string pos = HT.find_exn code_string pos in
            g := G.add_vertex !g (HT.find_exn code_id key, to_string key);
            Pos.Set.iter data
              ~f:(fun succ ->
                    g := G.add_edge !g (HT.find_exn code_id key, to_string key)
                                       (HT.find_exn code_id succ, to_string succ)));
    let file = open_out_bin fname in
    Dot.output_graph file !g
end

(* *** CFG traversal *)

let update_liveness linfo changed pos =
  let succs = LI.get_succ linfo pos in
  (* if not (Pos.Set.is_empty (Pos.Set.inter !changed succs)) then ( *)
  let live = ref SS.empty in
    (* compute union of live_before of successors *)
    (* F.printf "updating %a with succs: %a\n" pp_pos pos LI.pp_set_pos succs; *)
  Pos.Set.iter succs
    ~f:(fun spos ->
          let live_s = LI.get_live_before linfo spos in
          live := SS.union !live live_s);
  (* update live_{before,after} of this vertex *)
  let live_after = LI.get_live_after linfo pos in
  if not (SS.equal !live live_after) then changed := true;
  let live_before_old = LI.get_live_before linfo pos in
  let def_s = LI.get_def linfo pos in
  let use_s = LI.get_use linfo pos in
  Pos.Table.set linfo.LI.live_after ~key:pos ~data:!live;
  let live_before = SS.union (SS.diff !live def_s) use_s in
  if not (SS.equal live_before live_before_old) then changed := true;
  Pos.Table.set linfo.LI.live_before ~key:pos ~data:live_before

(* *** Liveness information computation *)

let rec init_liveness_instr linfo ~path ~idx ~exit_p instr =
  let pos = path@[idx] in
  let succ_pos = Option.value exit_p ~default:(path@[idx + 1]) in
  let li_use  = linfo.LI.use  in
  let li_def  = linfo.LI.def  in
  let li_str  = linfo.LI.str  in
  (* set use, def, and str *)
  Pos.Table.set li_use ~key:pos ~data:(use_instr instr);
  Pos.Table.set li_def ~key:pos ~data:(def_instr instr);
  Pos.Table.set li_str ~key:pos ~data:(LI.string_of_instr instr);
  (* set succ and recursively initialize blocks in if and while *)
  match instr with

  | Binstr(_) ->
    LI.add_succ linfo ~pos ~succ:succ_pos

  | If(Fcond(_),s1,s2) ->
    init_liveness_block linfo ~path:(pos@[0]) ~entry_p:pos ~exit_p:succ_pos s1;
    init_liveness_block linfo ~path:(pos@[1]) ~entry_p:pos ~exit_p:succ_pos s2
    
  | While(WhileDo,_,s) ->
    if s=[] then (
      LI.add_succ linfo ~pos ~succ:pos
    ) else (
      LI.add_succ linfo ~pos:(pos@[0;List.length s - 1]) ~succ:pos;
    );
    init_liveness_block linfo ~path:(pos@[0]) ~entry_p:pos ~exit_p:succ_pos s
    
  | While(DoWhile,fc,s) ->
    (* the use is associated with a later node *)
    Pos.Table.set li_use ~key:pos ~data:SS.empty;
    Pos.Table.set li_str ~key:pos ~data:"do {";
    (* add node where test and backwards jump happens *)
    let exit_pos = pos@[1] in
    let exit_str = fsprintf "} while %a;" pp_fcond fc in
    Pos.Table.set li_use ~key:exit_pos ~data:(use_instr instr);
    Pos.Table.set li_def ~key:exit_pos ~data:SS.empty;
    Pos.Table.set li_str ~key:exit_pos ~data:exit_str;
    LI.add_succ linfo ~pos:exit_pos ~succ:pos;
    LI.add_succ linfo ~pos:exit_pos ~succ:succ_pos;
    init_liveness_block linfo ~path:(pos@[0]) ~entry_p:pos ~exit_p:exit_pos s

  | If(Pcond(_),_,_)
  | For(_,_,_,_)     -> failwith "liveness analysis: unexpected instruction"

and init_liveness_block linfo ~path ~entry_p ~exit_p stmt =
  let rec go ~path ~idx = function
    | [] -> failwith "liveness analysis: impossible case"
    | [i] ->
      init_liveness_instr linfo ~path ~idx ~exit_p:(Some exit_p) i.L.l_val
    | i::s ->
      init_liveness_instr linfo ~path ~idx ~exit_p:None i.L.l_val;
      go ~path ~idx:(idx+1) s
  in
  if stmt = [] then (
    (* empty statement goes from entry to exit *)
    LI.add_succ linfo ~pos:entry_p ~succ:exit_p
  ) else (
    (* initialize first node *)
    let first_pos = path@[0] in
    LI.add_succ linfo ~pos:entry_p ~succ:first_pos;
    (* initialize statements *)
    go ~path ~idx:0 stmt
  )

let compute_liveness_stmt linfo stmt ~enter_def ~return_use =
  let ret_pos = LI.return_fun_pos in
  let enter_pos = LI.enter_fun_pos in
  (* initialize return node *)
  let ret_str = fsprintf "return %a" (pp_list "," pp_string) return_use in
  Pos.Table.set linfo.LI.str ~key:ret_pos ~data:ret_str;
  Pos.Table.set linfo.LI.use ~key:ret_pos ~data:(SS.of_list return_use);
  Pos.Table.set linfo.LI.def ~key:ret_pos ~data:(SS.empty);
  (* initialize function args node *)
  let args_str = fsprintf "enter %a" (pp_list "," pp_string) enter_def in
  Pos.Table.set linfo.LI.str ~key:enter_pos ~data:args_str;
  Pos.Table.set linfo.LI.use ~key:enter_pos ~data:(SS.empty);
  Pos.Table.set linfo.LI.def ~key:enter_pos ~data:(SS.of_list enter_def);
  (* compute CFG into linfo *)
  init_liveness_block linfo ~path:[] stmt
    ~entry_p:enter_pos
    ~exit_p:ret_pos;
  (* add backward edges to CFG *)
  LI.pred_of_succ linfo;
  (* set liveness information in live_info *)
  let cont = ref true in
  (* let changed_initial = Pos.Set.singleton LI.return_fun_pos in *)
  let use_return = LI.get_use linfo ret_pos in
  Pos.Table.set linfo.LI.live_before ~key:ret_pos ~data:use_return;
  while !cont do
    print_endline "iterate";
    (* let changed = ref changed_initial  in *)
    let changed = ref false in
    LI.traverse_cfg_backward ~f:(update_liveness linfo changed) linfo;
    if not !changed then cont := false;
    (* if Pos.Set.equal !changed changed_initial then cont := false; *)
    print_endline "iterate done"
  done

let compute_liveness_fundef fdef arg_defs =
  let linfo = LI.mk () in
  let stmt = fdef.fd_body in
  compute_liveness_stmt linfo stmt ~enter_def:arg_defs ~return_use:fdef.fd_ret;
  linfo

let compute_liveness_func func =
  let args_def = List.map ~f:(fun (_,n,_) -> n) func.f_args in
  let fdef = match func.f_def with
    | Def fd -> fd
    | Undef  -> failwith "Cannot add liveness annotations to undefined function"
    | Py(_)  -> failwith "Cannot add liveness annotations to python function"
  in
  compute_liveness_fundef fdef args_def

let compute_liveness_modul modul fname =
  match List.find modul.m_funcs ~f:(fun f -> f.f_name = fname) with
  | Some func -> compute_liveness_func func
  | None      -> failwith "compute_liveness: function with given name not found"

(* ** Collect equality and fixed register constraints from +=, -=, :=, ...
 * ------------------------------------------------------------------------ *)

module REGI = struct
  type t = {
    class_of : string        String.Table.t;
    rank_of  : int           String.Table.t;
    fixed    : (int * L.loc) String.Table.t;
  }

  let mk () = {
    class_of = String.Table.create ();
    rank_of  = String.Table.create ();
    fixed    = String.Table.create ();
  }

  let rec class_of rinfo name =
    match HT.find rinfo.class_of name with
    | None -> name
    | Some(p_name) ->
      let e_name = class_of rinfo p_name in
      if name<>p_name then HT.set rinfo.class_of ~key:name ~data:e_name;
      e_name

  let get_classes rinfo =
    let classes = String.Table.create () in
    let keys = HT.keys rinfo.class_of in
    List.iter keys
      ~f:(fun n ->
            let r = class_of rinfo n in 
            HT.change classes r
              ~f:(function | None     -> Some(SS.singleton n)
                           | Some(ss) -> Some(SS.add ss n)));
    classes

  let rank_of rinfo name =
    match HT.find rinfo.rank_of name with
    | None    -> 0
    | Some(r) -> r

  let fix_class rinfo d reg =
    let s = class_of rinfo d.d_name in
    match HT.find rinfo.fixed s with
    | None ->
      HT.set rinfo.fixed ~key:s ~data:(reg,d.d_loc)
    | Some(reg',_) when reg = reg' -> ()
    | Some(reg',loc') ->
      failtype_ loc' "conflicting requirements: %a vs %a for %s"
        X64.pp_int_reg reg' X64.pp_int_reg reg d.d_name

  let union_fixed fixed ~keep:s1 ~merge:s2 =
    match HT.find fixed s1, HT.find fixed s2 with
    | _, None -> ()
    | None, Some(r2) ->
      HT.remove fixed s2;
      HT.set fixed ~key:s1 ~data:r2
    | Some(r1), Some(r2) when r1 = r2 ->
      HT.remove fixed s2; 
    | Some(r1,_), Some(r2,_) ->
      failwith_ "conflicting requirements: %a vs %a for %s and %s"
        X64.pp_int_reg r1 X64.pp_int_reg r2 s1 s2

  let union_class rinfo d1 d2 =
    let root1 = class_of rinfo d1.d_name in
    let root2 = class_of rinfo d2.d_name in
    if root1<>root2 then (
      let rank1 = rank_of rinfo root1 in
      let rank2 = rank_of rinfo root2 in
      match () with
      | _ when rank1 < rank2 ->
        HT.set rinfo.class_of ~key:root1 ~data:root2;
        union_fixed rinfo.fixed ~keep:root2 ~merge:root1
      | _ when rank2 < rank1 ->
        HT.set rinfo.class_of ~key:root2 ~data:root1;
        union_fixed rinfo.fixed ~keep:root1 ~merge:root2
      | _ ->
        HT.set rinfo.class_of ~key:root1 ~data:root2;
        union_fixed rinfo.fixed ~keep:root2 ~merge:root1;
        HT.set rinfo.rank_of  ~key:root2 ~data:(rank2 + 1)
    )

  let pp_fixed fmt (i,_l) = X64.pp_int_reg fmt i

  let pp fmt rinfo =
    F.fprintf fmt
      ("classes: %a\n"^^"ri_fixed: %a\n")
      (pp_ht ", "  "->" pp_string pp_set_string)  (get_classes rinfo)
      (pp_ht ", "  "->" pp_string pp_fixed) rinfo.fixed

end

let reg_info_binstr rinfo bi =
  let is_reg_dest d =
    let (t,s) = d.d_decl in
    if s = Reg
    then ( assert (t = U64 && d.d_idx=inone); true )
    else ( false )
  in
  let is_reg_src s =
    match s with
    | Imm(_) -> assert false
    | Src(d) -> is_reg_dest d
  in
  let reg_info_op op ds ss =
    match view_op op ds ss with

    | V_Umul(d1,d2,s1,_)
      when is_reg_dest d1 && is_reg_dest d2 && is_reg_src s1 ->
      REGI.union_class rinfo (get_src_dest_exn s1) d2;
      REGI.fix_class rinfo d2 (X64.int_of_reg X64.RAX);
      REGI.fix_class rinfo d1 (X64.int_of_reg X64.RDX)

    | V_Carry(_,_,d2,s1,_,_)
      when is_reg_dest d2 && is_reg_src s1 ->
      REGI.union_class rinfo (get_src_dest_exn s1) d2

    | V_ThreeOp(_,d1,s1,_)
    | V_Cmov(_,d1,s1,_,_)
    | V_Shift(_,_,d1,s1,_) when is_reg_dest d1 && is_reg_src s1 ->
      REGI.union_class rinfo (get_src_dest_exn s1) d1

    | V_ThreeOp(O_Imul,_,_,Imm(_))-> ()

    | V_Umul(d1,_,_,_)      -> failtype_ d1.d_loc "reg-alloc"
    | V_ThreeOp(_,d1,_,_)   -> failtype_ d1.d_loc "reg-alloc"
    | V_Carry(_,_,d1,_,_,_) -> failtype_ d1.d_loc "reg-alloc"
    | V_Cmov(_,d1,_,_,_)    -> failtype_ d1.d_loc "reg-alloc"
    | V_Shift(_,_,d1,_,_)   -> failtype_ d1.d_loc "reg-alloc"
  in
  match bi with

  | Op(o,ds,ss) ->
    reg_info_op o ds ss

  (* add equality constraint *)
  | Assgn(d,s,Eq) when is_reg_dest d ->
    begin match s with
    | Imm(_) -> assert false
    | Src(s) -> ignore(REGI.union_class rinfo s d)
    end

  | Load(_,_,_)
  | Assgn(_,_,_)        
  | Store(_,_,_)
  | Comment(_)   -> ()

  | Call(_) -> failwith "inline calls before register allocation"

let rec reg_info_instr rinfo li =
  let ri_stmt = reg_info_stmt rinfo in
  match li.L.l_val with
  | Binstr(bi)         -> reg_info_binstr rinfo bi
  | While(_,_fc,s)     -> ri_stmt s
  | If(Fcond(_),s1,s2) -> ri_stmt s1; ri_stmt s2

  | If(Pcond(_),_,_)
  | For(_,_,_,_)     -> failwith "register allocation: unexpected instruction"

and reg_info_stmt rinfo stmt =
  List.iter ~f:(reg_info_instr rinfo) stmt

let reg_info_func rinfo func fdef =
  let fix_regs_args rinfo =
    let arg_len  = List.length func.f_args in
    let arg_regs = List.take X64.arg_regs arg_len in
    if List.length arg_regs < arg_len then (
      let arg_max  = List.length X64.arg_regs in
      failwith_ "register_alloc: at most %i arguments supported" arg_max
    );
    List.iter (List.zip_exn func.f_args arg_regs)
      ~f:(fun ((s,n,t),arg_reg) ->
            assert (s = Reg && t = U64);
            REGI.fix_class rinfo (mk_dest_name n Reg U64) (X64.int_of_reg arg_reg))
  in
  let fix_regs_ret rinfo =
    let ret_extern_regs = List.map ~f:X64.int_of_reg X64.[RAX; RDX] in
    let ret_len = List.length fdef.fd_ret in
    let ret_regs = List.take ret_extern_regs ret_len in
    if List.length ret_regs < ret_len then (
      let ret_max = List.length ret_extern_regs in
      failwith_ "register_alloc: at most %i arguments supported" ret_max
    );
    List.iter (List.zip_exn fdef.fd_ret ret_regs)
      ~f:(fun (n,ret_reg) -> REGI.fix_class rinfo (mk_dest_name n Reg U64) ret_reg)
  in

  fix_regs_args rinfo;
  fix_regs_ret rinfo;
  reg_info_stmt rinfo fdef.fd_body
  (* F.printf "\n%a\n%!" REGI.pp rinfo *)

(* ** Register allocation
 * ------------------------------------------------------------------------ *)

(* lower registers are special purpose, so we take the maximum free one *)
let max_not_in reg_num rs =
  let module E = struct exception Found of unit end in
  let ri = ref (reg_num - 1) in
  let lrs = List.rev @@ Int.Set.to_list rs in
  (try (
    List.iter lrs ~f:(fun i -> if i = !ri then decr ri else raise (E.Found()))
   ) with
    E.Found() -> ()
  );
  if !ri >= 0 then (
    assert (not (Int.Set.mem rs !ri));
    !ri
  ) else
    failwith "Cannot find free register"

let assign_reg reg_num denv conflicts classes rinfo cur_pos name =
  let dbg = ref false in
  let watch_list =
    ["bit_3__0";"j_3__0";"swap_3__0";]
  in
  match Map.find denv name with
  | Some(U64,Reg) ->
    (* F.printf "assigning register to %s @@ %a\n" n pp_pos cur_pos; *)
    let cl = REGI.class_of rinfo name in
    if List.mem watch_list name || List.mem watch_list cl
    then (
      dbg := true;
      F.printf "Here we are: %s %a\n%!" name pp_pos cur_pos
    );
    let ofixed = HT.find rinfo.REGI.fixed cl in
    if !dbg then F.printf "  in class %s fixed to %a\n%!" cl (pp_opt "-" REGI.pp_fixed) ofixed;
    let class_name = HT.find classes cl |> Option.value ~default:(SS.singleton cl) in
    let conflicted = ref SS.empty in
    SS.iter class_name
      ~f:(fun n ->
            conflicted :=
              SS.union !conflicted
                (HT.find conflicts n
                 |> Option.value ~default:SS.empty
                 |> SS.filter ~f:(fun n -> let (t,s) = Map.find_exn denv n in s = Reg && t = U64)
                ));
    let conflicted = !conflicted in
    if !dbg then F.printf "  conflicted with %a\n%!" pp_set_string conflicted;
    let f n = Option.map ~f:fst (HT.find rinfo.REGI.fixed (REGI.class_of rinfo n)) in
    let conflicted_fixed = Int.Set.of_list @@ List.filter_map ~f (SS.to_list conflicted) in
    if !dbg then
      F.printf "  conflicted with fixed %a\n%!"
        (pp_list "," X64.pp_int_reg) (Set.to_list conflicted_fixed);
    begin match ofixed with
    | None ->
      let ri = max_not_in reg_num conflicted_fixed in
      REGI.fix_class rinfo (mk_dest_name cl U64 Reg) ri;
      if !dbg then F.printf "  fixed register to %a\n%!" X64.pp_int_reg ri
    | Some(ri,l) ->
      if Set.mem conflicted_fixed ri then (
        F.printf "\n\nERROR:\n\n%!";
        F.printf "  reg %s in class %s fixed to %a\n%!" name cl (pp_opt "-" REGI.pp_fixed) ofixed;
        F.printf "  conflicted with %a\n%!" pp_set_string conflicted;
        let f n =
          Option.bind (HT.find rinfo.REGI.fixed (REGI.class_of rinfo n))
            (fun (i,_) -> if i = ri then Some (n,i) else None)
        in
        let conflicted_fixed = List.filter_map ~f (SS.to_list conflicted) in
        F.printf "  conflicted with fixed %a\n%!"
          (pp_list "," (pp_pair ":" pp_string X64.pp_int_reg)) conflicted_fixed;
        
        failtype_ l "assign_reg: conflict between fixed register"
      )
    end

  | None -> assert false

  | Some(_t,_s) -> ()
    (* F.printf "ignoring %s with %a %s\n" n pp_ty t (string_of_storage s) *)

let assign_regs reg_num denv conflicts linfo rinfo =
  let visited = Pos.Table.create () in
  let visit   = ref [LI.enter_fun_pos] in
  let classes = REGI.get_classes rinfo in

  while !visit<>[] do
    let cur_pos,rem_pos = match !visit with p::ps -> (p,ps) | [] -> assert false in
    visit := rem_pos;
    if not (HT.mem visited cur_pos) then (
      HT.set visited ~key:cur_pos ~data:();
      (* get defined variables *)
      let defs = SS.to_list @@ LI.get_def linfo cur_pos in
      List.iter defs ~f:(assign_reg reg_num denv conflicts classes rinfo cur_pos);
      visit := !visit @ (Set.to_list @@ LI.get_succ linfo cur_pos)
    )
  done

let reg_alloc_func reg_num func =
  assert (func.f_call_conv = Extern);
  let rename denv rinfo name =
    match Map.find denv name with
    | None -> assert false
    | Some(U64,Reg) ->
      let cl = REGI.class_of rinfo name in
      let ri = fst @@ HT.find_exn rinfo.REGI.fixed cl in
      fsprintf "r_%i_%a" ri X64.pp_int_reg ri
    | Some(_,_) ->
      name
  in
  let extract_conflicts linfo conflicts ~key:pos ~data:live_set =
    let defs = LI.get_def linfo pos in
    SS.iter (SS.union live_set defs)
      ~f:(fun n ->
            let live_set = SS.remove live_set n in
            HT.change conflicts n
              ~f:(function | None     -> Some(live_set)
                           | Some(ls) -> Some(SS.union live_set ls)))
  in

  (* compute equality constraints and fixed constraints *)
  let rinfo = REGI.mk () in
  let fd = get_fundef ~err_s:"perform register allocation" func in
  reg_info_func rinfo func fd;

  (* compute liveness information *)
  let linfo = compute_liveness_func func in
  let conflicts = String.Table.create () in
  HT.iteri linfo.LI.live_after ~f:(extract_conflicts linfo conflicts);
  let denv = IT.denv_of_func func (IT.extract_decls func.f_args fd) in
  assign_regs reg_num denv conflicts linfo rinfo;
  rename_func (rename denv rinfo) func
  
let reg_alloc_modul reg_num modul fname =
  map_fun ~f:(reg_alloc_func reg_num) modul fname

(* PRE: We assume the code is in SSA. *)
(*
let register_allocate _nregs _efun0 = 
  let module E = struct exception PickExc of string end in

  (* Set of free registers: 0 .. nregs -1 *)
  let free_regs = ref (Int.Set.of_list (List.init nregs ~f:(fun i -> i))) in
  let free_regs_add i =
    assert (not (Set.mem !free_regs i));
    free_regs := Set.add !free_regs i
  in
  let free_regs_remove i =
    assert (Set.mem !free_regs i);
    free_regs := Set.remove !free_regs i
  in

  (* mapping from pseudo registers to integers 0 .. nreg-1 denoting machine registers *)
  let reg_map = Preg.Table.create () in
  let int_to_preg i = mk_preg_u64 (fsprintf "%%%i" i) in
  let get_reg pr = int_to_preg (hashtbl_find_exn reg_map pp_preg_ty pr) in

  (* track pseudo-registers that require a fixed register *)
  let fixed_pregs = Preg.Table.create () in
  let pick_free pr =
    match HT.find fixed_pregs pr with
    | Some ri ->
      if Set.mem !free_regs ri then (
        HT.set reg_map ~key:pr ~data:ri;
        free_regs_remove ri;
        ri
      ) else (
        let err =
          fsprintf
            "required register %s (%s) for %a already in use\nfree registers: [%a]\nmap: %a"
            (X64.string_of_reg (X64.reg_of_int ri))
            ((int_to_preg ri).pr_name)
            pp_preg pr
            (pp_list "," pp_int) (Set.to_list !free_regs)
            (pp_list "," (pp_pair "->" pp_preg pp_int))
            (HT.to_alist reg_map)
        in
        raise (E.PickExc err)
      )
    | None ->
      begin match Set.max_elt !free_regs with
      | None -> raise (E.PickExc "no registers left")
      | Some i ->
        HT.set reg_map ~key:pr ~data:i;
        free_regs_remove i;
        i
      end
  in
  let trans_src = function
    | Simm(_) as i -> i
    | Sreg(pr)     -> Sreg(get_reg pr)
    | Smem(pr,o)   -> Smem(get_reg pr,o)
  in
  let trans_dest d =
    let get pr =
      match HT.find reg_map pr with
      | None   -> int_to_preg (pick_free pr)
      | Some i -> int_to_preg i
    in
    match d with
    | Dreg(pr)   -> Dreg(get pr)
    | Dmem(pr,o) -> Dmem(get pr,o)
  in

  let free_dead_regs read_after_rhs =
    let remove_dead pr i =
      if not (Set.mem read_after_rhs pr)
      then ( free_regs_add i; false )
      else true
    in
    HT.filteri_inplace reg_map ~f:remove_dead
  in
  let rec alloc left right =
    match right with
    | [] -> List.rev left
    | {li_bi = bi; li_read_after_rhs = read_after_rhs}::right ->
      (* F.printf "reg_alloc: %a\n" pp_base_instr bi; *)
      let bi =
        try
          begin match bi with
          | Comment(_) -> bi

          (* enforce dst = src1 and do not allocate registers for carry flag *)
          | App((Add|Sub) as o,(([_;Dreg(d)] | [Dreg(d)]) as ds),(Sreg(s1)::s2::cfin)) ->
            let r1 = hashtbl_find_exn reg_map pp_preg_ty s1 in
            let s1 = trans_src (Sreg s1) in
            let s2 = trans_src s2        in
            free_dead_regs read_after_rhs;
            HT.set fixed_pregs ~key:d  ~data:r1;
            let d = trans_dest (Dreg d) in
            App(o,(linit ds)@[d],s1::s2::cfin)

          | App(Add,_,_) -> assert false

          | App(Cmov(_) as o,[Dreg(d)],[Sreg(s1);s2;cfin]) ->
             let r1 = hashtbl_find_exn reg_map pp_preg_ty s1 in
             let s1 = trans_src (Sreg(s1)) in
             let s2 = trans_src s2        in
             free_dead_regs read_after_rhs;
             HT.set fixed_pregs ~key:d  ~data:r1;
             let d = trans_dest (Dreg d) in
             App(o,[d],[s1;s2;cfin])

          | App(Cmov(_),_,_) -> assert false

          | App(o,ds,ss) ->
             let ss = List.map ~f:trans_src ss in
             free_dead_regs read_after_rhs;
             let ds = List.map ~f:trans_dest ds in
             App(o,ds,ss)
          end
        with
          E.PickExc s ->
            F.printf "\nRegister allocation failed:\n%s\n" s;
            F.printf "\nhandled:\n%a\n" (pp_list "\n" pp_base_instr) (List.rev left);
            F.printf "\nfailed for:\n%a\n" pp_base_instr bi;
            F.printf "\nremaining:\n%a\n%!"
              (pp_list "\n" pp_base_instr) (List.map ~f:(fun li -> li.li_bi) right);
            raise (E.PickExc s)
      in
      (* F.printf "reg_alloc_done: %a\n" pp_base_instr bi; *)
      alloc (bi::left) right
  in

  let () =
    let (eq_classes, fixed_classes, _class_map) =
      eq_constrs (stmt_to_base_instrs efun0.ef_body) (failwith "efun0.ef_args")
    in
    (* register %rax and %rdx for mul *)
    HT.iter fixed_classes
      ~f:(fun ~key:i ~data:reg ->
            let pregs = hashtbl_find_exn eq_classes pp_int i in
            (* F.printf "## using %s for %a\n" (X64.string_of_reg reg) (pp_list "," pp_preg)
                (Set.to_list pregs); *)
            Set.iter pregs ~f:(fun preg ->
              HT.set fixed_pregs ~key:preg  ~data:(X64.(int_of_reg reg)))
      );

    if efun0.ef_extern then (
      (* directly use the ABI argument registers for arguments *)
      let arg_len = List.length efun0.ef_args in
      let arg_regs = List.take (List.map ~f:X64.int_of_reg X64.arg_regs) arg_len in
      let arg_max = List.length X64.arg_regs in
      if List.length arg_regs < arg_len then
        failwith (fsprintf "register_alloc: at most %i arguments supported" arg_max);
      (* List.iter (List.zip_exn efun0.ef_args arg_regs)
        ~f:(fun (arg,arg_reg) -> HT.set fixed_pregs ~key:arg ~data:arg_reg);
      *)

      (* directly use the ABI return registers for return values *)
      let ret_extern_regs = List.map ~f:X64.int_of_reg X64.[RAX; RDX] in
      let ret_len = List.length efun0.ef_ret in
      let ret_regs = List.take ret_extern_regs ret_len in
      let ret_max = List.length ret_extern_regs in
      if List.length ret_regs < ret_len then
        failwith (fsprintf "register_alloc: at most %i arguments supported" ret_max);
      List.iter (List.zip_exn efun0.ef_ret ret_regs)
        ~f:(fun (ret,ret_reg) -> HT.set fixed_pregs ~key:ret ~data:ret_reg)
    )
  in
  let args = List.map efun0.ef_args ~f:(fun pr -> int_to_preg (pick_free pr)) in
  let bis = alloc [] (register_liveness efun0) in
  let efun =
    { efun0 with
      ef_args = args;
      ef_body = base_instrs_to_stmt bis;
      ef_ret  = List.map ~f:(fun pr -> get_reg pr) efun0.ef_ret;
    }
  in
  (*validate_transform efun0 efun;*)
  efun *)

(* ** Translation to assembly
 * ------------------------------------------------------------------------ *)

let to_asm_x64 _efun =
  failwith "undefined"
  (*
  let mreg_of_preg pr =
    let fail () =
      failwith
        (fsprintf "to_asm_x64: expected register of the form %%i, got %a" pp_preg_ty pr)
    in
    let s = if pr_is_indexed pr then fail () else pr.pr_name in
    let i =
      try
        begin match String.split s ~on:'%' with
        | ""::[s] -> int_of_string s
        | _       -> fail ()
        end
      with
      | Failure "int_of_string" -> fail ()
    in
    X64.reg_of_int i
  in
  let ensure_dest_mreg d mr msg =
    match d with
    | Dreg(pr) when mreg_of_preg pr = mr -> ()
    | _                                  -> failwith msg
  in
  let ensure_src_mreg s mr msg =
    match s with
    | Sreg(pr) when mreg_of_preg pr = mr -> ()
    | _                                  -> failwith msg
  in
  let ensure c msg = if not c then failwith ("to_asm_x64: "^msg) in
  let trans_cexpr = function
    | Cconst(i) -> i
    | Cvar(_)
    | Cbinop(_) ->
      failwith "to_asm_x64: cannot translate non-constant c-expressions"
  in
  let trans_src = function
    | Sreg(r)    -> X64.Sreg(mreg_of_preg r)
    | Simm(i)    -> X64.Simm(i)
    | Smem(r,ie) -> X64.Smem(mreg_of_preg r,trans_cexpr ie)
  in
  let trans_dest = function
    | Dreg(r)    -> X64.Dreg(mreg_of_preg r)
    | Dmem(r,ie) -> X64.Dmem(mreg_of_preg r,trans_cexpr ie)
  in
  let trans bi =
    let c = X64.Comment (fsprintf "mil: %a" pp_base_instr bi) in
    match bi with

    | Comment(s) ->
      [X64.Comment(s)]

    | App(Assgn,[d],[s]) ->
      [c; X64.( Binop(Mov,trans_src s,trans_dest d) )]

    | App(UMul,[dh;dl],[s1;s2]) ->
      ensure_dest_mreg dh X64.RDX "mulq high result must be %rdx";
      ensure_dest_mreg dl X64.RAX "mulq low result must be %rax";
      ensure_src_mreg  s1 X64.RAX "mulq source 1 must be %rax";

      let instr = X64.( Unop(Mul,trans_src s2) ) in
      [c;instr]

    | App(IMul,[dl],[s1;s2]) ->
      ensure (not (is_src_imm s1))  "imul source 1 cannot be immediate";
      ensure (is_src_imm s2)  "imul source 2 must be immediate";
      ensure (is_dest_reg dl) "imul dest must be register";
      [c; X64.( Triop(IMul,trans_src s2,trans_src s1,trans_dest dl) )]

    | App(Cmov(CfSet(b)),[d],[s1;s2;_cin]) ->
      ensure (equal_src (dest_to_src d) s1) "cmov with dest<>src1";
      let instr = X64.( Binop(Cmov(CfSet(b)),trans_src s2,trans_dest d) ) in
      [c; instr]

    | App(Shift(dir),[d],[s1;s2]) ->
      ensure (equal_src (dest_to_src d) s1) "shift with dest<>src1";
      ensure (is_src_imm s2)  "shift source 2 must be immediate";
      let op = match dir with Right -> X64.Shr | Left -> X64.Shl in
      let instr = X64.( Binop(op,trans_src s2,trans_dest d) )  in
      [c;instr]

    | App(Xor,[d],[s1;s2]) ->
      ensure (equal_src (dest_to_src d) s1) "add/sub with dest<>src1";
      let instr = X64.( Binop(Xor,trans_src s2,trans_dest d) )  in
      [c;instr]

    | App(op,([_;d] | [d]),s1::s2::cin) ->
      ensure (equal_src (dest_to_src d) s1) "add/sub with dest<>src1";
      let instr =
        match op,cin with
        | Add,  []  -> X64.( Binop(Add,trans_src s2,trans_dest d) )
        | Add,  [_] -> X64.( Binop(Adc,trans_src s2,trans_dest d) )
        | BAnd, []  -> X64.( Binop(And,trans_src s2,trans_dest d) )
        | BAnd, [_] -> assert false
        | Sub,  []  -> X64.( Binop(Sub,trans_src s2,trans_dest d) )
        | Sub,  [_] -> X64.( Binop(Sbb,trans_src s2,trans_dest d) )
        | _         -> assert false
      in
      [c; instr]

    | _ -> assert false
  in
  let asm_code =
    List.concat_map ~f:trans (stmt_to_base_instrs efun.ef_body)
  in
  X64.(
    { af_name = efun.ef_name;
      af_body = asm_code;
      af_args = failwith "List.map ~f:mreg_of_preg efun.ef_args";
      af_ret  = failwith "List.map ~f:mreg_of_preg efun.ef_ret";
    }
  )
  *)

(* ** Calling convention for "extern" functions
 * ------------------------------------------------------------------------ *)

let push_pop_call_reg op  =
  let call_reg =
    X64.([ X64.Sreg R11;
           Sreg R12;
           Sreg R13;
           Sreg R14;
           Sreg R15;
           Sreg RBX;
           Sreg RBP
         ])
  in
  List.map ~f:(fun reg -> X64.Unop(op,reg)) call_reg

let wrap_asm_function afun =
  let name = "_"^afun.X64.af_name in
  let prefix =
    X64.([ Section "text";
           Global name;
           Label name;
           Binop(Mov,Sreg RSP,Dreg R11);
           Binop(And,Simm (U64.of_int 31),Dreg R11);
           Binop(Sub,Sreg R11,Dreg RSP)
    ]) @ (push_pop_call_reg X64.Push )
  in
  let suffix =
      (List.rev (push_pop_call_reg X64.Pop ))
    @ X64.([ Binop(Add,Sreg R11,Dreg RSP); Ret ])
  in
  prefix @ afun.X64.af_body @ suffix
