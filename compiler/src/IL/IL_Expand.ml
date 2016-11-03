(* * Compilation and source-to-source transformations on IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Util
open Arith
open IL_Lang
open IL_Map
open IL_Iter
open IL_Utils

module X64 = Asm_X64
module MP  = MParser
module HT  = Hashtbl
module IT  = IL_Typing

(* ** Interpreting compile-time expressions and conditions
 * ------------------------------------------------------------------------ *)

let eval_pbinop = function
  | Pplus  -> U64.add
  | Pmult  -> U64.mul
  | Pminus -> U64.sub

let eval_pexpr ptable ltable ce =
  let rec go = function
    | Pbinop(o,ie1,ie2) ->
      begin match go ie1, go ie2 with
      | Result.Ok(x1), Ok(x2) ->
        Ok(eval_pbinop o x1 x2)
      | Error(s), _
      | _, Error(s) ->
        Error(s)
      end
    | Pconst(c) -> Ok c
    | Patom(Pparam(p)) ->
      begin match HT.find ptable p.Param.name with
      | Some (x) -> Ok x
      | None     -> failwith_ "eval_pexpr: parameter %a undefined" Param.pp p
      end
    | Patom(Pvar(v)) ->
      begin match HT.find ltable v.Var.num with
      | Some (Vu64 x) -> Ok x
      | Some (_) ->
        Error (fsprintf "eval_pexpr: variable %a of wrong type" Var.pp v)
      | None ->
        Error (fsprintf "eval_pexpr: variable %a undefined" Var.pp v)
      end
  in
  go ce

let eval_pcondop pc = fun x y ->
  match pc with
  | Peq      -> U64.equal x y
  | Pineq    -> not (U64.equal x y)
  | Pless    -> U64.compare x y < 0
  | Pgreater -> U64.compare x y > 0
  | Pleq     -> U64.compare x y <= 0
  | Pgeq     -> U64.compare x y >= 0

let eval_pcond ptable ltable cc =
  let rec go = function
    | Ptrue              -> Result.Ok(true)
    | Pnot(ic)           ->
      begin match go ic with
      | Ok(c)    -> Ok (not c)
      | Error(s) -> Error(s)
      end
    | Pand(cc1,cc2)      ->
      begin match go cc1, go cc2 with
      | Ok(c1),Ok(c2) -> Ok(c1 && c2)
      | Error(s), _
      | _, Error(s) ->
        Error(s)
      end
    | Pcmp(cco,ce1,ce2) ->
      begin match eval_pexpr ptable ltable ce1, eval_pexpr ptable ltable ce2 with
      | Ok(x1),Ok(x2) -> Ok(eval_pcondop cco x1 x2)
      | Error(s), _
      | _, Error(s) ->
        Error(s)
      end
  in
  go cc

let eval_pexpr_exn ptable ltable ce = 
  eval_pexpr ptable ltable ce |> Result.ok_or_failwith

let eval_pcond_exn ptable ltable cc = 
  eval_pcond ptable ltable cc |> Result.ok_or_failwith

(* ** Simple transformations
 * ------------------------------------------------------------------------ *)
(* *** Reset module info / strip comments *)

let reset_info_modul modul =
  concat_map_modul_all modul
    ~f:(fun loc _pos _oinfo instr ->
          [ { L.l_loc = loc; L.l_val = set_info_instr None instr } ])

let strip_comments_modul modul fname =
  let is_not_Comment lbi =
    match lbi.L.l_val with
    | Comment _ -> false
    | _         -> true
  in
  let strip_comments loc _pos _oinfo instr =
    let instrs = 
      match instr with
      | Block(bis,i) -> [ Block(List.filter ~f:is_not_Comment bis,i) ]
      | instr        -> [ instr ]
    in
    List.map ~f:(fun i -> { L.l_loc=loc; L.l_val=i }) instrs
  in
  concat_map_modul modul fname ~f:strip_comments

(* *** Renumbering Var.num *)

type renumber_opt =
  | UniqueNumModule
  | UniqueNumFun
  | ReuseNum

let renumber_vars_func ?(ctr=ref 1) () func =
  let imap     = Vname_num.Table.create () in
  let rn v =
    let nn = (v.Var.name,v.Var.num) in
    match HT.find imap nn with
    | Some(n) -> { v with Var.num = n }
    | None    ->
      let n = !ctr in
      ctr := succ n;
      HT.set imap ~key:nn ~data:n;
      { v with Var.num = n }
  in
  map_vars_func ~f:rn func

let renumber_vars_func_reuse func =
  let imap     = Vname_num.Table.create () in
  let num_used = Vname.Table.create () in
  let rn v =
    let nn = (v.Var.name,v.Var.num) in
    match HT.find imap nn with
    | Some(n) -> { v with Var.num = n }
    | None    ->
      let n = ref 0 in
      HT.change num_used v.Var.name
        ~f:(function | None    -> n := 0; Some(1)
                     | Some(i) -> n := i; Some(i+1));
      HT.set imap ~key:nn ~data:!n;
      { v with Var.num = !n }
  in
  map_vars_func ~f:rn func

let renumber_vars_named_func ?ctr () nf =
  { nf_name = nf.nf_name;
    nf_func = renumber_vars_func ?ctr () nf.nf_func }


let renumber_vars_named_func_reuse nf =
  { nf_name = nf.nf_name;
    nf_func = renumber_vars_func_reuse nf.nf_func }

let renumber_vars_modul_all rno modul =
  match rno with
  | ReuseNum ->
    List.map ~f:renumber_vars_named_func_reuse modul
  | _ ->
    let rnvf = 
      match rno with
      | UniqueNumModule -> renumber_vars_named_func ?ctr:(Some(ref 1)) ()
      | UniqueNumFun    -> renumber_vars_named_func ?ctr:None ()
      | _ -> assert false
    in
    List.map ~f:rnvf modul
 
(* ** Merge consecutive basic blocks
 * ------------------------------------------------------------------------ *)
(* *** Summary
A statement is a sequence of instructions (Block/If/For/While) where If,
For, While recursively contain statements. This function merges basic
blocks and ensures that all basic blocks are followed by If/For/While or
the last element of a statement.
*)
(* *** Code *)

let finish_block prev_stmt cur_block =
  match List.concat @@ List.rev cur_block with
  | [] -> prev_stmt
  | (lbi_first::_) as bis  ->
    let lbi_last = List.last_exn bis in
    let loc = L.mk_loc (lbi_first.L.l_loc.L.loc_start,lbi_last.L.l_loc.L.loc_end) in
    { L.l_val = Block(bis,None); L.l_loc = loc }::prev_stmt

let merge_blocks_stmt stmt =
  let rec go prev_stmt cur_block linstrs =
    match linstrs with
    | [] -> List.rev @@ finish_block prev_stmt cur_block
    | linstr::linstrs ->
      let mk instr = { linstr with L.l_val = instr } in
      begin match linstr.L.l_val with
      | Block(bs,_) ->
        go prev_stmt (bs::cur_block) linstrs
      | If(c,s1,s2,i) ->
        let s1 = go [] [] s1 in
        let s2 = go [] [] s2 in
        go ((mk @@ If(c,s1,s2,i))::(finish_block prev_stmt cur_block)) [] linstrs
      | For(v,lb,ub,s,i) ->
        let s = go [] [] s in
        go ((mk @@ For(v,lb,ub,s,i))::(finish_block prev_stmt cur_block)) [] linstrs
      | While(wt,c,s,i) ->
        let s = go [] [] s in
        go ((mk @@ While(wt,c,s,i))::(finish_block prev_stmt cur_block)) [] linstrs
      end
  in
  go [] [] stmt  

let merge_blocks_modul modul fname =
  map_body_modul ~f:merge_blocks_stmt modul fname

let merge_blocks_modul_all modul =
  map_body_modul_all ~f:merge_blocks_stmt modul

(* ** Partially evaluate dimension and parameter-expressions
 * ------------------------------------------------------------------------ *)

let peval_param ptable _ p =
  match HT.find ptable p.Param.name with
  | Some(x) -> Pconst(x)
  | None    -> failwith_ "peval_patom: parameter %a undefined" Param.pp p

let peval_patom ptable ltable pa =
  match pa with
  | Pparam(p)     -> peval_param ptable ltable p
  | Pvar(v) as pv ->
    begin match HT.find ltable v.Var.num with
    | Some (Vu64 x) -> Pconst(x)
    | None          -> Patom(pv)
    | Some(_)       ->
      failwith_ "peval_pexpr: variable %a of wrong type" Var.pp v
    end

let peval_pexpr_g peval_atom ptable ltable ce =
  let rec go = function
    | Pbinop(o,e1,e2) ->
      begin match go e1, go e2 with
      | Pconst c1, Pconst c2 ->
        Pconst(eval_pbinop o c1 c2)
      | e1,e2 -> Pbinop(o,e1,e2)
      end
    | Patom(a) -> peval_atom ptable ltable a
    | Pconst(_) as e -> e
  in
  go ce

let peval_pexpr ptable ltable = peval_pexpr_g peval_patom ptable ltable

let peval_dexpr ptable ltable = peval_pexpr_g peval_param ptable ltable

let peval_pcond ptable ltable cc =
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
      begin match peval_pexpr ptable ltable ce1, peval_pexpr ptable ltable ce2 with
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

let rec inline_call func_table ctr fname ds ss =
  let func =
    match hashtbl_find_exn func_table Fname.pp fname with
    | func, true  -> func
    | func, false ->
      let func = inline_calls_func func_table fname func in
      HT.set func_table ~key:fname ~data:(func,true);
      func
  in
  let func = renumber_vars_func ~ctr () func in
  let fdef = get_fundef ~err_s:"inline_call: impossible" func in
  let ret_ss = 
    List.map fdef.f_ret
      ~f:(fun v -> Src({d_var=v; d_idx=None; d_loc=v.Var.uloc;}))
  in
  let arg_ds =
    List.map ~f:(fun v -> {d_var=v; d_idx=None; d_loc=v.Var.uloc}) fdef.f_arg
  in
  let pref = List.map2_exn ~f:(fun d s -> Assgn(d,s,Eq)) arg_ds ss in
  let suff = List.map2_exn ~f:(fun d s -> Assgn(d,s,Eq)) ds ret_ss in

  let pref = Comment("START: inlined call to "^Fname.to_string fname)::pref in
  let suff = suff@[Comment("END: inlined call to "^Fname.to_string fname)] in
  let mk_block bis =
    let lbis = List.map ~f:(fun bi -> {L.l_val=bi; L.l_loc=L.dummy_loc}) bis in
    { L.l_val = Block(lbis,None);
      L.l_loc = L.dummy_loc }
  in
  (mk_block pref)::fdef.f_body@[(mk_block suff)]

and inline_calls_block func_table ctr lbis =
  let rec go prev_stmt lbis =
    match lbis with
    | [] -> List.rev prev_stmt

    | lbi::lbis ->
      begin match lbi.L.l_val with
      | Call(fn,ds,ss) ->
        let fstmt = inline_call func_table ctr fn ds ss in
        let prev_stmt = (List.rev fstmt)@prev_stmt in
        go prev_stmt lbis
        (* NOTE: we don't merge blocks here, this will be tried in inline_calls_stmt *)
      | _ ->
        go ({L.l_val=Block([lbi],None); L.l_loc=lbi.L.l_loc}::prev_stmt) lbis
      end
  in
  go [] lbis

and inline_calls_instr func_table ctr linstr =
  let ilc_s = inline_calls_stmt func_table ctr in
  let instr = linstr.L.l_val in
  let mki i = { linstr with L.l_val = i } in
  let instrs =
    match instr with
    | If(c,s1,s2,i)    -> [ mki @@ If(c,ilc_s s1, ilc_s s2,i) ]
    | For(c,lb,ub,s,i) -> [ mki @@ For(c,lb,ub,ilc_s s,i) ]
    | While(wt,fc,s,i) -> [ mki @@ While(wt,fc,ilc_s s,i) ]
    | Block(lbis,_)    -> inline_calls_block func_table ctr lbis
  in
  instrs

and inline_calls_stmt func_table ctr (stmt : 'info stmt) : 'info stmt =
  merge_blocks_stmt @@ List.concat_map ~f:(inline_calls_instr func_table ctr) stmt

and inline_calls_func func_table (fname : Fname.t) func =
  let fd = match func with
    | Foreign(_) -> failwith_ "cannot inline calls in foreign function %a" Fname.pp fname
    | Native(fd) -> fd
  in
  let max_num = max_var_fundef fd in
  (* F.printf "max: %a\n%!" pp_int64 max_num; *)
  let ctr = ref (succ max_num) in
  let stmt = inline_calls_stmt func_table ctr fd.f_body in
  Native { fd with f_body = stmt }

let inline_calls_modul modul fname =
  (* before inlining a call to f, we inline in f and store the result in func_table  *)
  let func_table =
    List.map ~f:(fun nf -> (nf.nf_name,(nf.nf_func,false))) modul
    |> Fname.Table.of_alist_exn
  in
  map_func ~f:(inline_calls_func func_table fname) modul fname

(* ** Macro expansion: loop unrolling, if, ...
 * ------------------------------------------------------------------------ *)
(* *** Summary
Given values for parameters, perform the following unfolding:
1. evaluate pexpr/dexpr in dimensions and ranges
2. unfold for-loops and if-then-else with parameter-cond
3. evaluate pexpr in indexing
Assumes that there are no function calls in the macro-expanded function.
*)
(* *** Code *)

let inst_ty ptable ty =
  let ltable = Int.Table.create () in
  match ty with
  | TInvalid -> assert false
  | Bool     -> Bool
  | U64      -> U64
  | Arr(dim) -> Arr(peval_dexpr ptable ltable dim)

let inst_var ltable v ~default ~f =
  match HT.find ltable v.Var.num with
  | None          -> default
  | Some(Vu64(u)) -> f @@ Pconst(u)
  | Some(_)       -> assert false

let inst_idx ptable ltable idx =
  match idx with
  | Ivar(v)    -> inst_var ltable v ~default:idx ~f:(fun pe -> Ipexpr pe)
  | Ipexpr(pe) -> Ipexpr(peval_pexpr ptable ltable pe)
  

let inst_dest ptable ltable d =
  { d with
    d_idx = Option.map ~f:(inst_idx ptable ltable) d.d_idx }

let inst_src ptable ltable = function
  | Imm(pe) -> Imm(peval_pexpr ptable ltable pe)
  | Src(d)  ->
    let s = Src(inst_dest ptable ltable d) in
    if d.d_idx<>None then (
      s
    ) else (
      inst_var ltable d.d_var ~default:s ~f:(fun pe -> Imm(pe))
    )

let inst_base_instr ptable ltable lbi =
  let inst_p = peval_pexpr ptable ltable in
  let inst_d = inst_dest   ptable ltable in
  let inst_s = inst_src    ptable ltable in
  let inst_ds = List.map ~f:inst_d in
  let inst_ss = List.map ~f:inst_s in
  let bi = lbi.L.l_val in
  let bi =
    match bi with
    | Comment(_)      -> bi
    | Op(o,ds,ss)     -> Op(o,inst_ds ds,inst_ss ss)
    | Assgn(d,s,t)    -> Assgn(inst_d d,inst_s s,t)
    | Load(d,s,pe)    -> Load(inst_d d,inst_s s,inst_p pe)
    | Store(s1,pe,s2) -> Store(inst_s s1,inst_p pe,inst_s s2)
    | Call(fn,ds,ss)  -> Call(fn,inst_ds ds,inst_ss ss)
  in
  { lbi with L.l_val = bi }

let rec macro_expand_instr ptable ltable linstr =
  let me_s = macro_expand_stmt ptable ltable in
  let inst_bi = inst_base_instr ptable ltable in
  let add_loc instr = { linstr with L.l_val = instr } in
  match linstr.L.l_val with
      
  | Block(lbis,_)         -> [ add_loc @@ Block(List.map ~f:inst_bi lbis,None) ]

  | While(wt,fc,s,_)      -> [ add_loc @@ While(wt,fc,me_s s,None) ]
        
  | If(Fcond(fc),s1,s2,_) -> [ add_loc @@ If(Fcond(fc),me_s s1,me_s s2,None) ]
        
  | If(Pcond(pc),s1,s2,_) ->
    let cond = eval_pcond_exn ptable ltable pc in
    let s = if cond then s1 else s2 in
    me_s s

  | For(iv,lb_ie,ub_ie,s,_) ->
    let lb  = eval_pexpr_exn ptable ltable lb_ie in
    let ub  = eval_pexpr_exn ptable ltable ub_ie in
    assert (U64.compare lb ub <= 0);
    assert (iv.d_idx=None);
    let i_num = iv.d_var.Var.num in
    let res = ref [] in
    let ctr = ref lb in
    let old_val = HT.find ltable i_num in
    while (U64.compare !ctr ub < 0) do
      HT.set ltable ~key:i_num ~data:(Vu64 !ctr);
      let s = me_s s in
      res := s::!res;
      ctr := U64.succ !ctr
    done;
    HT.change ltable i_num ~f:(fun _ -> old_val);
    List.concat @@ List.rev !res

and macro_expand_stmt ptable ltable stmt =
  List.concat_map ~f:(macro_expand_instr ptable ltable) stmt

let macro_expand_native ptable fd =
  vars_num_unique_fundef fd;
  let ltable = Int.Table.create () in
  { fd with f_body = macro_expand_stmt ptable ltable fd.f_body }

let macro_expand_func ptable func =
  (* check that all parameters are given *)
  iter_params_func func ~fparam:(fun p ->
    if not (HT.mem ptable p.Param.name) then
      failloc_ p.Param.loc "all parameters must be given for macro expansion"); 
  let func = map_tys_func ~f:(inst_ty ptable) func in
  match func with
  | Foreign(_) -> func
  | Native(fd) -> Native(macro_expand_native ptable fd)

let macro_expand_modul ptable modul fname =
  map_func ~f:(macro_expand_func ptable) modul fname

let macro_expand_modul_all ptable modul =
  List.map ~f:(fun nf -> { nf with nf_func = macro_expand_func ptable nf.nf_func }) modul

(* ** Expand array assignments *)
(* *** Summary
Replace array assignments 'a = b;' where a, b : u64[n] by
'a[0] = b[0]; ...; a[n-1] = b[n-1];'
FIXME: Would it be easier to replace this by 'for' and perform the
       step before macro-expansion?
*)
(* *** Code *)

let array_assign_expand_basic_instr lbi =
  let bi = lbi.L.l_val in
  match bi with
  | Assgn(d,Src(s),t) ->
    let td = d.d_var.Var.ty in
    let ts = s.d_var.Var.ty in
    begin match d.d_idx, s.d_idx, td, ts with
    | None, None, Arr(Pconst(ub1)), Arr(Pconst(ub2)) ->
      assert (U64.equal ub1 ub2);
      let mk_assgn i =
        let d = {d with d_idx = Some(Ipexpr(Pconst(i))) } in
        let s = Src({s with d_idx = Some(Ipexpr(Pconst(i))) }) in
        { lbi with L.l_val = Assgn(d,s,t) }
      in
      List.map ~f:mk_assgn (list_from_to ~first:U64.zero ~last:ub1)
    | _ -> [lbi]
    end
  | _ -> [lbi]

let array_assign_expand_instr loc _pos _oinfo instr =
  let instr =
    match instr with
    | Block(bis,_) -> Block(List.concat_map ~f:array_assign_expand_basic_instr bis,None)
    | _            -> instr
  in
  [ { L.l_val = instr; L.l_loc = loc } ]
 
let array_assign_expand_modul modul fname =
  concat_map_modul modul fname ~f:array_assign_expand_instr

(* ** Expand arrays *)
(* *** Summary
Replace register arrays by individual registers. For stack arrays,
do the same unless there are array gets with non-constant indexes.
Assumes that there no function calls in the macro-expanded function
and that all inline-loops and ifs have been expanded.
*)
(* *** Code *)

let keep_arrays_non_const_index _fdef =
  undefined ()
(*
  let dests = dests_fundef fdef in
  let non_const_arrays = ref Ident.Set.empty in
  let classify_arrays d = 
    (* if d.d_oidx<>None then F.printf "array: %a\n" pp_dest d; *)
    match d.d_idx with
    | Inone -> ()
    | Iconst(Pconst(_)) -> ()
    | Ireg(di) ->
      non_const_arrays := Set.add !non_const_arrays d.d_id;
      let (s,_) = d.d_decl in
      let (si,_) = di.d_decl in
      begin match s, si with
      | Stack, Reg -> ()
      | _, _ ->
        failwith_
          ("%s: array %a (%s) with non-constant indexes requires stack storage, "
           ^^"index %a (%s) must have reg storage")
          "array expansion"
          pp_ident d.d_id (string_of_storage s)
          pp_ident di.d_id (string_of_storage si)
      end
    | Iconst(pe) ->
      failwith_ "%s: the parameter-expression %a cannot be used as index"
        "array expansion" pp_pexpr pe
  in
  DS.elements dests |> List.iter ~f:classify_arrays;
  !non_const_arrays
*)

let array_expand_stmt _keep_arrays _unique_suffix _stmt =
  undefined ()
(*
  let _rename_var name u =
    fsprintf "%a_%a_%s" pp_ident name pp_uint64 u unique_suffix
  in
  let _update_decl ((t,s) as d) =
    match t with
    | U64 | Bool     -> d
    | Arr(Pconst(_)) -> (U64,s)
    | Arr(_) -> failwith "array expansion: impossible, array bounds are not constants"
  in
  let _ren name idx decl =
    if not (Set.mem keep_arrays name) then
      match idx with
      | Inone             -> name, idx, decl
      | Ireg(_)           -> name, idx, decl
      | Iconst(Pconst(_u)) -> failwith "undefined"
        (*rename_var name u, inone, update_decl decl*)
      | Iconst(pe)        ->
        failwith_ "%s: the parameter-expression %a cannot be used as index"
          "array_expand_stmt" pp_pexpr pe
    else
      name,idx,decl
  in
  undefined ()
  (* dest_map_stmt_t (fun _ -> None) ren stmt *)
*)

let array_expand_fundef _fdef =
  failwith "undefined"
(*
  if fdef.fd_decls<>None then failwith_ "array expand: expected empty decls";
  let fresh_suffix = fresh_suffix_fundef fdef "arr" in
  let keep_arrays = keep_arrays_non_const_index fdef in
  let body = array_expand_stmt keep_arrays fresh_suffix fdef.fd_body in
  { fdef with
    fd_body = body;
    fd_decls = None
  }
*)

(* FIXME: we assume this is an extern function, hence all arguments and
          returned values must have type u64 *)
let array_expand_func _func =
  undefined ()
  (* map_fundef ~err_s:"expand arrays" ~f:array_expand_fundef func *)

let array_expand_modul _modul _fname =
  undefined ()
  (* map_fun modul fname ~f:array_expand_func *)

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

let rec local_ssa_instr _rn_info _linstr =
  failwith "undefined"
  (*
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
  *)

and local_ssa_stmt rn_map stmt =
  List.map ~f:(local_ssa_instr rn_map) stmt

let local_ssa_fundef fdef =
  let rn_info = RNI.mk () in
  let body = local_ssa_stmt rn_info fdef.f_body in
  let ret = failwith  "undefined" (*List.map fdef.fd_ret ~f:(RNI.rename rn_info)*) in
  { fdef with f_body = body; f_ret = ret;}

let local_ssa_func _func =
  failwith "undefined"
  (*
  let func = map_fundef ~err_s:"apply local SSA transformation" ~f:local_ssa_fundef func in
  { func with f_args = List.map ~f:(fun (s,n,t) -> (s,RNI.mk_reg_name n 0,t)) func.f_args }
  *)

let local_ssa_modul _modul _fname =
  undefined ()
  (* map_fun modul fname ~f:local_ssa_func *)
