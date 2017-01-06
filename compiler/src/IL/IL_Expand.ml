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

let eval_pbinop op =
  let open Big_int_Infix in
  match op with
  | Pplus  -> fun x y -> x +! y
  | Pmult  -> fun x y -> x *! y
  | Pminus -> fun x y -> x -! y

let eval_pexpr ptable ltable ce =
  let open Value in
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
      | Some(Vu(_,x))   -> Ok x
      | Some(Varr(_,_)) -> failwith_ "eval_pexpr: array parameter not supported" Param.pp p
      | None            -> failwith_ "eval_pexpr: parameter %a undefined" Param.pp p
      end
    | Patom(Pvar(v)) ->
      begin match HT.find ltable v.Var.num with
      | Some (Value.Vu(n,x)) -> Ok(mod_pow_two x n)
      | Some (_) ->
        failloc_ v.Var.uloc "eval_pexpr: variable %a has wrong type" Var.pp v
      | None ->
        failloc_ v.Var.uloc "eval_pexpr: variable %a undefined" Var.pp v
      end
  in
  go ce

let eval_pcondop pc = fun x y ->
  let open Big_int_Infix in
  match pc with
  | Peq  -> x === y
  | Pneq -> not (x === y)
  | Plt  -> Big_int.compare_big_int x y < 0
  | Pgt  -> Big_int.compare_big_int x y > 0
  | Ple  -> Big_int.compare_big_int x y <= 0
  | Pge  -> Big_int.compare_big_int x y >= 0

let eval_pcond ptable ltable cc =
  let rec go = function
    | Pbool(b) -> Result.Ok(b)
    | Pnot(ic) ->
      begin match go ic with
      | Ok(c)    -> Ok (not c)
      | Error(s) -> Error(s)
      end
    | Pbop(o,cc1,cc2) ->
      begin match go cc1, go cc2 with
      | Ok(c1),Ok(c2) ->
        begin match o with
        | Pand -> Ok(c1 && c2)
        | Por  -> Ok(c1 || c2)
        end
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
      (* we use negative indices for stack variables *)
      let n = if v.Var.stor=Stack then -n else n in
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
    { modul with mod_funcs=List.map ~f:renumber_vars_named_func_reuse modul.mod_funcs }
  | _ ->
    let rnvf = 
      match rno with
      | UniqueNumModule -> renumber_vars_named_func ?ctr:(Some(ref 1)) ()
      | UniqueNumFun    -> renumber_vars_named_func ?ctr:None ()
      | _ -> assert false
    in
    { modul with mod_funcs = List.map ~f:rnvf modul.mod_funcs }
 
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
      let fix_stmt stmt = stmt
        (*
        match stmt with
        | [] -> [ { linstr with L.l_val = Block([],None) } ]
        | _  -> stmt
        *)
      in
      let mk instr = { linstr with L.l_val = instr } in
      begin match linstr.L.l_val with
      | Block(bs,_) ->
        go prev_stmt (bs::cur_block) linstrs
      | If(c,s1,s2,i) ->
        let s1 = fix_stmt @@ go [] [] s1 in
        let s2 = fix_stmt @@ go [] [] s2 in
        go ((mk @@ If(c,s1,s2,i))::(finish_block prev_stmt cur_block)) [] linstrs
      | For(v,lb,ub,s,i) ->
        let s = fix_stmt @@ go [] [] s in
        go ((mk @@ For(v,lb,ub,s,i))::(finish_block prev_stmt cur_block)) [] linstrs
      | While(wt,c,s,i) ->
        let s = fix_stmt @@ go [] [] s in
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
  | Some(Value.Vu(_,x))   -> Pconst(x)
  | Some(Value.Varr(_,_)) -> failwith_ "peval_patom: array parameter %a unsupported" Param.pp p
  | None                  -> failwith_ "peval_patom: parameter %a undefined" Param.pp p

let peval_patom ptable ltable pa =
  match pa with
  | Pparam(p)     -> peval_param ptable ltable p
  | Pvar(v) as pv ->
    begin match HT.find ltable v.Var.num with
    | Some (Value.Vu(_,x)) -> Pconst(x)
    | None                 -> Patom(pv)
    | Some(_) ->
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

let peval_pexpr ptable ltable =
  peval_pexpr_g peval_patom ptable ltable

let peval_dexpr ptable ltable =
  peval_pexpr_g peval_param ptable ltable

let peval_pcond ptable ltable cc =
  let rec go = function
    | Pbool(b) -> Pbool(b)
    | Pnot(ic) ->
      begin match go ic with
      | Pnot(c)  -> c
      | Pbool(b) -> Pbool(not b)
      | c        -> Pnot(c)
      end
    | Pbop(Pand,cc1,cc2) ->
      begin match go cc1, go cc2 with
      | Pbool(true), Pbool(true)   -> Pbool(true)
      | Pbool(false), _
      | _           , Pbool(false) -> Pbool(false)
      | c1, c2                     -> Pbop(Pand,c1,c2)
      end
    | Pbop(Por,cc1,cc2) ->
      begin match go cc1, go cc2 with
      | Pbool(false), Pbool(false) -> Pbool(false)
      | Pbool(true), _
      | _           , Pbool(true) -> Pbool(true)
      | c1, c2                    -> Pbop(Por,c1,c2)
      end
    | Pcmp(cco,ce1,ce2) ->
      begin match peval_pexpr ptable ltable ce1, peval_pexpr ptable ltable ce2 with
      | Pconst(c1), Pconst(c2) ->
        if eval_pcondop cco c1 c2 then Pbool(true) else Pbool(false)
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
      ~f:(fun v -> Src(Sdest({d_var=v; d_idx=None; d_loc=v.Var.uloc;})))
  in
  let arg_ds =
    List.map ~f:(fun v -> Rdest(Sdest({d_var=v; d_idx=None; d_loc=v.Var.uloc}))) fdef.f_arg
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
    List.map ~f:(fun nf -> (nf.nf_name,(nf.nf_func,false))) modul.mod_funcs
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

let inst_ty ptable ltable ty =
  match ty with
  | TInvalid   -> assert false
  | Bty(_)     -> ty
  | Arr(i,dim) -> Arr(i,peval_dexpr ptable ltable dim)

let inst_var ltable v ~default ~f =
  match HT.find ltable v.Var.num with
  | None                -> default
  | Some(Value.Vu(n,u)) -> f n @@ Pconst(u)
  | Some(_)             -> assert false

let inst_idx ptable ltable idx =
  match idx with
  | Ivar(v)    -> inst_var ltable v ~default:idx ~f:(fun _ pe -> Ipexpr pe)
  | Ipexpr(pe) -> Ipexpr(peval_pexpr ptable ltable pe)

let inst_sdest ptable ltable sd =
  { sd with
    d_idx = Option.map ~f:(inst_idx ptable ltable) sd.d_idx }

let inst_rdest ptable ltable d =
  let isd = inst_sdest ptable ltable in
  let ipe = peval_pexpr ptable ltable in
  match d with
  | Mem(sd,pe) -> Mem(isd sd, ipe pe)
  | Sdest(sd)  -> Sdest(isd sd)

let inst_dest ptable ltable d =
  match d with
  | Ignore(_) -> d
  | Rdest(rd) -> Rdest(inst_rdest ptable ltable rd)

let inst_src ptable ltable = function
  | Imm(i,pe) -> Imm(i,peval_pexpr ptable ltable pe)
  | Src(rd)    ->
    let s = Src(inst_rdest ptable ltable rd) in
    begin match rd with
    | Sdest(sd) when sd.d_idx=None ->
      inst_var ltable sd.d_var ~default:s ~f:(fun n pe -> Imm(n,pe))
    | _ -> s
    end

let inst_base_instr ptable ltable lbi =
  let bi = lbi.L.l_val in
  (* let inst_p = peval_pexpr ptable ltable in *)
  let inst_d = inst_dest   ptable ltable in
  let inst_s = inst_src    ptable ltable in
  let inst_ds = List.map ~f:inst_d in
  let inst_ss = List.map ~f:inst_s in
  let bi =
    match bi with
    | Comment(_)      -> bi
    | Op(o,ds,ss)     -> Op(o,inst_ds ds,inst_ss ss)
    | Assgn(d,s,t)    -> Assgn(inst_d d,inst_s s,t)
    (* | Load(d,s,pe)    -> Load(inst_d d,inst_s s,inst_p pe) *)
    (* | Store(s1,pe,s2) -> Store(inst_s s1,inst_p pe,inst_s s2) *)
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
    (* info s; *)
    me_s s

  | For(iv,lb_ie,ub_ie,s,_) ->
    let lb  = eval_pexpr_exn ptable ltable lb_ie in
    let ub  = eval_pexpr_exn ptable ltable ub_ie in
    assert (Big_int.compare_big_int lb ub <= 0);
    assert (iv.d_idx=None);
    (* info s; *)
    let i_num = iv.d_var.Var.num in
    let res = ref [] in
    let ctr = ref lb in
    let old_val = HT.find ltable i_num in
    while (Big_int.compare_big_int !ctr ub < 0) do
      HT.set ltable ~key:i_num ~data:(Value.mk_Vu 64 !ctr);
      let s = me_s s in
      res := s::!res;
      ctr := Big_int.succ_big_int !ctr
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
  iter_params_func func ~f:(fun p ->
    if not (HT.mem ptable p.Param.name) then
      failloc_ p.Param.loc "all parameters must be given for macro expansion");
  let ltable = Int.Table.create () in
  let func = map_tys_func ~f:(inst_ty ptable ltable) func in
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
  | Assgn(Rdest(Sdest(d)),Src(Sdest(s)),t) ->
    let td = d.d_var.Var.ty in
    let ts = s.d_var.Var.ty in
    begin match d.d_idx, s.d_idx, td, ts with
    | None, None, Arr(i,Pconst(ub1)), Arr(j,Pconst(ub2)) ->
      assert (Big_int.eq_big_int ub1 ub2 && i = j);
      let mk_assgn i =
        let d = Sdest{ d with d_idx = Some(Ipexpr(Pconst(i))) } in
        let s = Src(Sdest{s with d_idx = Some(Ipexpr(Pconst(i)))}) in
        { lbi with L.l_val = Assgn(Rdest(d),s,t) }
      in
      List.map ~f:mk_assgn (list_from_to_big_int ~first:Big_int.zero_big_int ~last:ub1)
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

let array_expand_fundef fd =
  (* check that args and ret do not contain arrays, var numbers are unique *)
  List.iter fd.f_ret ~f:(fun v -> assert (v.Var.ty=tu64));
  List.iter fd.f_arg ~f:(fun v -> assert (v.Var.ty=tu64));
  vars_num_unique_fundef fd;

  let ctr = ref (succ (max_var_fundef fd)) in
  let stmt = fd.f_body in

  (* populate non-const table *)
  let non_const_table = Int.Table.create () in
  iter_sdests_stmt stmt ~f:(fun d ->
    match d.d_idx with
    | Some(Ipexpr(Pconst(_))) | None -> ()
    | Some(_) ->
      HT.set non_const_table ~key:d.d_var.Var.num ~data:()
  );

  (* populate mapping table *)
  let const_table = Int.Table.create () in
  iter_sdests_stmt stmt ~f:(fun d ->
    match d.d_idx with
    | Some(Ipexpr(Pconst(_))) ->
      let n = d.d_var.Var.num in
      if (not (HT.mem non_const_table n) &&
          not (HT.mem const_table n)) then (
        let a_size = match d.d_var.Var.ty with
          | Arr(_,Pconst(u)) -> Big_int.int_of_big_int u
          | _                -> assert false
        in
        HT.set const_table ~key:n ~data:!ctr;
        ctr := !ctr + a_size
      )
    | _ -> ()
  );

  (* apply mapping table *)
  let stmt = map_sdests_stmt stmt ~f:(fun d ->
    match d.d_idx with
    | Some(Ipexpr(Pconst(i))) ->
      let n = d.d_var.Var.num in
      begin match HT.find const_table n with
      | Some(base) ->
        let i = Big_int.int_of_big_int i in
        let v = d.d_var in
        { d with
          d_idx = None;
          d_var = { v with Var.num = base + i; Var.ty = tu64}; }
      | None -> d
      end
    | _ -> d)
  in
  { fd with f_body = stmt }

let array_expand_func func =
  match func with
  | Foreign(_) -> assert false
  | Native(fd) -> Native(array_expand_fundef fd)

let array_expand_modul modul fname = 
  map_func ~f:array_expand_func modul fname
