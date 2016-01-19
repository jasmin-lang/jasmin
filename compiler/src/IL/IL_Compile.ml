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

(* ** Partially evaluate expressions
 * ------------------------------------------------------------------------ *)

let peval_pexpr pmap lmap ce =
  let rec go = function
    | Pbinop(o,e1,e2) ->
      begin match go e1, go e2 with
      | Pconst c1, Pconst c2 ->
        Pconst(eval_pbinop o c1 c2)
      | e1,e2 -> Pbinop(o,e1,e2)
      end
    | Pconst(_) as e -> e
    | Pparam(s) as e ->
      begin match Map.find pmap s with
      | Some(x) -> Pconst(x)
      | None    -> e
      end
    | Pvar(s) as e ->
      begin match Map.find lmap s with
      | Some (Vu64 x) -> Pconst(x)
      | Some(_)       -> failwith_ "peval_pexpr: variable %s of wrong type" s
      | None          -> e
      end
  in
  go ce

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
    | Pcond(cco,ce1,ce2) ->
      begin match peval_pexpr pmap lmap ce1, peval_pexpr pmap lmap ce2 with
      | Pconst(c1), Pconst(c2) ->
        if eval_pcondop cco c1 c2 then Ptrue else Pnot(Ptrue)
      | e1,         e2         -> Pcond(cco,e1,e2)
      end
  in
  go cc

(* ** Inline function calls
 * ------------------------------------------------------------------------ *)

let rec inline_call func_map suffix c loc decls fname ds ss =
  let ssuffix = "_"^string_of_int !c^(String.make (suffix + 1) '_') in
  let func = map_find_exn func_map pp_string fname in
  let fdef = match func.f_def with
    | Def d -> d
    | Undef | Py _ -> failwith_ "cannot inline calls in undefined function %s" fname
  in
  let ret_ss = List.map ~f:(fun s -> Src(mk_dest_name (s^ssuffix))) fdef.fd_ret in
  let arg_ds = List.map ~f:(fun (_,s,_) -> mk_dest_name (s^ssuffix)) func.f_args in
  let arg_decls = List.map ~f:(fun (sto,s,ty) -> (sto,s^ssuffix,ty)) func.f_args in
  decls := !decls@arg_decls@(rename_decls (fun s -> s^ssuffix) fdef.fd_decls);
  let stmt = rename_stmt (fun s -> s^ssuffix) fdef.fd_body in
  let stmt = inline_calls_stmt func_map suffix c decls stmt in
  (List.map2_exn ~f:(fun d s -> mk_base_instr loc (Assgn(d,s,Eq))) arg_ds ss)
  @ stmt
  @ (List.map2_exn ~f:(fun d s -> mk_base_instr loc (Assgn(d,s,Eq))) ds ret_ss)

and inline_calls_base_instr func_map (suffix : int) c loc decls bi =
  match bi with
  | Call(fn,ds,ss) ->
    incr c;
    [ { l_val = Binstr(Comment(fsprintf "Start Call: %a" pp_base_instr bi)); l_loc = loc} ]
    @ inline_call func_map suffix c loc decls fn ds ss
    @ [ { l_val = Binstr(Comment(fsprintf "End Call: %a" pp_base_instr bi)); l_loc = loc} ]

  | bi -> [ { l_val = Binstr(bi); l_loc = loc} ]

and inline_calls_instr func_map (suffix : int) c decls (li : instr located) =
  let ilc_s = inline_calls_stmt func_map suffix c decls in
  let instrs =
    match li.l_val with
    | If(c,s1,s2)      -> [{ li with l_val = If(c,ilc_s s1, ilc_s s2)}]
    | For(t,c,lb,ub,s) -> [{ li with l_val = For(t,c,lb,ub,ilc_s s)}]
    | Binstr(bi)       -> inline_calls_base_instr func_map suffix c li.l_loc decls bi
  in
  instrs

and inline_calls_stmt func_map (suffix : int) c decls (s : stmt) : stmt =
  List.concat_map ~f:(inline_calls_instr func_map suffix c decls) s

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
  let decls = ref fdef.fd_decls in
  let stmt = inline_calls_stmt func_map suffix c decls fdef.fd_body in
  let func = { func with f_def =
               Def { fdef with fd_body = stmt; fd_decls = !decls } } in
  Map.add func_map ~key:fname ~data:func

let inline_calls_modul (modul : modul) (fname : string) : modul =
  let func_map =
    String.Map.of_alist_exn (List.map ~f:(fun f -> (f.f_name,f)) modul.m_funcs)
  in
  let func_map = inline_calls_fun func_map fname in
  { modul with m_funcs = Map.data func_map}

(* ** Macro expansion: loop unrolling, if, ...
 * ------------------------------------------------------------------------ *)

let inst_pexpr pmap lmap pe =
  peval_pexpr pmap lmap pe

let inst_ty pmap ty =
  match ty with
  | Bool     -> Bool
  | U64(ope) -> U64(Option.map ope ~f:(inst_pexpr pmap String.Map.empty))

let inst_dest pmap lmap d =
  { d with d_oidx = Option.map d.d_oidx ~f:(inst_pexpr pmap lmap) }

let inst_src pmap lmap = function
  | Src(d)  -> Src(inst_dest pmap lmap d)
  | Imm(pe) -> Imm(inst_pexpr pmap lmap pe)

let inst_op pmap lmap op =
  let inst_d = inst_dest pmap lmap in
  let inst_s = inst_src  pmap lmap in
  match op with
  | ThreeOp(op)       -> ThreeOp(op)
  | Umul(d)           -> Umul(inst_d d)
  | Carry(co,d1o,s1o) -> Carry(co,Option.map d1o ~f:inst_d,Option.map s1o ~f:inst_s)
  | CMov(cmf,s1)      -> CMov(cmf,inst_s s1)
  | Shift(d,d1o)      -> Shift(d,Option.map d1o ~f:inst_d)

let inst_base_instr pmap lmap bi =
  let inst_p = inst_pexpr pmap lmap in
  let inst_d = inst_dest  pmap lmap in
  let inst_s = inst_src   pmap lmap in
  match bi with
  | Op(o,d,(s1,s2)) -> Op(inst_op pmap lmap o,inst_d d,(inst_s s1,inst_s s2))
  | Assgn(d,s,t)    -> Assgn(inst_d d,inst_s s,t)
  | Load(d,s,pe)    -> Load(inst_d d,inst_s s,inst_p pe)
  | Store(s1,pe,s2) -> Store(inst_s s1,inst_p pe,inst_s s2)
  | Comment(_)      -> bi
  | Call(_)         -> failwith "inline calls before macro expansion"

let macro_expand_stmt pmap stmt =
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
    let loc = li.l_loc in
    match li.l_val with

    | Binstr(binstr) -> [mk_base_instr loc (inst_base_instr pmap lmap binstr)]

    | If(ic,st1,st2) ->
      (* F.printf "\n%s %a\n%!" (spaces indent) pp_pcond ic; *)
      let cond = eval_pcond_exn pmap lmap ic in
      let st = if cond then st1 else st2 in
        [bicom loc (comment_if "START: " indent cond ic)]
      @ (List.concat_map ~f:(fun bi -> (expand (indent + 2) lmap bi)) st)
      @ [bicom loc (comment_if "END:   " indent cond ic)]

    | For(Loop,iv,lb_ie,ub_ie,stmt) ->
      let stmt = List.concat_map stmt ~f:(expand (indent + 2) lmap) in
      [{ li with l_val = For(Loop,iv,lb_ie,ub_ie,stmt) }]
        
    | For(Unfold,iv,lb_ie,ub_ie,stmt) ->
      (* F.printf "\n%s %a .. %a\n%!" (spaces indent) pp_pexpr lb_ie pp_pexpr ub_ie;  *)
      let lb  = eval_pexpr_exn pmap lmap lb_ie in
      let ub  = eval_pexpr_exn pmap lmap ub_ie in
      assert (U64.compare lb ub <= 0);
      let body_for_v v =
          [bicom loc (fsprintf "%s%s = %s" (spaces (indent+2)) iv (U64.to_string v))]
        @ (List.concat_map stmt ~f:(expand (indent + 2) (Map.add lmap ~key:iv ~data:(Vu64 v))))
      in
        [bicom loc (comment_while "START:" indent iv lb_ie ub_ie)]
      @ List.concat_map (list_from_to ~first:lb ~last:ub) ~f:body_for_v
      @ [bicom loc (comment_while "END:" indent iv lb_ie ub_ie)]
  in
  List.concat_map ~f:(expand 0 String.Map.empty) stmt

let macro_expand_fundef pmap fdef =
  { fd_decls = List.map fdef.fd_decls ~f:(fun (s,n,ty) -> (s,n,inst_ty pmap ty))
  ; fd_body  = macro_expand_stmt pmap fdef.fd_body
  ; fd_ret   = fdef.fd_ret
  }

let macro_expand_func pmap func =
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

let macro_expand_modul pvar_map modul fname =
  List.iter modul.m_params
    ~f:(fun (n,_) -> if not (Map.mem pvar_map n)
                     then failwith_ "parameter %s not given for expand" n);
  { m_params = [];
    m_funcs  = List.map modul.m_funcs
                 ~f:(fun func -> if func.f_name = fname
                                 then macro_expand_func pvar_map func
                                 else func) }

(* ** Single assignment
 * ------------------------------------------------------------------------ *)

let transform_ssa _efun =
  failwith "undefined"
  (*
  let bis = stmt_to_base_instrs efun.ef_body in
  let counter = ref (U64.of_int 0) in
  let var_map = Preg.Table.create () in
  let get_index pr =
    let r = hashtbl_find_exn var_map pp_preg pr in
    mk_preg_index_u64 "r" r pr.pr_aux
  in
  let new_index pr =
    let c = !counter in
    counter := U64.succ !counter;
    Hashtbl.set var_map ~key:pr ~data:c;
    mk_preg_index_u64 "r" c pr.pr_aux
  in
  let update_src = function
    | Simm(_) as s -> s
    | Sreg(pr)     -> Sreg(get_index pr)
    | Smem(pr,ie)  -> Smem(get_index pr,ie)
  in
  let update_dest = function
    | Dreg(pr)    -> Dreg(new_index pr)
    | Dmem(pr,ie) -> Dmem(get_index pr,ie)
  in
  let rename = function
    | Comment(_) as bi -> bi
    | App(o,ds,ss) -> (* Note: sources must be updated before destinations *)
      (* F.printf ">> %a\n" pp_base_instr bi; *)
      let ss = List.map ~f:update_src ss in
      let ds = List.map ~f:update_dest ds in
      App(o,ds,ss)
  in
  (* perform in the right order *)
  let args = List.map ~f:(fun pr -> new_index pr) efun.ef_args in
  let bis  = List.map ~f:rename bis in
  let rets = List.map ~f:(fun pr -> get_index pr) efun.ef_ret in
  { efun with ef_args = args; ef_body = base_instrs_to_stmt bis; ef_ret = rets; }
  *)

(* ** Validate transformation (assuming that transform_ssa correct)
 * ------------------------------------------------------------------------ *)

let validate_transform _efun0 _edef0 _efun _edef =
  failwith "undefined"
(*
  if not (equal_efun (transform_ssa efun0) (transform_ssa efun)) then (
    (* shrink counter-example *)
   for i = 1 to List.length edef.ef_body do
      let efun0  = shorten_efun i efun0 in
      let efun   = shorten_efun i efun in
      let tefun0 = transform_ssa efun0 in
      let tefun  = transform_ssa efun in
      if not (equal_efun tefun tefun0) then (
        Out_channel.write_all "/tmp/before" ~data:(fsprintf "%a" pp_efun efun0);
        Out_channel.write_all "/tmp/after" ~data:(fsprintf "%a" pp_efun efun);
        Out_channel.write_all "/tmp/before_ssa" ~data:(fsprintf "%a" pp_efun tefun0);
        Out_channel.write_all "/tmp/after_ssa" ~data:(fsprintf "%a" pp_efun tefun);
        failwith "failure: see /tmp/before and /tmp/after for invalid renaming"
      )
    done;
    assert false
  )
*)

(* ** Register liveness
 * ------------------------------------------------------------------------ *)

type live_info = {
  li_bi : base_instr;
  li_read_after_rhs : Dest.Set.t; (* the set of registers that might be read after
                                     the RHS of bi has been evaluated *)
}

(* returns a list of tuples (bi, V) denoting that the instructions
   bi;... depend on the registers V *)
let register_liveness _efun =
  failwith "undefined"
  (*
  let bis = stmt_to_base_instrs efun.ef_body in
  let analz_dest read = function
    | Dreg(r)   -> Set.remove read r
    | Dmem(r,_) -> Set.add    read r
  in
  let analz_src read = function
    | Sreg(r) | Smem(r,_) -> Set.add read r
    | Simm(_) -> read
  in
  let rec go read left right =
    match left, right with
    | [],_ -> right
    | li::lis,ris ->
      begin match li with
      | App(_,ds,ss) ->
        (* first remove variables that are written *)
        let read_after_lhs = List.fold ~f:analz_dest ~init:read ds in

        (* then add variables that are read *)
        let read = List.fold ~f:analz_src  ~init:read_after_lhs ss in
        go read lis ({ li_bi = li; li_read_after_rhs = read_after_lhs}::ris)
      | Comment _ ->
        go read lis ({ li_bi = li; li_read_after_rhs = read }::ris)
      end
  in
  go (Preg.Set.of_list efun.ef_ret) (List.rev bis) []
  *)

(* ** Collect equality constraints from +=, -=, :=, ...
 * ------------------------------------------------------------------------ *)

let eq_constrs _bis _regs =
  failwith "undefined"
  (*
  let eq_classes    = Int.Table.create  () in
  let class_map     = Preg.Table.create () in
  let fixed_classes = Int.Table.create  () in
  let last_index = ref (-1) in

  let new_class pr =
    incr last_index;
    let ci = !last_index in
    Hashtbl.add_exn class_map  ~key:pr ~data:ci;
    Hashtbl.add_exn eq_classes ~key:ci ~data:(Preg.Set.singleton pr);
    ci
  in
  let add_to_class pr_old pr_new =
    let ci = match Hashtbl.find class_map pr_old with
      | Some c -> c
      | None ->
        failwith (fsprintf "eq_constrs_: %a undefined\n%a"
                    pp_preg pr_old
                    (pp_list "," pp_preg)
                    (Hashtbl.keys class_map))
    in
    Hashtbl.add_exn class_map ~key:pr_new ~data:ci;
    Hashtbl.change eq_classes ci
      (function
        | None   -> assert false
        | Some s -> Some (Set.add s pr_new));
    ci
  in
  let fix_class i reg =
    match Hashtbl.find fixed_classes i with
    | None ->
      Hashtbl.set fixed_classes ~key:i ~data:reg
    | Some reg' when reg = reg' -> ()
    | Some reg' ->
      failwith (fsprintf "conflicting requirements: %s vs %s"
                  (X64.string_of_reg reg') (X64.string_of_reg reg))
  in
  let handle_bi = function
   | Comment _ -> ()

   | App((Add|Sub), ([_;Dreg(d)] | [Dreg(d)]), Sreg(s)::_) ->
     (* ignore flags *)
     ignore (add_to_class s d)

   | App(UMul, [Dreg(d1);Dreg(d2)], (Sreg(s1)::_)) ->
     let i1 = new_class d1 in
     let i2 = add_to_class s1 d2 in
     fix_class i1 X64.RDX;
     fix_class i2 X64.RAX;

   | App(CMov _, [Dreg(d)],[Sreg(s1);_s2;_cin]) ->
     ignore (add_to_class s1 d)

   | App((Add|Sub|UMul|CMov _), _, _) as bi ->
     failwith (fsprintf "eq_constrs: unexpected instruction %a\n" pp_base_instr bi)

   | App(_, ds, _) ->
     let dregs = List.filter_map ~f:(function Dreg(r) -> Some(r) | _ -> None) ds in
     List.iter ~f:(fun d -> ignore (new_class d)) dregs
  in
  List.iter regs ~f:(fun pr -> ignore (new_class pr));
  List.iter bis ~f:handle_bi;
  (eq_classes, fixed_classes, class_map)
  *)

(* ** Register allocation
 * ------------------------------------------------------------------------ *)

(* PRE: We assume the code is in SSA. *)
let register_allocate _nregs _efun0 =
  failwith "undefined"
  (*
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
    match Hashtbl.find fixed_pregs pr with
    | Some ri ->
      if Set.mem !free_regs ri then (
        Hashtbl.set reg_map ~key:pr ~data:ri;
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
            (Hashtbl.to_alist reg_map)
        in
        raise (E.PickExc err)
      )
    | None ->
      begin match Set.max_elt !free_regs with
      | None -> raise (E.PickExc "no registers left")
      | Some i ->
        Hashtbl.set reg_map ~key:pr ~data:i;
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
      match Hashtbl.find reg_map pr with
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
    Hashtbl.filteri_inplace reg_map ~f:remove_dead
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
            Hashtbl.set fixed_pregs ~key:d  ~data:r1;
            let d = trans_dest (Dreg d) in
            App(o,(linit ds)@[d],s1::s2::cfin)

          | App(Add,_,_) -> assert false

          | App(CMov(_) as o,[Dreg(d)],[Sreg(s1);s2;cfin]) ->
             let r1 = hashtbl_find_exn reg_map pp_preg_ty s1 in
             let s1 = trans_src (Sreg(s1)) in
             let s2 = trans_src s2        in
             free_dead_regs read_after_rhs;
             Hashtbl.set fixed_pregs ~key:d  ~data:r1;
             let d = trans_dest (Dreg d) in
             App(o,[d],[s1;s2;cfin])

          | App(CMov(_),_,_) -> assert false

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
    Hashtbl.iter fixed_classes
      ~f:(fun ~key:i ~data:reg ->
            let pregs = hashtbl_find_exn eq_classes pp_int i in
            (* F.printf "## using %s for %a\n" (X64.string_of_reg reg) (pp_list "," pp_preg)
                (Set.to_list pregs); *)
            Set.iter pregs ~f:(fun preg ->
              Hashtbl.set fixed_pregs ~key:preg  ~data:(X64.(int_of_reg reg)))
      );

    if efun0.ef_extern then (
      (* directly use the ABI argument registers for arguments *)
      let arg_len = List.length efun0.ef_args in
      let arg_regs = List.take (List.map ~f:X64.int_of_reg X64.arg_regs) arg_len in
      let arg_max = List.length X64.arg_regs in
      if List.length arg_regs < arg_len then
        failwith (fsprintf "register_alloc: at most %i arguments supported" arg_max);
      (* List.iter (List.zip_exn efun0.ef_args arg_regs)
        ~f:(fun (arg,arg_reg) -> Hashtbl.set fixed_pregs ~key:arg ~data:arg_reg);
      *)

      (* directly use the ABI return registers for return values *)
      let ret_extern_regs = List.map ~f:X64.int_of_reg X64.[RAX; RDX] in
      let ret_len = List.length efun0.ef_ret in
      let ret_regs = List.take ret_extern_regs ret_len in
      let ret_max = List.length ret_extern_regs in
      if List.length ret_regs < ret_len then
        failwith (fsprintf "register_alloc: at most %i arguments supported" ret_max);
      List.iter (List.zip_exn efun0.ef_ret ret_regs)
        ~f:(fun (ret,ret_reg) -> Hashtbl.set fixed_pregs ~key:ret ~data:ret_reg)
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
  efun
  *)

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

    | App(CMov(CfSet(b)),[d],[s1;s2;_cin]) ->
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
