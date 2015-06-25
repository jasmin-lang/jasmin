open Core.Std
open Util
open IL_Lang

module X64 = Asm_X64
module MP  = MParser

(* ------------------------------------------------------------------------ *)
(* Interpreting compile-time expressions and conditions *)

let eval_cbinop = function
  | Cplus  -> Big_int_Infix.(+!)
  | Cmult  -> Big_int_Infix.( *!)
  | Cminus -> Big_int_Infix.(-!)


let eval_cexpr cvar_map ce =
  let rec go = function
    | Cbinop(o,ie1,ie2) -> eval_cbinop o (go ie1) (go ie2)
    | Cconst(c)         -> Big_int.big_int_of_int64 c
    | Cvar(s) ->
      begin match Map.find cvar_map s with
      | Some x -> x
      | None   -> failwith ("eval_cexpr: parameter "^s^" undefined")
      end
  in
  go ce

let eval_ccondop = Big_int_Infix.(function
  | Ceq      -> (===)
  | Cineq    -> fun x y -> not (x === y)
  | Cless    -> (<!)
  | Cgreater -> fun x y -> y <! x
  | Cleq     -> fun x y -> x <! y || x === y
  | Cgeq     -> fun x y -> y <! x || x === y
)

let eval_ccond cvar_map cc =
  let rec go = function
    | Ctrue              -> true
    | Cnot(ic)           -> not (go ic)
    | Cand(cc1,cc2)      -> (go cc1) && (go cc2)
    | Ccond(cco,ce1,ce2) ->
      eval_ccondop cco (eval_cexpr cvar_map ce1) (eval_cexpr cvar_map ce2)
  in
  go cc

let inst_cexpr cvar_map ce =
  Cconst (Big_int.int64_of_big_int (eval_cexpr cvar_map ce))

let inst_reg cvar_map (r,ies) =
  (r,List.map ~f:(inst_cexpr cvar_map) ies)

let inst_src cvar_map = function
  | Sreg(r)       -> Sreg(inst_reg cvar_map r)
  | Smem(r,ie)    -> Smem(inst_reg cvar_map r, inst_cexpr cvar_map ie)
  | Simm(_) as im -> im

let inst_dest cvar_map = function
  | Dreg(v)       -> Dreg(inst_reg cvar_map v)
  | Dmem(v,ie)    -> Dmem(inst_reg cvar_map v, inst_cexpr cvar_map ie)

let inst_base_instr cvar_map bi =
  let inst_d = inst_dest cvar_map in
  let inst_s = inst_src cvar_map in
  match bi with
  | App(o,ds,ss) -> App(o,List.map ~f:inst_d ds,List.map ~f:inst_s ss)
  | Comment(_)   -> bi

(* ------------------------------------------------------------------------ *)
(* Macro expansion: loop unrolling, if, ...  *)

let macro_expand cvar_map st =
  let spaces indent = String.make indent ' ' in
  let s_of_cond c = if c then "if" else "else" in
  let s_of_bi = Big_int.string_of_big_int in
  let comment_if s indent cond ic =
    fsprintf "%s%s %s %a" (spaces indent) s (s_of_cond cond) pp_icond ic
  in
  let comment_while s indent iv lb_ie ub_ie =
    fsprintf "%s%s for %s in %a..%a" s (spaces indent) iv pp_cexpr lb_ie pp_cexpr ub_ie
  in

  let rec expand indent ivm = function
    | BInstr(binstr) -> [inst_base_instr ivm binstr]

    | If(ic,st1,st2) ->
      let cond = eval_ccond ivm ic in
      let st = if cond then st1 else st2 in
      (Comment (comment_if "START: " indent cond ic))
      :: (List.concat_map ~f:(expand (indent + 2) ivm) st)
      @ [Comment (comment_if "END: " indent cond ic)]

    | For(iv,lb_ie,ub_ie,st) ->
      let open Big_int_Infix in
      let lb  = eval_cexpr ivm lb_ie in
      let ub  = eval_cexpr ivm ub_ie in
      let v   = ref lb in
      let bis = ref [] in
      assert (lb <! ub || lb === ub);
      while (not (ub <! !v)) do
        let body =
          List.concat_map ~f:(expand (indent + 2) (Map.add ivm ~key:iv ~data:!v)) st;
        in
        bis := !bis
               @ [Comment (fsprintf "%s%s = %s" (spaces (indent+2)) iv (s_of_bi !v))]
               @ body;
        v := !v +! Big_int.unit_big_int
      done;
      (Comment (comment_while "START:" indent iv lb_ie ub_ie))
      :: !bis
      @  [(Comment (comment_while "END:" indent iv lb_ie ub_ie))]
  in
  List.concat_map ~f:(expand 0 cvar_map) st

(* ------------------------------------------------------------------------ *)
(* Single assignment  *)

let transform_ssa efun =
  let bis = stmt_to_base_instrs efun.ef_body in
  let counter = ref (Int64.of_int (-1)) in
  let var_map = Preg.Table.create () in
  let get_index pr =
    ("r", [Cconst (Hashtbl.find_exn var_map pr)])
    
  in
  let new_index pr =
    counter := Int64.succ !counter;    
    Hashtbl.set var_map ~key:pr ~data:!counter;
    ("r", [Cconst !counter])
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
      let ss = List.map ~f:update_src ss in
      let ds = List.map ~f:update_dest ds in
      App(o,ds,ss)
  in
  (* perform in the right order *)
  let args = List.map ~f:(fun pr -> new_index pr) efun.ef_args in
  let bis = List.map ~f:rename bis in
  let rets = List.map ~f:(fun pr -> get_index pr) efun.ef_ret in
  { efun with ef_args = args; ef_body = base_instrs_to_stmt bis; ef_ret = rets; }

(* ------------------------------------------------------------------------ *)
(* Validate transformation (assuming that transform_ssa correct) *)

let validate_transform efun0 efun = 
  if not (equal_efun (transform_ssa efun0) (transform_ssa efun)) then (
    (* shrink counter-example *)
    for i = 1 to List.length efun0.ef_body do
      let efun0 = shorten_efun i efun0 in
      let efun  = shorten_efun i efun in
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

(* ------------------------------------------------------------------------ *)
(* Register liveness *)

type live_info = {
  li_bi : base_instr;
  li_read_after_rhs : Preg.Set.t; (* the set of register that might be read after
                                     the RHS of bi has been evaluated *)
}

(* returns a list of tuples (bi, V) denoting that the instructions
   bi;... depend on the registers V *)
let register_liveness efun =
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
      | _ ->
        go read lis ({ li_bi = li; li_read_after_rhs = read }::ris)
      end
  in
  go (Preg.Set.of_list efun.ef_ret) (List.rev bis) []

(* ------------------------------------------------------------------------ *)
(* Register allocation *)

(* FIXME: State preconditions precisely. *)
let register_allocate nregs efun0 =

  (* List of free registers in decreasing order, this simplifies "saving up" %rax (0)
     and %rdx (0) until they are really required. *)
  let free_regs = ref (Int.Set.of_list (List.init nregs ~f:(fun i -> i))) in
  let free_regs_add i =
    assert (not (Set.mem !free_regs i));
    free_regs := Set.add !free_regs i
  in
  let free_regs_remove i =
    assert (Set.mem !free_regs i);
    free_regs := Set.remove !free_regs i
  in
  
  (* mapping from pseudo registers to integers 0 .. nreg -1 denoting machine registers *)
  let reg_map = Preg.Table.create () in
  let int_to_preg i = fsprintf "%%%i" i,[] in
  let get_reg pr = int_to_preg (Hashtbl.find_exn reg_map pr) in

  (* track pseudo-registers that required a fixed register *)
  let fixed_pregs = Preg.Table.create () in
  let () =

    (* register %rax and %rdx for mul *)
    List.iter (stmt_to_base_instrs efun0.ef_body)
      ~f:(function
           | App(UMul,[Dreg(h);Dreg(l)],[Sreg(s1);Sreg(_)]) ->
             Hashtbl.set fixed_pregs ~key:l  ~data:(X64.(int_of_reg RAX));
             Hashtbl.set fixed_pregs ~key:s1 ~data:(X64.(int_of_reg RAX));
             Hashtbl.set fixed_pregs ~key:h  ~data:(X64.(int_of_reg RDX))
           | _ -> ()
      );

    (* directly use the ABI argument registers for arguments *)
    let arg_len = List.length efun0.ef_args in
    let arg_regs = List.take (List.map ~f:X64.int_of_reg X64.arg_regs) arg_len in
    if List.length arg_regs < arg_len then
      failwith (Printf.sprintf "register_alloc: at most %i arguments supported" (List.length arg_regs));
    List.iter (List.zip_exn efun0.ef_args arg_regs)
      ~f:(fun (arg,arg_reg) -> Hashtbl.set fixed_pregs ~key:arg ~data:arg_reg);

    (* directly use the ABI return registers for return values *)
    let ret_len = List.length efun0.ef_ret in
    let ret_regs = List.take (List.map ~f:X64.int_of_reg X64.[RAX; RDX]) ret_len in
    if List.length ret_regs < ret_len then
      failwith (Printf.sprintf "register_alloc: at most %i arguments supported" (List.length ret_regs));
    List.iter (List.zip_exn efun0.ef_ret ret_regs)
      ~f:(fun (ret,ret_reg) -> Hashtbl.set fixed_pregs ~key:ret ~data:ret_reg)
  in

  let pick_free pr =
    match Hashtbl.find fixed_pregs pr with
    | Some ri ->
      if Set.mem !free_regs ri then (
        Hashtbl.set reg_map ~key:pr ~data:ri;
        free_regs_remove ri;
        ri
      ) else (
        failwith
          (fsprintf "required register %s already in use: %a"
             (X64.string_of_reg (X64.reg_of_int ri))
             (pp_list "," pp_int) (Set.to_list !free_regs))
      )
    | None ->
      begin match Set.max_elt !free_regs with
      | None -> failwith "no registers left"
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
      | None    -> int_to_preg (pick_free pr)
      | Some i  -> int_to_preg i
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
  
  let alloc {li_bi = bi; li_read_after_rhs = read_after_rhs} =
    (* F.printf "reg_alloc: %a\n" pp_base_instr bi; *)
    let bi =
      match bi with
      | Comment(_) -> bi
        
      (* enforce dst = src1 and do not allocate registers for carry flag *)
      | App(Add,(([_;Dreg(d)] | [Dreg(d)]) as ds),(Sreg(s1)::s2::cfin)) ->
        let r1 = Hashtbl.find_exn reg_map s1 in
        let s1 = trans_src (Sreg s1) in
        let s2 = trans_src s2        in
        free_dead_regs read_after_rhs;
        Hashtbl.set fixed_pregs ~key:d  ~data:r1;
        let d = trans_dest (Dreg d) in
        App(Add,(linit ds)@[d],s1::s2::cfin)

      | App(Add,_,_) -> assert false
      
      | App(Sub,(([_;Dreg(d)] | [Dreg(d)]) as ds),(Sreg(s1)::s2::cfin)) ->
        let r1 = Hashtbl.find_exn reg_map s1 in
        let s1 = trans_src (Sreg s1) in
        let s2 = trans_src s2        in
        free_dead_regs read_after_rhs;
        Hashtbl.set fixed_pregs ~key:d  ~data:r1;
        let d = trans_dest (Dreg d) in
        App(Sub,(linit ds)@[d],s1::s2::cfin)

      | App(Sub,_,_) -> assert false
  
      | App(Cmov(_) as o,[Dreg(d)],[Sreg(s1);s2;cfin]) ->
        let r1 = Hashtbl.find_exn reg_map s1 in
        let s1 = trans_src (Sreg(s1)) in
        let s2 = trans_src s2        in
        free_dead_regs read_after_rhs;
        Hashtbl.set fixed_pregs ~key:d  ~data:r1;
        let d = trans_dest (Dreg d) in
        App(o,[d],[s1;s2;cfin])

      | App(Cmov(_),_,_) -> assert false

      | App(o,ds,ss) ->
        let ss = List.map ~f:trans_src ss in
        free_dead_regs read_after_rhs;
        let ds = List.map ~f:trans_dest ds in
        App(o,ds,ss)
    in
    (* F.printf "reg_alloc_done: %a\n" pp_base_instr bi; *)
    bi
  in

  let args = List.map efun0.ef_args ~f:(fun pr -> int_to_preg (pick_free pr)) in
  let bis = List.map ~f:alloc (register_liveness efun0) in
  let efun =
    { efun0 with
      ef_args = args;
      ef_body = base_instrs_to_stmt bis;
      ef_ret  = List.map ~f:(fun pr -> get_reg pr) efun0.ef_ret;
    }
  in
  validate_transform efun0 efun;
  efun

(* ------------------------------------------------------------------------ *)
(* Translation to assembly  *)

let to_asm_x64 efun =
  let mreg_of_preg pr =
    let fail () = failwith "asm_x64: expected register of the form %i" in
    let s = match pr with (s,[]) -> s | _ -> fail () in
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
  let ensure c msg = if not c then failwith msg in
  let trans_cexpr = function
    | Cconst(i) -> i
    | Cvar(_)
    | Cbinop(_) -> failwith "to_asm_x64: cannot translate non-constant c-expressions"
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
      ensure_dest_mreg dh X64.RDX "to_asm_x64: mulq high result must be %rdx";
      ensure_dest_mreg dl X64.RAX "to_asm_x64: mulq low result must be %rax";
      ensure_src_mreg  s1 X64.RAX "to_asm_x64: mulq source 1 must be %rax";

      let instr = X64.( Unop(Mul,trans_src s2) ) in
      [c;instr]

    | App(IMul,[dl],[s1;s2]) ->
      ensure (not (is_src_imm s1))  "to_asm_x64: imul source 1 cannot be immediate";
      ensure (is_src_imm s2)  "to_asm_x64: imul source 2 must be immediate";
      ensure (is_dest_reg dl) "to_asm_x64: imul dest must be register";
      [c; X64.( Triop(IMul,trans_src s2,trans_src s1,trans_dest dl) )]

    | App(Cmov(CfSet(b)),[d],[s1;s2;_cin]) ->
      ensure (equal_src (dest_to_src d) s1) "to_asm_x64: cmov with dest<>src1";
      let instr = X64.( Binop(Cmov(CfSet(b)),trans_src s2,trans_dest d) ) in
      [c; instr]



    | App(Shr,[d],[s1;s2]) ->
      ensure (equal_src (dest_to_src d) s1) "to_asm_x64:shr with dest<>src1";
      ensure (is_src_imm s2)  "to_asm_x64: shr source 2 must be immediate";
      let instr = X64.( Binop(Shr,trans_src s2,trans_dest d) )  in 
      [c;instr]

    | App(Shl,[d],[s1;s2]) ->
      ensure (equal_src (dest_to_src d) s1) "to_asm_x64: shl with dest<>src1";
      ensure (is_src_imm s2)  "to_asm_x64: shr source 2 must be immediate";
      let instr = X64.( Binop(Shl,trans_src s2,trans_dest d) )  in 
      [c;instr]

    | App(Xor,[d],[s1;s2]) ->
      ensure (equal_src (dest_to_src d) s1) "to_asm_x64: add/sub with dest<>src1";
      let instr = X64.( Binop(Xor,trans_src s2,trans_dest d) )  in 
      [c;instr]

    | App(op,([_;d] | [d]),s1::s2::cin) ->
      ensure (equal_src (dest_to_src d) s1) "to_asm_x64: add/sub with dest<>src1";

      let instr =
        match op,cin with
        | Add, []   -> X64.( Binop(Add,trans_src s2,trans_dest d) )
        | Add, [_]  -> X64.( Binop(Adc,trans_src s2,trans_dest d) )
        | BAnd, []  -> X64.( Binop(And,trans_src s2,trans_dest d) )
        | BAnd, [_] -> assert false
        | Sub, []   -> X64.( Binop(Sub,trans_src s2,trans_dest d) )
        | Sub, [_]  -> X64.( Binop(Sbb,trans_src s2,trans_dest d) )
        | _         -> assert false
      in
      [c; instr]

    | _ -> assert false
  in
  let asm_code = List.concat_map ~f:trans (stmt_to_base_instrs efun.ef_body) in
  X64.(
    { af_name = efun.ef_name;
      af_body = asm_code;
      af_args = List.map ~f:mreg_of_preg efun.ef_args;
      af_ret = List.map ~f:mreg_of_preg efun.ef_ret;
    }
  )

(* ------------------------------------------------------------------------ *)
(* Calling convention for "extern" functions  *)

let wrap_asm_function afun =
  let name = "_"^afun.X64.af_name in
  let prefix =
    X64.([ Section "text";
           Global name;
           Label name;
           Unop(Push,Sreg RBP);
           Binop(Mov,Sreg RSP,Dreg RBP) ])
  in
  let suffix =
    X64.([ Unop(Pop,Sreg RBP);
           Ret ])
  in
  prefix @ afun.X64.af_body @ suffix
