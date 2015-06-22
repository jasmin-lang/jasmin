open Core.Std
open Util
open IL_Lang

module X64 = Asm_X64
module MP  = MParser

type asm_lang = X64

type transform =
  | MacroExpand of (string * Big_int.big_int) list
  | SSA
  | RegisterAlloc
  | Asm of asm_lang

(* ------------------------------------------------------------------------ *)
(* Interpreting index expressions and conditions *)

let cvars_cexpr ie =
  let rec go = function
    | Cvar(s) ->
      String.Set.singleton s
    | Cbinop(_,ce1,ce2) ->
      Set.union (go ce1) (go ce2)
    | Cconst _ -> String.Set.empty
  in
  go ie

let cvars_ccond cc =
  let rec go = function
    | Ctrue -> String.Set.empty
    | Cnot(ic) -> go ic
    | Cand (ic1,ic2) ->
      Set.union (go ic1) (go ic2)
    | Ccond(_,ce1,ce2) ->
      Set.union (cvars_cexpr ce1) (cvars_cexpr ce2)
  in
  go cc

let eval_cbinop co =
  let open Big_int_Infix in
  match co with
  | Cplus  -> (+!)
  | Cmult  -> ( *!)
  | Cminus -> (-!)


let eval_cexpr cvar_map ce =
  let rec go = function
    | Cvar(s) ->
      begin match Map.find cvar_map s with
      | Some x -> x
      | None ->
        failwith ("eval_cexpr: parameter "^s^" undefined")
      end
    | Cbinop(o,ie1,ie2) ->
      (eval_cbinop o) (go ie1) (go ie2)
    | Cconst(c) ->
      Big_int.big_int_of_int64 c
  in
  go ce

let eval_ccondop cco =
  let open Big_int_Infix in
  match cco with
  | Ceq      -> (===)
  | Cineq    -> fun x y -> not (x === y)
  | Cless    -> (<!)
  | Cgreater -> fun x y -> y <! x
  | Cleq     -> fun x y -> x <! y || x === y
  | Cgeq     -> fun x y -> y <! x || x === y

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

let inst_var cvar_map = function
  | Vreg(v,ies) ->
    Vreg(v,List.map ~f:(inst_cexpr cvar_map) ies)
  | Mreg(_) as r -> r

let inst_src cvar_map = function
  | Svar(v)       -> Svar(inst_var cvar_map v)
  | Smem(v,ie)    -> Smem(inst_var cvar_map v, inst_cexpr cvar_map ie)
  | Simm(_) as im -> im

let inst_dest cvar_map = function
  | Dvar(v)       -> Dvar(inst_var cvar_map v)
  | Dmem(v,ie)    -> Dmem(inst_var cvar_map v, inst_cexpr cvar_map ie)

let inst_base_instr cvar_map bi =
  let inst_d = inst_dest cvar_map in
  let inst_s = inst_src cvar_map in
  match bi with
  | Assgn(d,s) ->
    Assgn(inst_d d,inst_s s)
  | Mul(mdh,dl,s1,s2) ->
    Mul(Option.map ~f:inst_d mdh,inst_d dl,inst_s s1,inst_s s2)
  | BinOpCf(bop,cf_out,d1,s1,s2,cfin) ->
    BinOpCf(bop,cf_out,inst_d d1,inst_s s1,inst_s s2,cfin)
  | Comment(_) -> bi

(* ------------------------------------------------------------------------ *)
(* Macro expansion: loop unrolling, if, ...  *)

let macro_expand cvar_map st =
  let spaces indent =
    String.make indent ' '
  in
  let rec go indent ivm = function
    | [] -> []
    | instr::instrs ->
      begin match instr with
      | BInstr(binstr) ->
        (inst_base_instr ivm binstr)::(go indent ivm instrs)
      | If(ic,st1,st2) ->
        let cond = eval_ccond ivm ic in
        let st = if cond then st1 else st2 in
        let comment s =
          Comment (fsprintf "%s%s %s %a" (spaces indent) s (if cond then "if" else "else") pp_icond ic)
        in
        (comment "START: ")::(go (indent + 2) ivm st)@[comment "END: "]@(go indent ivm instrs)
      | For(iv,lb_ie,ub_ie,st) ->
        let lb = eval_cexpr ivm lb_ie in
        let ub = eval_cexpr ivm ub_ie in
        let open Big_int_Infix in
        assert (lb <! ub || lb === ub);
        let v = ref lb in
        let sts = ref [] in
        while (not (ub <! !v)) do
          let comment =
            Comment (fsprintf "%s%s = %s" (spaces (indent+2)) iv (Big_int.string_of_big_int !v))
          in
          sts := !sts @ [comment] @ go (indent + 2) (Map.add ivm ~key:iv ~data:(!v)) st;
          v := !v +! Big_int.unit_big_int
        done;
        let comment s =
          Comment (fsprintf "%s%s for %s in %a..%a" s (spaces indent) iv pp_cexpr lb_ie pp_cexpr ub_ie)
        in
        (comment "START:")::!sts@[(comment "END:")]@(go indent ivm instrs)
      end
  in
  go 0 cvar_map st

(* ------------------------------------------------------------------------ *)
(* Single assignment  *)

let transform_ssa bis =
  let var_index = Vreg.Table.create () in
  let get_index v = Option.value ~default:Int64.zero (Hashtbl.find var_index v) in
  let incr_index v =
    let i = Int64.succ (get_index v) in
    Hashtbl.set var_index ~key:v ~data:i;
    i
  in
  let update_src = function
    | (Simm(_) | Svar(Mreg(_)) | Smem(Mreg(_),_)) as s -> s
    | Svar(Vreg(v,ies)) -> Svar(Vreg(v, ies@[Cconst (get_index (v,ies))]))
    | Smem(Vreg(v,ies),ie) -> Smem(Vreg(v,ies@[Cconst (get_index (v,ies))]), ie)
  in
  let update_dest = function
    | (Dvar(Mreg(_)) | Dmem(Mreg(_),_)) as s -> s
    | Dvar(Vreg(v,ies)) -> Dvar(Vreg(v, ies@[Cconst (incr_index (v,ies))]))
    | Dmem(Vreg(v,ies),ie) -> (* write to address of variable, but not variable itself *)
      Dmem(Vreg(v,ies@[Cconst (get_index (v,ies))]), ie)
  in
  let rec go = function
    | [] -> []
    | bi::bis ->
      let bi =
        match bi with
        (* Note: sources must be updated before destinations *)
        | Comment(_) -> bi
        | Assgn(d,s) ->
          let s = update_src s in
          let d = update_dest d in
          Assgn(d,s)
        | Mul(mdh,dl,s1,s2) ->
          let s1  = update_src s1 in
          let s2  = update_src s2 in
          let mdh = Option.map ~f:update_dest mdh in
          let dl  = update_dest dl in
          Mul(mdh,dl,s1,s2)
        | BinOpCf(bo,cout,d,s1,s2,cin) ->
          let s1 = update_src s1 in
          let s2 = update_src s2 in
          let d  = update_dest d in
          BinOpCf(bo,cout,d,s1,s2,cin)
      in
      bi::(go bis)
  in
  go bis

(* ------------------------------------------------------------------------ *)
(* Register allocation *)

let register_allocate (usable_regs : rname list) bis =

  let free_regs = ref usable_regs in
  let reg_map = ref Vreg.Map.empty in
  let find_reg nv = Map.find_exn !reg_map nv in
  let get_free_reg nv =
    match !free_regs with
    | []      -> failwith "register_allocate: ran out of registers"
    | r::rest ->
      free_regs := rest;
      reg_map := Map.add !reg_map ~key:nv ~data: r;
      r
  in

  let reuse_reg ~old_nv ~new_nv =
    let r = find_reg old_nv in
    reg_map := Map.add (Map.remove !reg_map old_nv) ~key:new_nv ~data:r;
    r
  in

  let src_use_reg = function
    | (Svar(Mreg(_)) | Smem(Mreg(_),_) | Simm(_)) as d -> d
    | Svar(Vreg(nv))   -> Svar(Mreg(find_reg nv))
    | Smem(Vreg(nv),o) -> Smem(Mreg(find_reg nv),o)
  in

  let dest_alloc_reg = function
    | (Dvar(Mreg(_)) | Dmem(Mreg(_),_)) as d -> d
    | Dvar(Vreg(nv))   -> let r = get_free_reg nv in Dvar(Mreg(r))
      (* this is a write to memory, not to the register *)
    | Dmem(Vreg(nv),o) -> let r = find_reg nv in Dmem(Mreg(r),o)
  in

  let rec go = function
    | [] -> []
    | bi::bis ->
      F.printf "before: %a\n%!" pp_base_instr bi;
      let bi =
        match bi with
        (* Note: we update sources before destinations *)
        | Comment(_) -> bi

        | Assgn(d,s) ->
          let s = src_use_reg s in
          let d = dest_alloc_reg d in
          Assgn(d,s)

        | Mul(mdh,dl,s1,s2) ->
          let s1 = src_use_reg s1 in
          let s2 = src_use_reg s2 in
          let mdh = Option.map ~f:dest_alloc_reg mdh in
          let dl = dest_alloc_reg dl in
          Mul(mdh,dl,s1,s2)

        | BinOpCf(bo,cout,d,s1,s2,cin) ->
          let s2 = src_use_reg s2 in
          let (d,s1) =
            match d,s1 with

            | Dvar(Mreg(dr)), Svar(Mreg(sr)) ->
              assert (dr = sr);
              d,s1

            | Dvar(Vreg(dv)), Svar(Vreg(sv)) ->
              let r = reuse_reg ~old_nv:sv ~new_nv:dv in
              Dvar(Mreg(r)),Svar(Mreg(r))

            | Dmem(Mreg(dr),die), Smem(Mreg(sr),sie) ->
              assert (dr = sr && die = sie);
              d,s1

            | Dmem(Vreg(dv),die), Smem(Vreg(sv),sie) ->
              assert (die = sie);
              let r = reuse_reg ~old_nv:sv ~new_nv:dv in
              Dmem(Mreg(r),die),Smem(Mreg(r),sie)

            | _ -> assert false
          in
          BinOpCf(bo,cout,d,s1,s2,cin)
      in
      F.printf "after:  %a\n%!" pp_base_instr bi;
      bi::(go bis)   
  in
  F.printf "\nregister alloc:\n%!";
  go bis

(* ------------------------------------------------------------------------ *)
(* Translation to assembly  *)

let stmt_to_base_instrs st =
  List.map st
    ~f:(function BInstr(i) -> i | _ -> assert false)

let base_instrs_to_stmt bis =
  List.map ~f:(fun i -> BInstr(i)) bis

let to_asm_x64 st =
  let is_imm_src = function Simm _ -> true | _ -> false in
  let is_reg_dest = function Dvar(Mreg(_)) -> true | _ -> false in
  let trans_src = function
    | Svar(Mreg(r))    -> X64.Sreg(X64.reg_of_string r)
    | Simm(i)         -> X64.Simm(i)
    | Smem(Mreg(r),ie) ->
      begin match ie with
      | Cconst(i) -> X64.Smem(X64.reg_of_string r,i)
      | _ -> assert false
      end
    | _ -> failwith "not implemented yet"
  in
  let trans_dest = function
    | Dvar(Mreg(r)) -> X64.Dreg(X64.reg_of_string r)
    | Dmem(Mreg(r),ie) ->
      begin match ie with
      | Cconst(i) -> X64.Dmem(X64.reg_of_string r,i)
      | _ -> assert false
      end
    | _ -> failwith "not implemented yet"
  in
  let rec go = function
    | [] -> []
    | bi::bis ->
      let bi =
        let c = X64.Comment (fsprintf "mil: %a" pp_base_instr bi) in
        match bi with

        | Comment(s) ->
          [X64.Comment(s)]


        | Assgn(d,s) ->
          let instr = X64.( Binop(Mov,trans_src s,trans_dest d) ) in
          [c;instr]


        | Mul(Some dh,dl,s1,s2) ->
          if not (equal_dest dh (Dvar(Mreg "rdx"))) then
            failwith "to_asm_x64: mulq high result must be %rdx";
          if not (equal_dest dl (Dvar (Mreg "rax"))) then
            failwith "to_asm_x64: mulq low result must be %rax";
          if not (equal_src (dest_to_src dl) s1) then
            failwith "to_asm_x64: mulq low result must be equal to source 1";
          if is_imm_src s1 then
            failwith "to_asm_x64: mulq source 1 cannot be immediate";

          let instr = X64.( Unop(Mul,trans_src s2) ) in
          [c;instr]


        | Mul(None,dl,s1,s2) ->
          if is_imm_src s2 then
            failwith "to_asm_x64: imul source 1 cannot be immediate";
          if not (is_imm_src s2) then
            failwith "to_asm_x64: imul source 2 must be immediate";
          if not (is_reg_dest dl) then
            failwith "to_asm_x64: imul dest must be register";

          let instr = X64.( Triop(IMul,trans_src s1,trans_src s2,trans_dest dl) ) in
          [c;instr]


        | BinOpCf(op,_,d,s1,s2,cout) ->
          if not (equal_src (dest_to_src d) s1) then
            failwith "to_asm_x64: addition/subtraction with dest<>src1";

          let instr =
              match op,cout with
              | Add, IgnoreCarry ->
                X64.( Binop(Add,trans_src s2,trans_dest d) )
              | Add, UseCarry(_) ->
                X64.( Binop(Adc,trans_src s2,trans_dest d) )

              | BAnd, IgnoreCarry ->
                X64.( Binop(And,trans_src s2,trans_dest d) )
              | BAnd, UseCarry(_) -> assert false

              | Sub, IgnoreCarry ->
                X64.( Binop(Sub,trans_src s2,trans_dest d) )
              | Sub, UseCarry(_) ->
                X64.( Binop(Sbb,trans_src s2,trans_dest d) )
          in
          [c;instr]
      in
      bi@(go bis)
  in
  go (stmt_to_base_instrs st)

let wrap_asm_function is =
  let prefix =
    X64.([ Section "text";
           Global "_test";
           Label "_test";
           Unop(Push,Sreg RBP);
           Binop(Mov,Sreg RSP,Dreg RBP) ])
  in
  let suffix =
    X64.([ Unop(Pop,Sreg RBP);
           Ret ])
  in
  prefix @ is @ suffix

(* ------------------------------------------------------------------------ *)
(* Apply transformations in sequence.  *)

let ptrafo =
  let open MP in
  let mapping =
    many1 letter >>= fun s ->
    char '=' >>
    many1 digit >>= fun i ->
    return (String.of_char_list s,Big_int.big_int_of_string (String.of_char_list i))
  in
  let mappings =
    char '[' >> sep_by mapping (char ',') >>= fun l ->
    char ']' >>$ l
  in
  let asm_lang =
    choice [ string "x86-64" >>$ X64 ]
  in
  choice
    [ string "ssa" >>$ SSA
    ; string "register_alloc" >>$  RegisterAlloc
    ; string "asm" >> char '[' >> asm_lang >>= (fun l -> char ']' >>$ (Asm(l)))
    ; string "expand" >> mappings >>= fun m -> return (MacroExpand(m)) ]
      

let parse_trafo s =
  let open MP in
  match parse_string (sep_by ptrafo (char ',') >>= fun x -> eof >>$ x) s () with
  | Success t ->
    begin match List.rev t with
    | Asm(l)::rest ->
      if List.exists ~f:(function Asm(_) -> true | _ -> false) rest then (
        eprintf "asm[_] transformation must be last transformation";
        exit 1
      );
      (List.rev rest,Some l)
    | _ -> (t,None)
    end
  | Failed(s,_) ->
    eprintf "parsing transformation string failed: %s.\n%!" s;
    exit 1

let apply_transform trafo st =
  let app_trafo st t =
    match t with
    | MacroExpand(m) ->
         macro_expand (String.Map.of_alist_exn m) st
      |> base_instrs_to_stmt
    | SSA ->
         stmt_to_base_instrs st
      |> transform_ssa
      |> base_instrs_to_stmt
    | RegisterAlloc ->
         stmt_to_base_instrs st
      |> register_allocate ["r8"; "r9"; "r10"; "r11"; "r12"]
      |> base_instrs_to_stmt
    | Asm(_) -> assert false
  in
  List.fold_left trafo ~init:st ~f:app_trafo

let apply_transform_asm strafo st =
  let (trafo,mlang) = parse_trafo strafo in
  let st = apply_transform trafo st in
  match mlang with
  | None     -> `IL st
  | Some X64 -> `Asm_X64 (to_asm_x64 st |> wrap_asm_function)
