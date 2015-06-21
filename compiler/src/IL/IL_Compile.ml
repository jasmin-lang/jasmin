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

let ivars_iexpr ie =
  let rec go = function
    | IVar(s) ->
      String.Set.singleton s
    | IBinOp(_,ie1,ie2) ->
      Set.union (go ie1) (go ie2)
    | IConst _ -> String.Set.empty
  in
  go ie

let ivars_icond ic =
  let rec go = function
    | ITrue -> String.Set.empty
    | INot(ic) -> go ic
    | IAnd (ic1,ic2) ->
      Set.union (go ic1) (go ic2)
    | ICond(_,ie1,ie2) ->
      Set.union (ivars_iexpr ie1) (ivars_iexpr ie2)
  in
  go ic

let eval_ibinop io =
  let open Big_int_Infix in
  match io with
  | IPlus  -> (+!)
  | IMult  -> ( *!)
  | IMinus -> (-!)


let eval_iexpr ivar_map ie =
  let rec go = function
    | IVar(s) ->
      Option.value_exn (Map.find ivar_map s)
    | IBinOp(o,ie1,ie2) ->
      (eval_ibinop o) (go ie1) (go ie2)
    | IConst(c) ->
      U64.to_big_int c
  in
  go ie

let eval_icondop ico =
  let open Big_int_Infix in
  match ico with
  | CEq      -> (===)
  | CInEq    -> fun x y -> not (x === y)
  | CLess    -> (<!)
  | CGreater -> fun x y -> y <! x
  | CLeq     -> fun x y -> x <! y || x === y
  | CGeq     -> fun x y -> y <! x || x === y

let eval_icond ivar_map ic =
  let rec go = function
    | ITrue              -> true
    | INot(ic)           -> not (go ic)
    | IAnd(ic1,ic2)      -> (go ic1) && (go ic2)
    | ICond(ico,ie1,ie2) ->
      eval_icondop ico (eval_iexpr ivar_map ie1) (eval_iexpr ivar_map ie2)
  in
  go ic

let inst_iexpr ivar_map ie =
  IConst (U64.of_big_int (eval_iexpr ivar_map ie))

let inst_var ivar_map = function
  | Nvar(v,ies) ->
    Nvar(v,List.map ~f:(inst_iexpr ivar_map) ies)
  | Reg(_) as r -> r

let inst_src ivar_map = function
  | Svar(v)       -> Svar(inst_var ivar_map v)
  | Smem(v,ie)    -> Smem(inst_var ivar_map v, inst_iexpr ivar_map ie)
  | Simm(_) as im -> im

let inst_dest ivar_map = function
  | Dvar(v)       -> Dvar(inst_var ivar_map v)
  | Dmem(v,ie)    -> Dmem(inst_var ivar_map v, inst_iexpr ivar_map ie)

let inst_base_instr ivar_map bi =
  let inst_d = inst_dest ivar_map in
  let inst_s = inst_src ivar_map in
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

let macro_expand ivar_map st =
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
        let cond = eval_icond ivm ic in
        let st = if cond then st1 else st2 in
        let comment s =
          Comment (fsprintf "%s%s %s %a" (spaces indent) s (if cond then "if" else "else") pp_icond ic)
        in
        (comment "START: ")::(go (indent + 2) ivm st)@[comment "END: "]@(go indent ivm instrs)
      | For(iv,lb_ie,ub_ie,st) ->
        let lb = eval_iexpr ivm lb_ie in
        let ub = eval_iexpr ivm ub_ie in
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
          Comment (fsprintf "%s%s for %s in %a..%a" s (spaces indent) iv pp_iexpr lb_ie pp_iexpr ub_ie)
        in
        (comment "START:")::!sts@[(comment "END:")]@(go indent ivm instrs)
      end
  in
  go 0 ivar_map st

(* ------------------------------------------------------------------------ *)
(* Single assignment  *)

let transform_ssa bis =
  let var_index = Nvar.Table.create () in
  let get_index v = Option.value ~default:U64.zero (Hashtbl.find var_index v) in
  let incr_index v =
    let i = U64.succ (get_index v) in
    Hashtbl.set var_index ~key:v ~data:i;
    i
  in
  let update_src = function
    | (Simm(_) | Svar(Reg(_)) | Smem(Reg(_),_)) as s -> s
    | Svar(Nvar(v,ies)) -> Svar(Nvar(v, ies@[IConst (get_index (v,ies))]))
    | Smem(Nvar(v,ies),ie) -> Smem(Nvar(v,ies@[IConst (get_index (v,ies))]), ie)
  in
  let update_dest = function
    | (Dvar(Reg(_)) | Dmem(Reg(_),_)) as s -> s
    | Dvar(Nvar(v,ies)) -> Dvar(Nvar(v, ies@[IConst (incr_index (v,ies))]))
    | Dmem(Nvar(v,ies),ie) -> (* write to address of variable, but not variable itself *)
      Dmem(Nvar(v,ies@[IConst (get_index (v,ies))]), ie)
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

let register_allocate (_usable_regs : String.Set.t) bis =

  (* the lifetime of a named variable v is (i,j) if
     v is written in position i and last read in position j
     (note: we assume SSA => v only written once *)
  let _nvar_lifetimes =
    Nvar.Map.empty
  in

  (* list of positions that write a fixed register *)
  let _register_writes =
    String.Map.empty
  in    

  (* positions that read a fixed register *)
  let _register_reads =
    String.Map.empty
  in

  let go _nvar_map bis =
    bis
  in
  go Nvar.Map.empty bis

(* ------------------------------------------------------------------------ *)
(* Translation to assembly  *)

let stmt_to_base_instrs st =
  List.map st
    ~f:(function BInstr(i) -> i | _ -> assert false)

let base_instrs_to_stmt bis =
  List.map ~f:(fun i -> BInstr(i)) bis

let to_asm_x64 st =
  let is_imm_src = function Simm _ -> true | _ -> false in
  let is_reg_dest = function Dvar(Reg(_)) -> true | _ -> false in
  let trans_src = function
    | Svar(Reg(r))  -> X64.Sreg(X64.reg_of_string r)
    | Simm(i)  -> X64.Simm(i)
    | _ -> failwith "not implemented yet"
  in
  let trans_dest = function
    | Dvar(Reg(r)) -> X64.Dreg(X64.reg_of_string r)
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
          if not (equal_dest dh (Dvar(Reg "rdx"))) then
            failwith "to_asm_x64: mulq high result must be %rdx";
          if not (equal_dest dl (Dvar (Reg "rax"))) then
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
      |> register_allocate (String.Set.of_list ["r8"; "r9"; "r10"; "r11"; "r12"])
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
