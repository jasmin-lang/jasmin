(* * Interpreter for IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Util
open Arith
open IL_Lang
open IL_Utils
open IL_Typing

(* ** Interpreting compile-time expressions and conditions
 * ------------------------------------------------------------------------ *)

let eval_cbinop = function
  | Cplus  -> U64.add
  | Cmult  -> U64.mul
  | Cminus -> U64.sub

let eval_cexpr cvar_map ce =
  let rec go = function
    | Cbinop(o,ie1,ie2) -> eval_cbinop o (go ie1) (go ie2)
    | Cconst(c)         -> c
    | Cvar(s) ->
      begin match Map.find cvar_map s with
      | Some x -> x
      | None   -> failwith ("eval_cexpr: parameter "^s^" undefined")
      end
  in
  go ce

let eval_ccondop = function
  | Ceq      -> U64.equal
  | Cineq    -> fun x y -> not (U64.equal x y)
  | Cless    -> fun x y -> U64.compare x y < 0
  | Cgreater -> fun x y -> U64.compare x y > 0
  | Cleq     -> fun x y -> U64.compare x y <= 0
  | Cgeq     -> fun x y -> U64.compare x y >= 0

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
  Cconst (eval_cexpr cvar_map ce)

let inst_preg cvar_map preg =
  { preg with pr_index = List.map ~f:(inst_cexpr cvar_map) preg.pr_index }

let inst_src cvar_map = function
  | Sreg(r)       -> Sreg(inst_preg cvar_map r)
  | Smem(r,ie)    -> Smem(inst_preg cvar_map r, inst_cexpr cvar_map ie)
  | Simm(_) as im -> im

let inst_dest cvar_map = function
  | Dreg(v)       -> Dreg(inst_preg cvar_map v)
  | Dmem(v,ie)    -> Dmem(inst_preg cvar_map v, inst_cexpr cvar_map ie)

let inst_base_instr cvar_map bi =
  let inst_d = inst_dest cvar_map in
  let inst_s = inst_src cvar_map in
  match bi with
  | App(o,ds,ss) -> App(o,List.map ~f:inst_d ds,List.map ~f:inst_s ss)
  | Comment(_)   -> bi

(* ** Interpreter
 * ------------------------------------------------------------------------ *)

let is_Simm = function Simm _ -> true | _ -> false
let is_Comment = function Comment _ -> true | _ -> false

type mstate =
  { mcvars : u64  String.Map.t
  ; mregs  : u64  Preg.Map.t
  ; mflags : bool Preg.Map.t
  ; mmem   : u64  U64.Map.t
  }

let print_mstate ms =
  F.printf "regs: %a\n" (pp_list ", " (pp_pair " -> " pp_preg pp_uint64))
    (Preg.Map.to_alist ms.mregs);
  F.printf "flags: %a\n" (pp_list ", " (pp_pair " -> " pp_preg pp_bool))
    (Preg.Map.to_alist ms.mflags);
  F.printf "mem: %a\n" (pp_list ", " (pp_pair " -> " pp_uint64 pp_uint64))
    (U64.Map.to_alist ms.mmem)

let get_addr addr_r offset =
  let c8 = U64.of_int 8 in
  (* we only allow aligned reads/writes *)
  assert (U64.is_zero (U64.rem offset c8));
  U64.add addr_r offset

let rec read_src ms s =
  match s with
  | Simm i -> i
  | Sreg r ->
    begin match Map.find ms.mregs r with
    | Some x -> x
    | None   -> 
      failwith (fsprintf "cannot read register %a:%a" pp_preg r pp_ty r.pr_aux)
    end
  | Smem(r,Cconst i) ->
    let addr_r = read_src ms (Sreg r) in
    let addr = get_addr addr_r i in
    begin match Map.find ms.mmem addr with
    | Some x ->
      (* F.printf "read_mem: %a -> %a\n" pp_uint64 addr pp_uint64 x; *)
      x
    | None   -> 
      failwith (fsprintf "cannot read address %a" pp_uint64 addr)
    end
  | _ -> assert false

let write_dest ms d x =
  match d with
  | Dreg r ->
    (* F.printf "write_reg: %a -> %a\n" pp_preg r pp_uint64 x; *)
    { ms with mregs = Map.add ms.mregs ~key:r ~data:x }
  | Dmem(r,Cconst i) ->
    let addr_r = read_src ms (Sreg r) in
    let addr = get_addr addr_r i in
    (* F.printf "write_mem: %a -> %a\n" pp_uint64 addr pp_uint64 x; *)
    { ms with mmem = Map.add ms.mmem ~key:addr ~data:x }
  | _ -> assert false

let read_flag ms s =
  match s with
  | Sreg r ->
    Map.find_exn ms.mflags r
  | Simm _ ->
    failwith "cannot give immediate, flag (in register) expected" 
  | Smem(_,_) ->
    failwith "cannot give memory, flag (in register) expected"

let write_flag ms d b =
  match d with
  | Dreg r ->
    { ms with mflags = Map.add ms.mflags ~key:r ~data:b }
  | Dmem(_,_) ->
    failwith "cannot give memory, flag (in register) expected"

let interp_base_instr (ms : mstate) binstr =
  let go = function

    | A_Assgn(d,s) ->
      let x = read_src ms s in
      write_dest ms d x

    | A_UMul((h,l),(x,y)) ->
      let x = read_src ms x in
      let y = read_src ms y in
      let (zh,zl) = U64.umul x y in
      let ms = write_dest ms l zl in
      write_dest ms h zh

    | A_Carry(cop,(mcf_out,z),(x,y,mcf_in)) ->
      let cf =
        Option.value_map mcf_in ~default:false ~f:(fun cf -> read_flag ms cf)
      in
      let x = read_src ms x in
      let y = read_src ms y in
      let (zo,cfo) =
        match cop with
        | O_Add -> U64.add_carry x y cf
        | O_Sub -> U64.sub_carry x y cf
      in
      let ms = write_dest ms z zo in
      begin match mcf_out with
      | Some cf_out -> write_flag ms cf_out cfo
      | None        -> ms
      end

    | A_CMov(CfSet cf_is_set,d,(s1,s2,cf_in))  ->
      let s1 = read_src ms s1 in
      let s2 = read_src ms s2 in
      let cf = read_flag ms cf_in in
      let res = if cf = cf_is_set then s2 else s1 in
      write_dest ms d res

    | A_IMul(z,(x,y)) ->
      assert (is_Simm y);
      let x = read_src ms x in
      let y = read_src ms y in
      write_dest ms z (fst (U64.imul_trunc x y))
    
    | A_Logic(_lop,_d,(_s1,_s2)) ->
      failwith "not implemented"

    | A_Shift(_dir,(_mcf_out,_z),(_x,_cn)) ->
      failwith "not implemented"

  in
  if not (is_Comment binstr) then (
    (* F.printf "####################################\n"; 
    F.printf "executing: %a\n" pp_base_instr binstr; *)
    let aview =
      match binstr with
      | App(o,d,s) -> app_view (o,d,s)
      | Comment _ -> assert false
    in
    let ms = go aview in
    (* print_mstate ms; *)
    ms
  ) else (
    ms
  )

let rec interp_instr ms0 instr =
  match instr with
  | BInstr(bi) ->
    let bi = inst_base_instr ms0.mcvars bi in
    interp_base_instr ms0 bi
  | If(ccond,stmt1,stmt2) ->
    if eval_ccond ms0.mcvars ccond then
      interp_stmt ms0 stmt1
    else
      interp_stmt ms0 stmt2
  | For(cv,clb,cub,stmt) ->
    let lb = eval_cexpr ms0.mcvars clb in
    let ub = eval_cexpr ms0.mcvars cub in
    let old_val = Map.find ms0.mcvars cv in
    let i  = ref lb in
    let ms = ref ms0 in
    while U64.compare !i ub <= 0 do
       ms := { !ms with mcvars = Map.add !ms.mcvars ~key:cv ~data:!i };
       ms := interp_stmt !ms stmt;
       i := U64.succ !i
    done;
    { !ms with
      mcvars = Map.change !ms.mcvars cv (fun _ -> old_val) }

and interp_stmt (ms0 : mstate) stmt =
  List.fold stmt
    ~f:(fun ms i -> interp_instr ms i)
    ~init:ms0

let interp_string mem cvar_map args string =
  let open ParserUtil in
  let efun_ut = List.hd_exn (parse ~parse:IL_Parse.efuns "" string) in
  let efun = type_efun efun_ut (String.Table.create ()) in
  let stmt = efun.ef_body in

  let arg_regs = efun.ef_args in
  let regs =
    Preg.Map.of_alist_exn
      (List.zip_exn arg_regs args)
  in
  let flags = Preg.Map.of_alist_exn [] in
  let ms = {mregs = regs; mcvars = cvar_map; mflags = flags; mmem = mem; } in
 
  (* print_mstate ms; *)
  interp_stmt ms stmt
