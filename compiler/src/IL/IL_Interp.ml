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
  let inst_indexes = function
      | Index(ies) -> Index (List.map ~f:(inst_cexpr cvar_map) ies)
      | Range _ -> assert false
  in
  { preg with pr_index = inst_indexes preg.pr_index }

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

let expand_range cvar_map pr =
  match pr.pr_index with
  | Range(lb,ub) ->
    let lb = eval_cexpr cvar_map lb |> U64.to_big_int in
    let ub = eval_cexpr cvar_map ub |> U64.to_big_int in
    List.map
      ~f:(fun i ->
          mk_preg_index_u64 pr.pr_name (U64.of_big_int i) U64)
      (list_from_to ~first:lb ~last:ub)
  | _ -> [pr]

let expand_arg cvar_map pr =
  assert (not (pr_is_indexed pr));
  match pr.pr_aux with
  | Ivals([ce]) ->
    let n = eval_cexpr cvar_map ce in
    let lb = Big_int.zero_big_int in
    let ub = U64.to_big_int n in
    List.map
      ~f:(fun i ->
          mk_preg_index_u64 pr.pr_name (U64.of_big_int i) U64)
      (list_from_to ~first:lb ~last:ub)
  | Ivals(_) -> assert false (* multiple dimensions not implemented yet *)
  | Bool | U64 | Array _ -> [pr]

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

let interp_base_instr (ms : mstate) = function

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

let rec interp_instr ms0 efun_map instr =
  match instr with

  | BInstr(bi) ->
    let bi = inst_base_instr ms0.mcvars bi in
    begin match bi with
    | Comment _ -> ms0
    | App(o,d,s) ->
      interp_base_instr ms0 (app_view (o,d,s))
    end

  | If(ccond,stmt1,stmt2) ->
    if eval_ccond ms0.mcvars ccond then
      interp_stmt ms0 efun_map stmt1
    else
      interp_stmt ms0 efun_map stmt2

  | For(cv,clb,cub,stmt) ->
    let lb = eval_cexpr ms0.mcvars clb in
    let ub = eval_cexpr ms0.mcvars cub in
    let old_val = Map.find ms0.mcvars cv in
    let i  = ref lb in
    let ms = ref ms0 in
    while U64.compare !i ub <= 0 do
       ms := { !ms with mcvars = Map.add !ms.mcvars ~key:cv ~data:!i };
       ms := interp_stmt !ms efun_map stmt;
       i := U64.succ !i
    done;
    { !ms with
      mcvars = Map.change !ms.mcvars cv (fun _ -> old_val) }

  | Call(fname,ret,args) ->
    let mregs_o   = ms0.mregs in
    let mflags_o  = ms0.mflags in
    let efun      = map_find_exn efun_map pp_string fname in
    let expand_src = function
      | Sreg(pr) -> List.map ~f:(fun pr -> Sreg(pr)) (expand_range ms0.mcvars pr)
      | _        -> assert false
    in
    let expand_dest = function
      | Dreg(pr) -> List.map ~f:(fun pr -> Dreg(pr)) (expand_range ms0.mcvars pr)
      | _        -> assert false
    in
    let efun_ret = List.concat_map efun.ef_ret ~f:(expand_range ms0.mcvars) in
    let given_ret = List.concat_map ret ~f:(expand_dest) in
    let given_args = List.concat_map args ~f:expand_src in
    let efun_args  = List.concat_map efun.ef_args ~f:(expand_arg ms0.mcvars) in
    let arg_alist =
      List.map2_exn given_args efun_args
        ~f:(fun given_arg efun_arg ->
              match given_arg with
              | Sreg(given_preg) ->
                (efun_arg, map_find_exn mregs_o pp_preg_ty given_preg)
              | _ -> assert false)  
    in
    let ms = {
      ms0 with
      mflags = Preg.Map.empty;
      mregs  = Preg.Map.of_alist_exn arg_alist;
    }
    in
    let ms = interp_stmt ms efun_map efun.ef_body in
    { ms with
      mflags = mflags_o;
      mregs  = List.fold2_exn given_ret efun_ret
                 ~f:(fun acc given_dest efun_preg ->
                       match given_dest with
                       | Dreg(pr) -> 
                         Map.add acc ~key:pr ~data:(Map.find_exn ms.mregs efun_preg)
                       | _ -> assert false)
                 ~init:mregs_o
    }

and interp_stmt (ms0 : mstate) efun_map stmt =
  List.fold stmt
    ~f:(fun ms i -> interp_instr ms efun_map i)
    ~init:ms0

let interp_string mem cvar_map args ef_name string =
  let open ParserUtil in
  let efuns_ut = parse ~parse:IL_Parse.efuns "" string in
  let efuns = type_efuns efuns_ut in
  let efun_map = String.Map.of_alist_exn (List.map ~f:(fun ef -> (ef.ef_name,ef)) efuns) in
  let efun = Map.find_exn efun_map ef_name in
  let stmt = efun.ef_body in

  let arg_regs = efun.ef_args in
  let regs =
    Preg.Map.of_alist_exn
      (List.zip_exn arg_regs args)
  in
  let flags = Preg.Map.of_alist_exn [] in
  let ms = {mregs = regs; mcvars = cvar_map; mflags = flags; mmem = mem; } in
 
  (* print_mstate ms; *)
  interp_stmt ms efun_map stmt
