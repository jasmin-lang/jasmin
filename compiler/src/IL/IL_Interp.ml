(* * Interpreter for IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Util
open Arith
open IL_Lang
open IL_Compile
open IL_Utils
open IL_Typing

(* ** Interpreter
 * ------------------------------------------------------------------------ *)

let is_Simm = function Simm _ -> true | _ -> false
let is_Comment = function Comment _ -> true | _ -> false

type mstate =
  { mregs  : u64 Preg.Map.t
  ; mflags : bool Preg.Map.t
  ; mmem   : u64 U64.Map.t
  }

let print_mstate ms =
  F.printf "regs: %a\n" (pp_list ", " (pp_pair " -> " pp_preg pp_uint64))
    (Preg.Map.to_alist ms.mregs);
  F.printf "flags: %a\n" (pp_list ", " (pp_pair " -> " pp_preg pp_bool))
    (Preg.Map.to_alist ms.mflags);
  F.printf "mem: %a\n" (pp_list ", " (pp_pair " -> " pp_uint64 pp_uint64))
    (U64.Map.to_alist ms.mmem)

let get_addr addr_r offset =
  let offset = U64.of_int64 offset in
  let c8 = U64.of_int 8 in
  (* we only allow aligned reads/writes *)
  assert (U64.is_zero (U64.rem offset c8));
  U64.add addr_r offset

let rec read_src ms s =
  match s with
  | Simm i -> U64.of_int64 i
  | Sreg r ->
    begin match Map.find ms.mregs r with
    | Some x -> x
    | None   -> 
      failwith (fsprintf "cannot read register %a" pp_preg r)
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

    | App(Assgn,[d],[s]) ->
      let x = read_src ms s in
      write_dest ms d x

    | App(UMul,[h;l],[x;y]) ->
      let x = read_src ms x in
      let y = read_src ms y in
      let (zh,zl) = U64.umul x y in
      let ms = write_dest ms l zl in
      write_dest ms h zh

    | App(((Add | Sub) as op),dest,x::y::cf_in_list) ->
      let cf = match cf_in_list with
        | [cf_in] -> read_flag ms cf_in
        | []      -> false
        | _       -> assert false
      in
      let x = read_src ms x in
      let y = read_src ms y in
      let (zo,cfo) =
        match op with
        | Add -> U64.add_carry x y cf
        | Sub -> U64.sub_carry x y cf
        | _ -> assert false
      in
      let (mcf_out, z) = match dest with
        | [cf_out; z] -> (Some cf_out, z)
        | [z]         -> (None,z)
        | _           -> assert false
      in
      let ms = write_dest ms z zo in
      begin match mcf_out with
      | Some cf_out -> write_flag ms cf_out cfo
      | None        -> ms
      end

    | App(Cmov(CfSet cf_is_set),[d],[s1;s2;cf_in])  ->
      let s1 = read_src ms s1 in
      let s2 = read_src ms s2 in
      let cf = read_flag ms cf_in in
      let res = if cf = cf_is_set then s2 else s1 in
      write_dest ms d res

    | App(IMul,[z], [x;y])  ->
      assert (is_Simm y);
      let x = read_src ms x in
      let y = read_src ms y in
      write_dest ms z (fst (U64.imul_trunc x y))
    
    | App(BAnd,[_d],[_s1;_s2]) ->
      failwith "not implemented"

    | App(Xor, [_d],[_s1;_s2]) ->
      failwith "not implemented"

    | App(Shift(_dir),[_cf_out;_z],[_x;_cn]) ->
      failwith "not implemented"

    (* handled separately *)
    | Comment _ -> assert false

    (* wrong arity *)
    | App(Assgn,([] | _::_::_),_)                            -> assert false
    | App(Assgn,_,([] | _::_::_))                            -> assert false
    | App(IMul,([] | _::_::_),  _)                           -> assert false
    | App(IMul,_, ([] | [_] | _::_::_::_))                   -> assert false
    | App((Add | Sub),([] | [_] | _::_::_::_),_)             -> assert false
    | App((Add | Sub),_,([] | [_] )) -> assert false
    | App((BAnd | Xor),([] | _::_::_),_)                     -> assert false
    | App((BAnd | Xor),_,([] | [_] | _::_::_::_))            -> assert false
    | App(Cmov _,([] | _::_::_),_)                           -> assert false
    | App(Cmov _,_,([] | [_] | [_;_]| _::_::_::_::_))        -> assert false
    | App((UMul | Shift _),_,([] | [_] | _::_::_::_))        -> assert false
    | App((UMul | Shift _),([] | [_] | _::_::_::_),_)        -> assert false
  in
  if not (is_Comment binstr) then (
    (* F.printf "####################################\n"; 
    F.printf "executing: %a\n" pp_base_instr binstr; *)
    let ms = go binstr in
    (* print_mstate ms; *)
    ms
  ) else (
    ms
  )

let interp_base_instrs
  (ms0 : mstate)
  (instrs : base_instr list)
  =
  List.fold instrs
    ~f:(fun ms i -> interp_base_instr ms i)
    ~init:ms0

let interp_stmt
  (ms : mstate)
  cvar_map
  stmt
  =
  let instrs = macro_expand cvar_map stmt in
  interp_base_instrs ms instrs  

let interp_string mem args string =
  let open ParserUtil in
  let efun_ut = List.hd_exn (parse ~parse:IL_Parse.efuns "" string) in
  let efun = efun_type efun_ut in
  let stmt = efun.ef_body in

  let arg_regs = efun.ef_args in
  let regs =
    Preg.Map.of_alist_exn
      (List.zip_exn arg_regs args)
  in
  let flags = Preg.Map.of_alist_exn [] in
  let ms = {mregs = regs; mflags = flags; mmem = mem } in
 
  let cvar_map = String.Map.of_alist_exn [("n", Big_int.big_int_of_int 3)] in
  (* print_mstate ms; *)
  interp_stmt ms cvar_map stmt
