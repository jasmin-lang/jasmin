(* * Interpreter for IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Util
open Arith
open IL_Lang
open IL_Utils
open IL_Typing

module P = ParserUtil

(* ** Interpreting compile-time expressions and conditions
 * ------------------------------------------------------------------------ *)

type pmap = u64 String.Map.t

let eval_pbinop = function
  | Pplus  -> U64.add
  | Pmult  -> U64.mul
  | Pminus -> U64.sub

let eval_pexpr pmap lmap ce =
  let rec go = function
    | Pbinop(o,ie1,ie2) ->
      begin match go ie1, go ie2 with
      | Ok(x1), Ok(x2) ->
        Ok(eval_pbinop o x1 x2)
      | Error(s), _
      | _, Error(s) ->
        Error(s)
      end
    | Pconst(c) -> Ok c
    | Pparam(s) ->
      begin match Map.find pmap s with
      | Some (x) -> Ok x
      | None     -> failwith_ "eval_pexpr: parameter %s undefined" s
      end
    | Pvar(s) ->
      begin match Map.find lmap s with
      | Some (Vu64 x) -> Ok x
      | Some (_) ->
        Error (fsprintf "eval_pexpr: variable %s of wrong type" s)
      | None ->
        Error (fsprintf "eval_pexpr: variable %s undefined" s)
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

let eval_pcond pmap lmap cc =
  let rec go = function
    | Ptrue              -> Ok(true)
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
    | Pcond(cco,ce1,ce2) ->
      begin match eval_pexpr pmap lmap ce1, eval_pexpr pmap lmap ce2 with
      | Ok(x1),Ok(x2) -> Ok(eval_pcondop cco x1 x2)
      | Error(s), _
      | _, Error(s) ->
        Error(s)
      end
  in
  go cc

let eval_pexpr_exn pmap lmap ce = 
  eval_pexpr pmap lmap ce |> Result.ok_or_failwith

let eval_pcond_exn pmap lmap cc = 
  eval_pcond pmap lmap cc |> Result.ok_or_failwith

(* ** Interpreter
 * ------------------------------------------------------------------------ *)

(* *** Interpreter state
 * ------------------------------------------------------------------------ *)

type py_state = {
  mutable py_closed : bool;
  py_cin    : in_channel;
  py_cout   : out_channel;
}

type mstate =
  { m_pmap : u64   String.Map.t (* parameter variables *)
  ; m_lmap : value String.Map.t (* (function) local variables *)
  ; m_fmap : bool  String.Map.t (* flags *)
  ; m_mmap : u64   U64.Map.t    (* memory *)
  ; m_tenv : ty    String.Map.t (* declarations *)
  ; m_py   : py_state option    (* state of python interpreter *)
  }

let print_mstate ms =
  F.printf "cvars: %a\n" (pp_list ", " (pp_pair " -> " pp_string pp_uint64))
    (String.Map.to_alist ms.m_pmap);
  F.printf "regs: %a\n" (pp_list ", " (pp_pair " -> " pp_string pp_value))
    (String.Map.to_alist ms.m_lmap);
  F.printf "flags: %a\n" (pp_list ", " (pp_pair " -> " pp_string pp_bool))
    (String.Map.to_alist ms.m_fmap);
  F.printf "mem: %a\n" (pp_list ", " (pp_pair " -> " pp_uint64 pp_uint64))
    (U64.Map.to_alist ms.m_mmap);
  F.printf "decls: %a\n%!" (pp_list ", " (pp_pair " -> " pp_string pp_ty))
    (String.Map.to_alist ms.m_tenv)

let read_lvar lmap s oidx =
  let v = map_find_exn lmap pp_string s in
  match v, oidx with
  | Vu64(u), None -> Vu64(u)
  | Varr(vs),Some i ->
    Vu64(map_find_exn vs pp_uint64 i)
  | Varr(vs),None -> Varr(vs)
  | Vu64(_), _ ->
    failwith_ "read_lvar: expected array, got u64 in %s[%a]"
      s (pp_opt "," pp_uint64) oidx

let read_src_val pmap lmap (s : src) =
  match s with
  | Imm pe -> Vu64(eval_pexpr_exn pmap lmap pe)
  | Src(d) ->
    let oidx = Option.map (d.d_oidx) ~f:(eval_pexpr_exn pmap lmap) in
    read_lvar lmap d.d_name oidx

let read_src_ pmap lmap (s : src) =
  match read_src_val pmap lmap s with
  | Vu64(u) -> u
  | Varr(_) ->
    failwith_ "read_src: expected u64, got array for %a"
      pp_src s

let read_src ms = read_src_ ms.m_pmap ms.m_lmap

let write_lvar ov s oidx v =
  match ov, oidx, v with
  | _,             None   , _       -> v
  | None,          Some(i), Vu64(u) -> Varr(U64.Map.singleton i u)
  | Some(Varr(vs)),Some(i), Vu64(u) -> Varr(Map.add vs ~key:i ~data:u)
  | _,             Some(_), Varr(_) ->
    failwith_ "write_lvar: cannot write array to %s[%a]"
      s (pp_opt "_" pp_uint64) oidx
  | Some(Vu64(_)), Some(_), _ ->
    failwith_ "write_lvar: expected array, got u64 in %s[%a]"
      s (pp_opt "_" pp_uint64) oidx

let write_dest_ pmap lmap d v =
  let s    = d.d_name in
  let ov   = Map.find lmap s in
  let oidx = Option.map d.d_oidx ~f:(eval_pexpr_exn pmap lmap) in
  (* F.printf "###: %a\n%!" pp_value v; *)
  let nv   = write_lvar ov s oidx v in
  (* F.printf "###: %a\n%!" pp_value v'; *)
  Map.add lmap ~key:s ~data:nv

let write_dest ms d x =
  { ms with m_lmap = write_dest_ ms.m_pmap ms.m_lmap d x }

let write_dest_u64 ms d u = write_dest ms d (Vu64(u))

let read_flag ms s =
  match s with
  | Src{d_name; d_oidx=None} -> map_find_exn ms.m_fmap pp_string d_name
  | Src{d_oidx=Some(_)}      -> failwith "expected flag, got array access" 
  | Imm _                    -> failwith "expected flag, got immediate"

let write_flag ms d b =
  match d.d_oidx with
  | None    -> { ms with m_fmap = Map.add ms.m_fmap ~key:d.d_name ~data:b }
  | Some(_) -> failwith "cannot give array element, flag (in register) expected"

(* *** Interact with python interpreter
 * ------------------------------------------------------------------------ *)

let sage_dir =
  try
    Sys.getenv "SAGE_DIR"
  with Not_found ->
    failwith "Set environment variable SAGE_DIR to sage directory (containing bin/sage)"

(* let py_cmd = sage_dir^"/bin/sage -python -i" *)
let py_cmd = "/usr/bin/python -i"

let start_py () =
  let (c_in, c_out) = Unix.open_process py_cmd in
  { py_cin = c_in; py_cout = c_out; py_closed = false }

let eval_py_ pst cmd =
  if pst.py_closed then failwith "python process already closed";
  let (c_in, c_out) = pst.py_cin, pst.py_cout in
  output_string c_out cmd;
  flush c_out;
  (* result is last line of output *)
  (* F.printf "### eval_py_: waiting for python output for ``%s''\n%!" cmd; *)
  let res = input_line c_in in
  (* F.printf "### eval_py_: got python output ``%s''\n%!" res; *)
  res

let stop_sage pst =
  if pst.py_closed then failwith "sage process already closed";
  let (c_in, c_out) = pst.py_cin, pst.py_cout in
  let cmd = "exit()" in
  output_string c_out cmd;
  flush c_out;
  let o = input_line c_in in
  if o <> "end" then failwith "close: end expected";
  ignore (Unix.close_process (c_in,c_out))

let eval_py ms cmd =
  let pst =
    match ms.m_py with
    | None     -> failwith "impossible"
    | Some pst -> pst
  in
  let res = eval_py_ pst cmd in
  (res, { ms with m_py = Some pst })

(* *** Interpret operation
 * ------------------------------------------------------------------------ *)

let is_Simm = function Imm _ -> true | _ -> false

let interp_op (ms : mstate) z x y = function

  | Umul(h) ->
    let x = read_src ms x in
    let y = read_src ms y in
    let (zh,zl) = U64.umul x y in
    let ms = write_dest_u64 ms z zl in
    write_dest_u64 ms h zh

  | Carry(cop,mcf_out,mcf_in) ->
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
    let ms = write_dest_u64 ms z zo in
    begin match mcf_out with
    | Some cf_out -> write_flag ms cf_out cfo
    | None        -> ms
    end

  | CMov(CfSet cf_is_set,cf_in)  ->
    let s1 = read_src ms x in
    let s2 = read_src ms y in
    let cf = read_flag ms cf_in in
    let res = if cf = cf_is_set then s2 else s1 in
    write_dest_u64 ms z res

  | ThreeOp(O_Imul) ->
    if not (is_Simm y) then
      failwith_ "expected immediate value for %a in IMul" pp_src y;
    let x = read_src ms x in
    let y = read_src ms y in
    write_dest_u64 ms z (fst (U64.imul_trunc x y))
    
  | ThreeOp(O_Xor | O_And | O_Or as o) ->
    let x = read_src ms x in
    let y = read_src ms y in
    let f_op =
      match o with
      | O_Xor -> U64.logxor
      | O_And -> U64.logand
      | O_Or  ->
        (* F.printf "\n## %a or %a = %a\n%!" pp_uint64 x pp_uint64 y pp_uint64
          (U64.logor x y); *)
        U64.logor
      | _     -> failwith "impossible"
    in
    write_dest_u64 ms z (f_op x y)

  | Shift(dir,None) ->
    (* if not (is_Simm y) then
         failwith_ "expected immediate value for %a in Shift" pp_src y; *)
    let x = read_src ms x in
    let y = read_src ms y in
    let op = match dir with Left -> U64.shift_left | Right -> U64.shift_right in
    write_dest_u64 ms z (op x (U64.to_int y))

  | Shift(_dir,Some(_)) ->
    failwith "not implemented yet"


(* *** Interpret instruction
 * ------------------------------------------------------------------------ *)

let interp_assign pmap ~lmap_lhs ~lmap_rhs ds ss =
  let ss_ds =
    try List.zip_exn ss ds
    with Invalid_argument _ ->
      failwith_
        "assignment %a = %a failed, lhs and rhs have different dimensions (%a = %a)"
        (pp_list "," pp_dest) ds (pp_list "," pp_src) ss (pp_list "," pp_src)
        ss (pp_list "," pp_dest) ds
  in
  List.fold ss_ds
    ~init:lmap_lhs
    ~f:(fun lmap (s,d) -> write_dest_ pmap lmap d (read_src_val pmap lmap_rhs s))

let rec interp_instr ms0 efun_map linstr =
  (* F.printf "\ninstr: %a\n%!" pp_instr instr;
     print_mstate ms0; *)
  let pmap = ms0.m_pmap in
  match linstr.L.l_val with

  | Binstr(Comment(_)) ->
    ms0

  | Binstr(Assgn(d,s,_)) ->
    let lmap = interp_assign pmap ~lmap_lhs:ms0.m_lmap ~lmap_rhs:ms0.m_lmap [d] [s] in
    { ms0 with m_lmap = lmap }

  | Binstr(Load(d,s,pe)) ->
    let ptr = read_src ms0 s in
    let c = eval_pexpr_exn pmap ms0.m_lmap pe in
    let v = map_find_exn ms0.m_mmap pp_uint64 (U64.add c ptr) in
    write_dest ms0 d (Vu64 v)

  | Binstr(Store(s1,pe,s2)) ->
    let v = read_src ms0 s2 in
    let ptr = read_src ms0 s1 in
    let c = eval_pexpr_exn pmap ms0.m_lmap pe in
    { ms0 with
      m_mmap = Map.add ms0.m_mmap ~key:(U64.add ptr c) ~data:v }

  | Binstr(Op(o,d,(s1,s2))) ->
    interp_op ms0 d s1 s2 o

  | If(ccond,stmt1,stmt2) ->
    if eval_pcond_exn pmap ms0.m_lmap ccond then
      interp_stmt ms0 efun_map stmt1
    else
      interp_stmt ms0 efun_map stmt2

  | For(t,cv,clb,cub,stmt) ->
    let lb = eval_pexpr_exn pmap ms0.m_lmap clb in
    let ub = eval_pexpr_exn pmap ms0.m_lmap cub in
    let (initial, test, change) =
      if U64.compare lb ub < 0
      then (
        (lb, (fun i -> U64.compare i ub < 0), U64.succ)
      ) else ( (* 64 .. 0 -> 63,62,..,0 *)
        assert (U64.compare U64.zero lb < 0);
        (U64.pred lb, (fun i -> U64.compare i ub >= 0 && U64.compare i lb <= 0 )
        , U64.pred)
      )
    in
    let update ms i =
      { ms with m_lmap = Map.add ms.m_lmap ~key:cv ~data:(Vu64 i) }
    in
    let old_val = Map.find ms0.m_lmap cv in
    let ms = ref ms0 in
    let i = ref initial in
    while test !i do
      if false then (
        F.printf "\nfor%s %s=%a in %a..%a\n%!"
          (if t = Unfold then "" else ":")
          cv pp_uint64 !i pp_uint64 lb pp_uint64 ub);
      ms := update !ms !i;
      ms := interp_stmt !ms efun_map stmt;
      i := change !i;
    done;
    { !ms with
      m_lmap = Map.change !ms.m_lmap cv (fun _ -> old_val) }

  | Binstr(Call(fname,rets,args)) ->
    interp_call ms0 efun_map fname rets args

and interp_call ms efun_map fname call_rets call_args =
  (** look up function definition *)
  let func = map_find_exn efun_map pp_string fname in
  match func.f_def with
  | Def fdef   -> interp_call_native ms efun_map func fdef    call_rets call_args
  | Py py_code -> interp_call_python ms          func py_code call_rets call_args
  | Undef      -> failwith "Calling undefined function (only declared)"

and interp_call_python ms func py_code call_rets call_args =
  let decl_args = List.map func.f_args ~f:(fun (_,n,_) -> mk_dest_name n) in
  (** compute lmap for callee *)
  let pmap = ms.m_pmap in
  let lmap_caller = ms.m_lmap in
  let lmap_callee = String.Map.empty in
  let lmap_callee =
    interp_assign pmap
      ~lmap_lhs:lmap_callee ~lmap_rhs:lmap_caller
      decl_args call_args
  in
  (** execute function body *)
  let s_params =
    fsprintf "{%a}" (pp_list "," pp_string)
      (List.map (Map.to_alist ms.m_pmap)
        ~f:(fun (s,v) -> fsprintf "'%s' : %a" s pp_uint64 v))
  in
  let s_args =
    List.map func.f_args
      ~f:(fun (_,s,_) -> fsprintf "%a" pp_value_py (Map.find_exn lmap_callee s))
  in    
  let (res,ms) =
    eval_py ms
      (fsprintf "res = %s(%a)\nprint(str(res))\n" py_code
        (pp_list "," pp_string) (s_args@[s_params]))
  in
  let rets = parse_value res in
  (** store result *)
  let ss_ds = match call_rets with
    | [ds] -> [ (rets,ds) ]
    | []   -> []
    | _    -> assert false
  in
  let lmap_caller =
    List.fold ss_ds
      ~init:lmap_caller
      ~f:(fun lmap (s,d) -> write_dest_ pmap lmap d s)
  in
  { ms with m_lmap = lmap_caller; }

and interp_call_native ms efun_map func fdef call_rets call_args =
  let decl_args = List.map func.f_args ~f:(fun (_,name,_) -> mk_dest_name name) in
  let decl_rets = List.map fdef.fd_ret ~f:(fun n -> Src(mk_dest_name n)) in
  (** setup mstate for called function *)
  let pmap = ms.m_pmap in
  let tenv_caller = ms.m_tenv in
  let lmap_caller = ms.m_lmap in
  let fmap_caller = ms.m_fmap in
  let tenv_callee = tenv_of_func func fdef.fd_decls in
  let lmap_callee = String.Map.empty
    (* String.Map.of_alist_exn
       (List.map ~f:(fun (n,v) -> (n,Vu64 v)) (Map.to_alist pmap)) *)
  in
  let fmap_callee = String.Map.empty in
  let lmap_callee =
    interp_assign pmap
      ~lmap_lhs:lmap_callee ~lmap_rhs:lmap_caller
      decl_args call_args
  in
  let ms = (* keep pmap and mmap *)
    { ms with m_lmap = lmap_callee; m_fmap = fmap_callee; m_tenv = tenv_callee }
  in
  (** execute function body *)
  let ms = interp_stmt ms efun_map fdef.fd_body in
  (** store result *)
  let lmap_callee = ms.m_lmap in
  let lmap_caller =
    interp_assign pmap
      ~lmap_lhs:lmap_caller ~lmap_rhs:lmap_callee
      call_rets decl_rets
  in
  { ms with m_lmap = lmap_caller; m_fmap = fmap_caller; m_tenv = tenv_caller }

and interp_stmt (ms0 : mstate) efun_map stmt =
  List.fold stmt
    ~f:(fun ms i -> interp_instr ms efun_map i)
    ~init:ms0

(* *** Interpret function (in module)
 * ------------------------------------------------------------------------ *)

let interp_modul
  (modul : modul) (pmap : u64 String.Map.t) (mmap : u64 U64.Map.t)
  (args : value list) (fname : string)
  =
  typecheck_modul modul;
  let func_map =
    String.Map.of_alist_exn (List.map ~f:(fun f -> (f.f_name,f)) modul.m_funcs)
  in
  let func = map_find_exn func_map pp_string fname in
  let fdef = match func.f_def with 
    | Def d -> d
    | Undef | Py _ -> failwith_ "cannot call undefined function %s" fname
  in
  let stmt = fdef.fd_body in
  let f_args = func.f_args in
  if List.length f_args <> List.length args then
    failwith_ "interp_string: wrong number of arguments given (got %i, exp. %i)"
      (List.length args) (List.length f_args);
  (* FIXME: typecheck arguments and parameters *)
  let lmap =
    String.Map.of_alist_exn
      (List.zip_exn (List.map f_args ~f:(fun (_,n,_) -> n)) args)
  in
  let fmap = String.Map.of_alist_exn [] in
  let tenv = tenv_of_func func fdef.fd_decls in
  let pst =
      F.printf "### starting python\n%!";
      let pst = start_py () in
      F.printf "### loading dmasm_lib\n%!";
      output_string pst.py_cout "from dmasm_lib import *\n";
      flush pst.py_cout;
      let _ = eval_py_ pst "confirm_started()\n"  in
      F.printf "\n### dmasm_lib loaded\n%!";
      pst
  in
  let ms =
    { m_lmap = lmap
    ; m_pmap = pmap
    ; m_fmap = fmap
    ; m_mmap = mmap
    ; m_tenv = tenv
    ; m_py   = Some pst
    }
  in
  (* print_endline "#########################"; *)
  (* print_endline "## initial state"; *)
  (* print_mstate ms; *)
  let _ms = interp_stmt ms func_map stmt in
  (* print_endline "#########################"; *)
  (* print_endline "## state after execution"; *)
  (* print_mstate ms; *)
  (* print_endline "#########################"; *)
  modul
