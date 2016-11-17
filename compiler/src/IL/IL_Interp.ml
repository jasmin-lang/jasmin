(* * Interpreter for IL *)

(* ** Imports and abbreviations *)
open Core_kernel.Std
open Util
open Arith
open IL_Lang
open IL_Utils
open IL_Pprint
open IL_Iter
open IL_Typing
open IL_Expand

module P = ParserUtil

(* ** Interpreter
 * ------------------------------------------------------------------------ *)

(* *** Interpreter state
 * ------------------------------------------------------------------------ *)

type py_state = {
  mutable py_closed : bool;
  py_cin    : in_channel;
  py_cout   : out_channel;
}

type 'info mstate =
  { m_ptable  : big_int Pname.Table.t      (* parameter variables *)
  ; m_ltable  : value   Int.Table.t        (* (function) local variables *)
  ; m_fltable : bool    Int.Table.t        (* flags *)
  ; m_mtable  : u64     U64.Table.t        (* memory *)
  ; m_py      : py_state option          (* state of python interpreter *)
  ; m_ftable  : 'info func Fname.Table.t (* function environment *)
  }

(*
let print_mstate ms =
  F.printf "cvars: %a\n" (pp_list ", " (pp_pair " -> " pp_ident pp_uint64))
    (Map.to_alist ms.m_pmap);
  F.printf "regs: %a\n" (pp_list ", " (pp_pair " -> " pp_int64 pp_value))
    (Map.to_alist ms.m_lmap);
  F.printf "flags: %a\n" (pp_list ", " (pp_pair " -> " pp_int64 pp_bool))
    (Map.to_alist ms.m_fmap);
  F.printf "mem: %a\n" (pp_list ", " (pp_pair " -> " pp_uint64 pp_uint64))
    (Map.to_alist ms.m_mmap)
*)

(* *** Reading values
 * ------------------------------------------------------------------------ *)

let read_lvar ltable lv idx =
  let v = hashtbl_find_exn ltable pp_int lv.Var.num in
  match v, idx with
  | Vu(n,u), None     -> Vu(n,u)
  | Varr(n,vs),Some i -> Vu(n,map_find_exn vs pp_uint64 i)
  | Varr(n,vs),None   -> Varr(n,vs)
  | Vu(_,_), _ ->
    failwith_ "read_lvar: expected array, got u64 in %a[%a]"
      Var.pp lv (pp_opt "," pp_uint64) idx

let read_src_val ptable ltable (s : src) =
  match s with
  | Imm(i,pe) -> Vu(i,eval_pexpr_exn ptable ltable pe)
  | Src(d) ->
    let oidx = match d.d_idx with
      | None             -> None
      | Some(Ipexpr(pe)) -> Some(U64.of_big_int @@ eval_pexpr_exn ptable ltable pe)
      | Some(Ivar(v))    ->
        begin match read_lvar ltable v None with
        | Vu(64,u) -> Some(U64.of_big_int u)
        | _        -> assert false
        end
    in
    read_lvar ltable d.d_var oidx

let read_src_ pmap lmap (s : src) =
  match read_src_val pmap lmap s with
  | Vu(_,u) -> u
  | Varr(_) ->
    failwith_ "read_src: expected u64, got array for %a"
      pp_src_nt s

let read_src ms = read_src_ ms.m_ptable ms.m_ltable

let read_flag ms s =
  match s with
  | Src{d_var; d_idx=None} -> hashtbl_find_exn ms.m_fltable pp_int d_var.Var.num
  | Src{d_idx=Some(_)}     -> failwith "expected flag, got array access" 
  | Imm _                  -> failwith "expected flag, got immediate"

(* *** Writing values
 * ------------------------------------------------------------------------ *)

let write_lvar ov s oidx v =
  match ov, oidx, v with
  | _,               None   , _        -> v
  | None,            Some(i), Vu(n,u)  -> Varr(n,U64.Map.singleton i u)
  | Some(Varr(n,vs)),Some(i), Vu(m,u)  ->
    assert(n = m);
    Varr(n,Map.add vs ~key:i ~data:u)
  | _,               Some(_), Varr(_)  ->
    failloc_ s.Var.uloc "write_lvar: cannot write array to %a[%a]"
      Var.pp s (pp_opt "_" pp_uint64) oidx
  | Some(Vu(_)), Some(_), _ ->
    failloc_ s.Var.uloc "write_lvar: expected array, got u64 in %a[%a]"
      Var.pp s (pp_opt "_" pp_uint64) oidx

let write_dest_ ptable ltable d v =
  let s    = d.d_var in
  let ov   = HT.find ltable s.Var.num in
  let oidx = match d.d_idx with
    | None             -> None
    | Some(Ipexpr(pe)) -> Some(U64.of_big_int @@ eval_pexpr_exn ptable ltable pe)
    | Some(Ivar(_))    -> failwith "not implemented"
  in
  (* F.printf "###: write value %a -> %a\n%!" pp_dest_nt d pp_value v; *)
  let nv = write_lvar ov s oidx v in
  (* F.printf "###: new value %a -> %a\n%!" pp_dest_nt d pp_value nv; *)
  HT.set ltable ~key:s.Var.num ~data:nv

let write_dest ms d x =
  write_dest_ ms.m_ptable ms.m_ltable d x

let write_dest_u64 ms d u = write_dest ms d (Vu(64,u))

let write_flag ms d b =
  match d.d_idx with
  | None    -> HT.set ms.m_fltable ~key:d.d_var.Var.num ~data:b
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

(* *** Interpret operations
 * ------------------------------------------------------------------------ *)

let is_Simm = function Imm _ -> true | _ -> false

let interp_op (ms : 'info mstate) o ds ss =
  let to_bi = U64.to_big_int in
  let of_bi = U64.of_big_int in
  match view_op o ds ss with
  | V_Umul(h,z,x,y) ->
    let x = read_src ms x in
    let y = read_src ms y in
    let (zh,zl) = U64.umul (of_bi x) (of_bi y) in
    write_dest_u64 ms z (to_bi zl);
    write_dest_u64 ms h (to_bi zh)

  | V_Carry(cop,mcf_out,z,x,y,mcf_in) ->
    let cf =
      Option.value_map mcf_in ~default:false ~f:(fun cf -> read_flag ms cf)
    in
    let x = read_src ms x in
    let y = read_src ms y in
    let (zo,cfo) =
      match cop with
      | O_Add -> U64.add_carry (of_bi x) (of_bi y) cf
      | O_Sub -> U64.sub_carry (of_bi x) (of_bi y) cf
    in
    write_dest_u64 ms z (to_bi zo);
    begin match mcf_out with
    | Some cf_out -> write_flag ms cf_out cfo
    | None        -> ()
    end

  | V_Cmov(neg,z,x,y,cf)  ->
    let s1 = read_src ms x in
    let s2 = read_src ms y in
    let cf = read_flag ms cf in
    let res = if cf <> neg then s2 else s1 in
    write_dest_u64 ms z res

  | V_ThreeOp(O_Imul,z,x,y) ->
    (* if not (is_Simm y) then *)
      (* failwith_ "expected immediate value for %a in IMul" pp_src_nt y; *)
    let x = read_src ms x in
    let y = read_src ms y in
    write_dest_u64 ms z (to_bi @@ fst (U64.imul_trunc (of_bi x) (of_bi y)))
    
  | V_ThreeOp(O_Xor | O_And | O_Or as o,z,x,y) ->
    let x = read_src ms x in
    let y = read_src ms y in
    let f_op =
      match o with
      | O_Xor -> U64.logxor
      | O_And -> U64.logand
      | O_Or  -> U64.logor
      | _     -> failwith "impossible"
    in
    write_dest_u64 ms z (to_bi @@ f_op (of_bi x) (of_bi y))

  | V_Shift(dir,None,z,x,y) ->
    (* if not (is_Simm y) then
         failwith_ "expected immediate value for %a in Shift" pp_src y; *)
    let x = read_src ms x in
    let y = read_src ms y in
    let op = match dir with Left -> U64.shift_left | Right -> U64.shift_right in
    write_dest_u64 ms z (to_bi @@ op (of_bi x) (U64.to_int (of_bi y)))

  | V_Shift(_dir,Some(_),_,_,_) ->
    failwith "not implemented yet"

(* *** Interpret instruction
 * ------------------------------------------------------------------------ *)

let eval_fcond_exn fltable fc =
  let b = hashtbl_find_exn fltable pp_int fc.fc_var.Var.num in
  if fc.fc_neg then not b else b

let eval_fcond_or_pcond_exn ptable ltable fltable = function
  | Fcond(fc) -> eval_fcond_exn fltable fc
  | Pcond(pc) -> eval_pcond_exn ptable ltable pc

let interp_assign ptable ltable ds ss =
  let ss_ds =
    try List.zip_exn ss ds
    with Invalid_argument _ ->
      failwith_
        "assignment %a = %a failed, lhs and rhs have different dimensions (%a = %a)"
        (pp_list "," pp_dest_nt) ds (pp_list "," pp_src_nt) ss (pp_list "," pp_src_nt)
        ss (pp_list "," pp_dest_nt) ds
  in
  let vs_ds = List.map ss_ds ~f:(fun (s,d) -> (read_src_val ptable ltable s,d)) in
  List.iter vs_ds ~f:(fun (v,d) -> write_dest_ ptable ltable d v)

let rec interp_base_instr ms lbinstr =
  let to_bi = U64.to_big_int in
  let of_bi = U64.of_big_int in
  let ptable = ms.m_ptable in
  match lbinstr.L.l_val with
  | Comment(_) -> ()

  | Op(o,ds,ss) -> interp_op ms o ds ss

  | Call(fname,rets,args) -> interp_call ms fname rets args

  | Assgn(d,s,_) ->
    interp_assign ptable ms.m_ltable [d] [s]

  | Load(d,s,pe) -> (* FIXME: we should be able to load different sizes *)
    let ptr = read_src ms s in
    let c = eval_pexpr_exn ptable ms.m_ltable pe in
    let v = hashtbl_find_exn ms.m_mtable pp_uint64 (U64.add (of_bi c) (of_bi ptr)) in
    write_dest ms d (Vu(64,to_bi v))

  | Store(s1,pe,s2) ->
    let v = read_src ms s2 in
    let ptr = read_src ms s1 in
    let c = eval_pexpr_exn ptable ms.m_ltable pe in
    HT.set ms.m_mtable ~key:(U64.add (of_bi ptr) (of_bi c)) ~data:(of_bi v)

and interp_instr ms linstr =
  (* F.printf "\ninstr: %a\n%!" pp_instr instr;
     print_mstate ms0; *)
  let ptable = ms.m_ptable in
  match linstr.L.l_val with
  | Block(bis,_) ->    
    List.iter bis
      ~f:(fun lbi -> interp_base_instr ms lbi)

  | If(ccond,stmt1,stmt2,_) ->
    if eval_fcond_or_pcond_exn ptable ms.m_ltable ms.m_fltable ccond then
      interp_stmt ms stmt1
    else
      interp_stmt ms stmt2
 
  | While(WhileDo,fc,s,_) ->
    if (eval_fcond_exn ms.m_fltable fc) then (
      interp_stmt ms s;
      interp_instr ms linstr
    ) 

  | While(DoWhile,fc,s,_) ->
    interp_stmt ms s;
    if (eval_fcond_exn ms.m_fltable fc) then (
      interp_instr ms linstr
    )
  
  | For(cv,clb,cub,s,_) ->
    let cmp = Big_int.compare_big_int in
    let lb = eval_pexpr_exn ptable ms.m_ltable clb in
    let ub = eval_pexpr_exn ptable ms.m_ltable cub in
    let (initial, test, change) =
      if Big_int.compare_big_int lb ub < 0
      then (
        (lb, (fun i -> cmp i ub < 0), Big_int.succ_big_int)
      ) else ( (* 64 .. 0 -> 63,62,..,0 *)
        assert (cmp Big_int.zero_big_int lb < 0);
        (Big_int.pred_big_int lb, (fun i -> cmp i ub >= 0 && cmp i lb <= 0 )
        , Big_int.pred_big_int)
      )
    in
    let update i =
      HT.set ms.m_ltable ~key:cv.d_var.Var.num ~data:(Vu(64,i))
    in
    let old_val = HT.find ms.m_ltable cv.d_var.Var.num in
    let i = ref initial in
    while test !i do
      if false then (
        F.printf "\nfor %a=%a in %a..%a\n%!"
          pp_dest_nt cv pp_big_int !i pp_big_int lb pp_big_int ub);
      update !i;
      interp_stmt ms s;
      i := change !i;
    done;
    HT.change ms.m_ltable cv.d_var.Var.num ~f:(fun _ -> old_val)

and interp_call ms fname call_rets call_args = 
  (* look up function definition *)
  let func = hashtbl_find_exn ms.m_ftable Fname.pp fname in
  match func with
  | Native(fd) -> interp_call_native ms fd call_rets call_args
  | Foreign(fo) ->
    begin match fo.fo_py_def with 
    | None    -> failwith "Calling undefined function (only declared)"
    | Some(s) -> interp_call_python ms s call_rets call_args
    end

and interp_call_python ms py_code call_rets call_args =
  let ptable = ms.m_ptable in
  let ltable = ms.m_ltable in
  let s_params =
    fsprintf "{%a}" (pp_list "," pp_string)
      (List.map (HT.to_alist ms.m_ptable)
        ~f:(fun (pn,v) -> fsprintf "'%a' : %a" Pname.pp pn pp_big_int v))
  in
  let vs = List.map call_args ~f:(fun s -> read_src_val ptable ltable s) in
  let s_args = List.map vs ~f:(fun v -> fsprintf "%a" pp_value_py v) in    
  let res,_ =
    eval_py ms
      (fsprintf "res = %s(%a)\nprint(str(res))\n" py_code
        (pp_list "," pp_string) (s_args@[s_params]))
  in
  let rets = parse_value res in
  (* store result *)
  let ss_ds = match call_rets with
    | [ds] -> [ (rets,ds) ]
    | []   -> []
    | _    -> assert false
  in
  List.iter ss_ds ~f:(fun (s,d) -> write_dest_ ptable ltable d s)

and interp_call_native ms fd call_rets call_args =
  (* setup mstate for called function *)
  let ptable = ms.m_ptable in
  let ltable = ms.m_ltable in
  let mkd v = {d_var=v; d_idx=None; d_loc=v.Var.uloc} in
  (* load arguments *)
  let vs = List.map call_args ~f:(fun s -> read_src_val ptable ltable s) in
  List.iter2_exn fd.f_arg vs
    ~f:(fun var v -> write_dest ms (mkd var) v);

  (* execute function body *)
  interp_stmt ms fd.f_body;

  (* store result *)
  let vs = List.map fd.f_ret ~f:(fun v -> read_src_val ptable ltable (Src(mkd v))) in
  List.iter2_exn call_rets vs ~f:(fun d v -> write_dest ms d v)

and interp_stmt (ms : 'info mstate) stmt =
  List.iter stmt
    ~f:(fun li -> interp_instr ms li)

(* *** Interpret function (in module)
 * ------------------------------------------------------------------------ *)

let interp_modul
  (modul : 'info modul) (ptable : big_int Pname.Table.t) (mtable : u64 U64.Table.t)
  (_args : value list) (fname : Fname.t)
  =
  let modul = renumber_vars_modul_all UniqueNumModule modul in
  vars_num_unique_modul ~type_only:false modul; (* FIXME: everything must be unique, test this *)
  typecheck_modul modul;
  let ftable = Fname.Table.of_alist_exn (List.map ~f:(fun nf -> (nf.nf_name,nf.nf_func)) modul) in
  let func = hashtbl_find_exn ftable Fname.pp fname in
  let fd = get_fundef ~err_s:"interpreter " func in
  let stmt = fd.f_body in
  (*
  let f_args = func.f_args in
  if List.length f_args <> List.length args then
    failwith_ "interp_string: wrong number of arguments given (got %i, exp. %i)"
      (List.length args) (List.length f_args);
  *)
  (* FIXME: typecheck arguments and parameters *)
  let ltable = Int.Table.create ()
    (* Int64.Map.of_alist_exn *)
      (* (List.map2_exn ~f:(fun (_,i,_) a -> (i.i_num,a)) f_args args) *)
  in
  let fltable = Int.Table.create () in
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
    { m_ltable  = ltable
    ; m_ptable  = ptable
    ; m_fltable = fltable
    ; m_mtable  = mtable
    ; m_py      = Some pst
    ; m_ftable  = ftable
    }
  in
  (* print_endline "#########################"; *)
  (* print_endline "## initial state"; *)
  (* print_mstate ms; *)
  let _ms = interp_stmt ms stmt in
  (* print_endline "#########################"; *)
  (* print_endline "## state after execution"; *)
  (* print_mstate ms; *)
  (* print_endline "#########################"; *)
  ()
