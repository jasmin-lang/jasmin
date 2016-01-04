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

let eval_pexpr pmap ce =
  let rec go = function
    | Pbinop(o,ie1,ie2) -> eval_pbinop o (go ie1) (go ie2)
    | Pconst(c)         -> c
    | Pvar(s) ->
      begin match Map.find pmap s with
      | Some x -> x
      | None   -> failwith ("eval_cexpr: parameter "^s^" undefined")
      end
  in
  go ce

let eval_pcondop pc  = fun x y ->
  match pc with
  | Peq      -> U64.equal x y
  | Pineq    -> not (U64.equal x y)
  | Pless    -> U64.compare x y < 0
  | Pgreater -> U64.compare x y > 0
  | Pleq     -> U64.compare x y <= 0
  | Pgeq     -> U64.compare x y >= 0

let eval_pcond pmap cc =
  let rec go = function
    | Ptrue              -> true
    | Pnot(ic)           -> not (go ic)
    | Pand(cc1,cc2)      -> (go cc1) && (go cc2)
    | Pcond(cco,ce1,ce2) ->
      eval_pcondop cco (eval_pexpr pmap ce1) (eval_pexpr pmap ce2)
  in
  go cc
 
(* ** Interpreter
 * ------------------------------------------------------------------------ *)

(* *** Expansion of ranges
 * ------------------------------------------------------------------------ *)

let expand_get_or_all pmap dim idx =
  match idx with
  | Get pe -> [pe]
  | All(lb_o,ub_o) ->
    let zero = Pconst U64.zero in
    let lb = get_opt zero lb_o |> eval_pexpr pmap in
    let ub = get_opt dim ub_o |> eval_pexpr pmap in
    List.map (list_from_to ~first:lb ~last:ub) ~f:(fun c -> Pconst c)

let expand_dest (pmap : pmap) (tenv : tenv) d =
  match map_find_exn tenv pp_string d.d_pr.pr_name with
  | Bool -> failwith "Boolean arguments not allowed"
  | U64(pr_dims,arr_dims) ->
    let aidxs =
      if d.d_aidxs <> [] then d.d_aidxs
      else List.map ~f:(fun _ -> All(None,None)) arr_dims
    in
    let n_pd = List.length pr_dims in
    let n_pi = List.length d.d_pr.pr_idxs in
    let n_ad = List.length arr_dims in
    let n_ai = List.length aidxs in
    if n_pd <> n_pi then
      failwith_ "register indexes not fully applied (dim %i, args %i" n_pd n_pi;
    if n_ad <> n_ai then
      failwith_ "array indexes not fully applied (dim %i, args %i" n_ad n_ai;
    let dims = pr_dims@arr_dims in
    let idxs = d.d_pr.pr_idxs@aidxs in
    begin match idxs with
    | [] -> [{ d_aidxs = []; d_pr = { d.d_pr with pr_idxs = [] } }]
    | _::_ ->
      list_map2_exn ~f:(expand_get_or_all pmap) dims idxs
        ~err:(fun l_exp l_got ->
                failwith_ "expected %i, got %i in expand_dest" l_got l_exp)
      |> cartesian_product_list
      |> List.map ~f:(fun idxs -> { d_aidxs = []; d_pr = { d.d_pr with pr_idxs = idxs } })
    end

let expand_src (pmap : pmap) (tenv : tenv) = function
  | Imm(_) as s -> [s]
  | Src(d)      -> List.map (expand_dest pmap tenv d) ~f:(fun d -> Src(d))

let dest_of_arg (name,ty) =
  match ty with
  | Bool -> assert false
  | U64(idims,adims) ->
    let pr =
      { (mk_preg_name name) with
        pr_idxs = List.map idims ~f:(fun _ -> All(None,None)) }
    in
    { d_pr = pr; d_aidxs = List.map adims ~f:(fun _ -> All(None,None)) }

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

let read_lvar lmap s idxs0 =
  let rec go v idxs =
    match v, idxs with
    | Vu64(u), [] -> u
    | Varr(vs),i::idxs ->
      go (map_find_exn vs pp_uint64 i) idxs
    | Vu64(_), _::_ ->
      failwith_ "read_lvar: expected array, got u64 in %s[%a]"
        s (pp_list "," pp_uint64) idxs0
    | Varr(_),[] ->
      failwith_ "read_lvar: expected u64, got array (not fully applied) in %s[%a]"
        s (pp_list "," pp_uint64) idxs0
  in
  let v = map_find_exn lmap pp_string s in
  go v idxs0

let read_src_ pmap lmap (s : src_e) =
  match s with
  | Imm pe -> eval_pexpr pmap pe
  | Src({d_pr; d_aidxs=ces}) ->
    let idxs = List.map (d_pr.pr_idxs@ces) ~f:(eval_pexpr pmap) in
    read_lvar lmap d_pr.pr_name idxs

let read_src ms = read_src_ ms.m_pmap ms.m_lmap

let write_lvar v s idxs0 x =
  let rec go v idxs =
    match v, idxs with
    | None,          [] -> Vu64(x)
    | None,          i::idxs ->
      let v' = go None idxs in
      Varr(U64.Map.singleton i v')
    | Some(Vu64(_)), [] -> Vu64(x)
    | Some(Varr(vs)),i::idxs ->
      let v = Map.find vs i in
      let v' = go v idxs in
      Varr(Map.add vs ~key:i ~data:v')
    | Some(Vu64(_)), _::_ ->
      failwith_ "write_lvar: expected array, got u64 in %s[%a]"
        s (pp_list "," pp_uint64) idxs0
    | Some(Varr(_)),[] ->
      failwith_ "write_lvar: expected u64, got array (not fully applied) in %s[%a]"
        s (pp_list "," pp_uint64) idxs0
  in
  go v idxs0

let write_dest_ pmap lmap {d_pr; d_aidxs} x =
  let s    = d_pr.pr_name in
  let v    = Map.find lmap s in
  let idxs = List.map (d_pr.pr_idxs@d_aidxs) ~f:(eval_pexpr pmap) in
  (* F.printf "###: %a\n%!" pp_value v; *)
  let v'   = write_lvar v s idxs x in
  (* F.printf "###: %a\n%!" pp_value v'; *)
  Map.add lmap ~key:s ~data:v'

let write_dest ms d x =
  { ms with m_lmap = write_dest_ ms.m_pmap ms.m_lmap d x }

let read_flag ms s =
  match s with
  | Src{d_pr;d_aidxs=[]} -> map_find_exn ms.m_fmap pp_string d_pr.pr_name
  | Src{d_aidxs=_::_}    -> failwith "expected flag, got array access" 
  | Imm _                -> failwith "expected flag, got immediate"

let write_flag ms {d_pr;d_aidxs} b =
  match d_aidxs with
  | []   -> { ms with m_fmap = Map.add ms.m_fmap ~key:d_pr.pr_name ~data:b }
  | _::_ -> failwith "cannot give array element, flag (in register) expected" 

(* *** Interact with python interpreter
 * ------------------------------------------------------------------------ *)

let py_cmd = "/home/beschmi/bin/sage -python -i"
  (* FIXME: get from SAGE_PYTHON environment variable *)

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
    let ms = write_dest ms z zl in
    write_dest ms h zh

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
    let ms = write_dest ms z zo in
    begin match mcf_out with
    | Some cf_out -> write_flag ms cf_out cfo
    | None        -> ms
    end

  | CMov(CfSet cf_is_set,cf_in)  ->
    let s1 = read_src ms x in
    let s2 = read_src ms y in
    let cf = read_flag ms cf_in in
    let res = if cf = cf_is_set then s2 else s1 in
    write_dest ms z res

  | ThreeOp(O_Imul) ->
    if not (is_Simm y) then
      failwith_ "expected immediate value for %a in IMul" pp_src_e y;
    let x = read_src ms x in
    let y = read_src ms y in
    write_dest ms z (fst (U64.imul_trunc x y))
    
  | ThreeOp(O_And|O_Xor) ->
    failwith "not implemented"

  | Shift(_dir,_mcf_out) ->
    failwith "not implemented"

(* *** Interpret instruction
 * ------------------------------------------------------------------------ *)

let interp_assign pmap ~lhs ~rhs ds0 ss0 =
  let (tenv_lhs,lmap_lhs) = lhs in
  let (tenv_rhs,lmap_rhs) = rhs in
  let ss = List.concat_map ss0 ~f:(fun s -> expand_src  pmap tenv_rhs s) in
  let ds = List.concat_map ds0 ~f:(fun d -> expand_dest pmap tenv_lhs d) in
  let ss_ds =
    try List.zip_exn ss ds
    with Invalid_argument _ ->
      failwith_
        "assignment %a = %a failed, lhs and rhs have different dimensions (%a = %a)"
        (pp_list "," pp_dest) ds0 (pp_list "," pp_src) ss0 (pp_list "," pp_src_e)
        ss (pp_list "," pp_dest_e) ds
  in
  List.fold ss_ds
    ~init:lmap_lhs
    ~f:(fun lmap (s,d) -> write_dest_ pmap lmap d (read_src_ pmap lmap_rhs s))

let rec interp_instr ms0 efun_map instr =
  match instr with

  | Binstr(Comment(_)) ->
    ms0

  | Binstr(Assgn(d,s)) ->
    let lmap =
      interp_assign ms0.m_pmap
        ~lhs:(ms0.m_tenv,ms0.m_lmap) ~rhs:(ms0.m_tenv,ms0.m_lmap)
        [d] [s]
    in
    { ms0 with m_lmap = lmap }

  | Binstr(Op(o,d,(s1,s2))) ->
    interp_op ms0 d s1 s2 o

  | If(ccond,stmt1,stmt2) ->
    if eval_pcond ms0.m_pmap ccond then
      interp_stmt ms0 efun_map stmt1
    else
      interp_stmt ms0 efun_map stmt2

  | For(cv,clb,cub,stmt) ->
    let lb = eval_pexpr ms0.m_pmap clb in
    let ub = eval_pexpr ms0.m_pmap cub in
    assert (U64.compare lb ub < 0);
    assert (U64.compare ub (U64.of_int Int.max_value) < 0); 
    let old_val = Map.find ms0.m_pmap cv in
    let ms = ref ms0 in
    for i = U64.to_int lb to U64.to_int ub - 1 do
      ms := { !ms with m_pmap = Map.add !ms.m_pmap ~key:cv ~data:(U64.of_int i) };
      ms := interp_stmt !ms efun_map stmt;
    done;
    { !ms with
      m_pmap = Map.change !ms.m_pmap cv (fun _ -> old_val) }

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
  let decl_args = List.map func.f_args ~f:dest_of_arg in
  (** compute lmap for callee *)
  let pmap = ms.m_pmap in
  let tenv_caller = ms.m_tenv in
  let lmap_caller = ms.m_lmap in
  let tenv_callee = tenv_of_func func [] in
  let lmap_callee = String.Map.empty in
  let lmap_callee =
    interp_assign pmap
      ~lhs:(tenv_callee,lmap_callee) ~rhs:(tenv_caller,lmap_caller)
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
      ~f:(fun (s,_) -> fsprintf "%a" pp_value_py (Map.find_exn lmap_callee s))
  in    
  let (res,ms) =
    eval_py ms
      (fsprintf "res = %s(%a)\nprint(str(res))\n" py_code
        (pp_list "," pp_string) (s_args@[s_params]))
  in
  let rets = parse_value res in
  let rec flatten v =
    match  v with
    | Varr(m) ->
      List.sort ~cmp:(fun a b -> compare (fst a) (fst b)) (Map.to_alist m)
      |> List.concat_map ~f:(fun i_v -> flatten (snd i_v))
    | Vu64 u -> [u]
  in
  (** store result *)
  let ds = List.concat_map call_rets ~f:(fun d -> expand_dest pmap tenv_caller d) in
  let ss_ds =
    try List.zip_exn (flatten rets) ds
    with Invalid_argument _ ->
      assert false
  in
  let lmap_caller =
    List.fold ss_ds
      ~init:lmap_caller
      ~f:(fun lmap (s,d) -> write_dest_ pmap lmap d s)
  in
  { ms with m_lmap = lmap_caller; }

and interp_call_native ms efun_map func fdef call_rets call_args =
  let decl_args = List.map func.f_args ~f:dest_of_arg in
  let decl_rets = List.map fdef.fd_ret ~f:(fun pr -> Src {d_pr = pr; d_aidxs = []}) in
  (** setup mstate for called function *)
  let pmap = ms.m_pmap in
  let tenv_caller = ms.m_tenv in
  let lmap_caller = ms.m_lmap in
  let fmap_caller = ms.m_fmap in
  let tenv_callee = tenv_of_func func fdef.fd_decls in
  let lmap_callee = String.Map.empty in
  let fmap_callee = String.Map.empty in
  let lmap_callee =
    interp_assign pmap
      ~lhs:(tenv_callee,lmap_callee) ~rhs:(tenv_caller,lmap_caller)
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
      ~lhs:(tenv_caller,lmap_caller) ~rhs:(tenv_callee,lmap_callee)
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
  let lmap = String.Map.of_alist_exn (List.zip_exn (List.map f_args ~f:fst) args) in
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
