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
    let n_pd = List.length pr_dims in
    let n_pi = List.length d.d_pr.pr_idxs in
    let n_ad = List.length arr_dims in
    let n_ai = List.length d.d_aidxs in
    if n_pd <> n_pi then
      failwith_ "register indexes not fully applied (dim %i, args %i" n_pd n_pi;
    if n_ad <> n_ai then
      failwith_ "array indexes not fully applied (dim %i, args %i" n_ad n_ai;
    let dims = pr_dims@arr_dims in
    let idxs = d.d_pr.pr_idxs@d.d_aidxs in
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

(* *** Interpreter state
 * ------------------------------------------------------------------------ *)

type mstate =
  { m_pmap      : u64   String.Map.t (* parameter variables *)
  ; m_lmap      : value String.Map.t (* (function) local variables *)
  ; m_fmap      : bool  String.Map.t (* flags *)
  ; m_mmap      : u64   U64.Map.t    (* memory *)
  ; m_tenv      : ty    String.Map.t (* declarations *)
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
  F.printf "decls: %a\n" (pp_list ", " (pp_pair " -> " pp_string pp_ty))
    (String.Map.to_alist ms.m_tenv)

let read_lvar ms s idxs0 =
  let rec go v idxs =
    match v, idxs with
    | Vu64(u), [] -> u
    | Varr(vs),i::idxs ->
      go (map_find_exn vs pp_uint64 i) idxs
    | Vu64(u), _::_ ->
      failwith_ "read_lvar: expected array, got u64 in %s[%a]" s (pp_list "," pp_uint64) idxs0
    | Varr(vs),[] ->
      failwith_ "read_lvar: expected u64, got array (not fully applied) in %s[%a]"
        s (pp_list "," pp_uint64) idxs0
  in
  let v = map_find_exn ms.m_lmap pp_string s in
  go v idxs0

let read_src ms (s : src_e) =
  match s with
  | Imm pe -> eval_pexpr ms.m_pmap pe
  | Src({d_pr; d_aidxs=ces}) ->
    let idxs = List.map (d_pr.pr_idxs@ces) ~f:(eval_pexpr ms.m_pmap) in
    read_lvar ms d_pr.pr_name idxs

let write_lvar v s idxs0 x =
  let rec go v idxs =
    match v, idxs with
    | None,          [] -> Vu64(x)
    | None,          i::idxs ->
      let v' = go None idxs in
      Varr(U64.Map.singleton i v')
    | Some(Vu64(u)), [] -> Vu64(x)
    | Some(Varr(vs)),i::idxs ->
      let v = Map.find vs i in
      let v' = go v idxs in
      Varr(Map.add vs ~key:i ~data:v')
    | Some(Vu64(u)), _::_ ->
      failwith_ "write_lvar: expected array, got u64 in %s[%a]" s (pp_list "," pp_uint64) idxs0
    | Some(Varr(vs)),[] ->
      failwith_ "write_lvar: expected u64, got array (not fully applied) in %s[%a]"
        s (pp_list "," pp_uint64) idxs0
  in
  go v idxs0

let write_dest ms {d_pr; d_aidxs} x =
  let s    = d_pr.pr_name in
  let v    = Map.find ms.m_lmap s in
  let idxs = List.map (d_pr.pr_idxs@d_aidxs) ~f:(eval_pexpr ms.m_pmap) in
  (* F.printf ">>>: %a\n%!" pp_value v; *)
  let v'   = write_lvar v s idxs x in
  (* F.printf ">>>: %a\n%!" pp_value v'; *)
  { ms with m_lmap = Map.add ms.m_lmap ~key:s ~data:v' }

let read_flag ms s =
  match s with
  | Src{d_pr;d_aidxs=[]} -> map_find_exn ms.m_fmap pp_string d_pr.pr_name
  | Src{d_aidxs=_::_}    -> failwith "cannot give array element, flag (in register) expected" 
  | Imm _                -> failwith "cannot give immediate, flag (in register) expected" 

let write_flag ms {d_pr;d_aidxs} b =
  match d_aidxs with
  | []   -> { ms with m_fmap = Map.add ms.m_fmap ~key:d_pr.pr_name ~data:b }
  | _::_ -> failwith "cannot give array element, flag (in register) expected" 

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
    assert (is_Simm y);
    let x = read_src ms x in
    let y = read_src ms y in
    write_dest ms z (fst (U64.imul_trunc x y))
    
  | ThreeOp(O_And|O_Xor) ->
    failwith "not implemented"

  | Shift(_dir,_mcf_out) ->
    failwith "not implemented"

(* *** Interpret instruction
 * ------------------------------------------------------------------------ *)

let rec interp_instr ms0 efun_map instr =
  match instr with

  | Binstr(Comment(_)) ->
    ms0

  | Binstr(Assgn(d,s)) ->
    let ss = expand_src  ms0.m_pmap ms0.m_tenv s in
    let ds = expand_dest ms0.m_pmap ms0.m_tenv d in
    F.printf ">>>: %a\n%!" (pp_list "," pp_dest_e) ds;
    let ss_ds =
      try List.zip_exn ss ds
      with Invalid_argument _ ->
        failwith (fsprintf
                    "assignment %a failed, lhs and rhs have different dimensions (%a = %a)"
                    pp_instr instr (pp_list "," pp_src_e) ss (pp_list "," pp_dest_e) ds)
    in
    List.fold ss_ds
      ~init:ms0
      ~f:(fun ms (s,d) -> write_dest ms d (read_src ms s))

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
    failwith "call unsupported at the moment"
    (*
    let func = map_find_exn efun_map pp_string fname in
    let fdef = match func.f_def with
      | Some ed -> ed
      | None    -> failwith "Calling undefined function (only declared)"
    in
    let efun_args = List.concat_map efun.f_args ~f:(expand_arg ms0.mpvars) in
    let expand_dest d =
      let aidxs =
        List.filter_map d.d_aidxs
          ~f:(function Get i -> Some i | All(_,_) -> assert false)
      in
      List.map (expand_pr ms0 d.d_pr)
        ~f:(fun pr -> { d_pr = pr; d_aidxs = aidxs })
    in
    let expand_src s = match s with
      | Imm(_) -> assert false
      | Src(d) -> expand_dest d
    in
    
    let given_rets = List.concat_map rets ~f:expand_dest in
    let given_args = List.concat_map args ~f:expand_src in
    
    let mregs_o = ms0.mlvars in
    let mflags_o = ms0.mflags in
    let mdecls_o = ms0.mdecls in
    let mstack_last_o = ms0.mstack_last in

    let iname_of_preg = indexed_name_of_preg in
    let get_arg ({d_pr; d_aidxs} as d) =
      match d_aidxs with
      | [] -> read_src ms0 (Src(d))
      | ces ->
        let addr_r = read_src ms0 (Src({d_pr; d_aidxs=[]})) in
        let offs = get_offset ms0 d_pr ces in
        let addr = get_addr addr_r offs in
        addr
    in
    let arg_alist =
      list_map2_exn given_args efun_args
        ~f:(fun dest efun_arg ->
                (efun_arg,
                 get_arg dest))
       ~err:(fun l_exp l_got -> 
               failwith (fsprintf "expected %i, got %i in arg list" l_got l_exp))
    in
    let ms =
      { ms0 with
        mdecls = tenv_of_func efun edef;
        mflags = String.Map.empty;
        mregs  = assert false (* IndexedName.Map.of_alist_exn arg_alist; *)
      }
    in
    let efun_rets =
      List.concat_map fdef.fd_ret ~f:(fun pr -> expand_pr ms pr)
    in
    (* let ms = setup_stack ms edef in *)
    let ms = interp_stmt ms efun_map fdef.fd_body in
    let mregs =
      assert false (*
      try
        List.fold2_exn given_rets efun_rets
          ~f:(fun acc dest efun_pr ->
                assert (dest.d_aidxs=[]);
                Map.add acc ~key:(iname_of_preg ms.mcvars dest.d_pr)
                  ~data:(map_find_exn ms.mregs pp_indexed_name
                         (iname_of_preg ms.mcvars efun_pr)))
          ~init:mregs_o
      with Invalid_argument _ ->
        failwith "return value mismatch"
      *)
    in
    { ms with
      m_tenv  = m_tenv_o;
      m_fmap  = m_fmap_o;
      m_lmap  = m_lmap_o;
    }
    *)

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
  let fdef = Option.value_exn func.f_def in
  let stmt = fdef.fd_body in

  let f_args = func.f_args in
  if List.length f_args <> List.length args then
    failwith_ "interp_string: wrong number of arguments given (got %i, exp. %i)"
      (List.length args) (List.length f_args);
  (* FIXME: typecheck that given arguments are ok *)
  (* FIXME: typecheck parameters *)
  let lmap = String.Map.of_alist_exn (List.zip_exn (List.map f_args ~f:fst) args) in
  let fmap = String.Map.of_alist_exn [] in
  let tenv = tenv_of_func func fdef in
  let ms =
    { m_lmap = lmap;
      m_pmap = pmap;
      m_fmap = fmap;
      m_mmap = mmap;
      m_tenv = tenv;
    }
  in
  (* let ms = setup_stack ms edef in *)
 
  print_mstate ms;
  let ms = interp_stmt ms func_map stmt in
  print_endline "###################";
  print_mstate ms;
  print_endline "###################";
  modul
