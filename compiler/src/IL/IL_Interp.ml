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

let eval_pbinop = function
  | Pplus  -> U64.add
  | Pmult  -> U64.mul
  | Pminus -> U64.sub

let eval_pexpr cvar_map ce =
  let rec go = function
    | Pbinop(o,ie1,ie2) -> eval_pbinop o (go ie1) (go ie2)
    | Pconst(c)         -> c
    | Pvar(s) ->
      begin match Map.find cvar_map s with
      | Some x -> x
      | None   -> failwith ("eval_cexpr: parameter "^s^" undefined")
      end
  in
  go ce

let eval_pcondop = function
  | Peq      -> U64.equal
  | Pineq    -> fun x y -> not (U64.equal x y)
  | Pless    -> fun x y -> U64.compare x y < 0
  | Pgreater -> fun x y -> U64.compare x y > 0
  | Pleq     -> fun x y -> U64.compare x y <= 0
  | Pgeq     -> fun x y -> U64.compare x y >= 0

let eval_ccond cvar_map cc =
  let rec go = function
    | Ptrue              -> true
    | Pnot(ic)           -> not (go ic)
    | Pand(cc1,cc2)      -> (go cc1) && (go cc2)
    | Pcond(cco,ce1,ce2) ->
      eval_pcondop cco (eval_pexpr cvar_map ce1) (eval_pexpr cvar_map ce2)
  in
  go cc

let bounded_idx_lists bound_list =
  let go (idx_lists : u64 list list) (bound : u64) : u64 list list =
    List.concat_map idx_lists
      ~f:(fun is ->
          let indexes = list_from_to ~first:U64.zero ~last:bound in
          List.map indexes ~f:(fun i -> is@[i]))
  in
  List.fold ~f:go ~init:[[]] bound_list
 
let expand_arg cvar_map (s,ty) =
  match ty with
  | Bool -> failwith "Boolean arguments not allowed"
  | U64(idims,_adims) ->
    let idx_bounds = List.map ~f:(eval_pexpr cvar_map) idims in
    let idx_lists = bounded_idx_lists idx_bounds in
    List.map idx_lists ~f:(fun idx_list -> (s,idx_list))

(* ** Interpreter
 * ------------------------------------------------------------------------ *)

let is_Simm = function Imm _ -> true | _ -> false

type mstate =
  { mcvars      : u64  String.Map.t
  ; mregs       : u64  IndexedName.Map.t
  ; mflags      : bool String.Map.t
  ; mmem        : u64  U64.Map.t
  ; mdecls      : ty   String.Map.t
  ; mstack_last : u64
  }

let print_mstate ms =
  F.printf "cvars: %a\n" (pp_list ", " (pp_pair " -> " pp_string pp_uint64))
    (String.Map.to_alist ms.mcvars);
  F.printf "regs: %a\n" (pp_list ", " (pp_pair " -> " pp_indexed_name pp_uint64))
    (IndexedName.Map.to_alist ms.mregs);
  F.printf "flags: %a\n" (pp_list ", " (pp_pair " -> " pp_string pp_bool))
    (String.Map.to_alist ms.mflags);
  F.printf "mem: %a\n" (pp_list ", " (pp_pair " -> " pp_uint64 pp_uint64))
    (U64.Map.to_alist ms.mmem);
  F.printf "stack_last: %a\n" pp_uint64 ms.mstack_last;
  F.printf "decls: %a\n" (pp_list ", " (pp_pair " -> " pp_string pp_ty))
    (String.Map.to_alist ms.mdecls)

let setup_stack ms efun =
  let u8 = (U64.of_int 8) in
  List.concat_map efun.ef_decls
    ~f:(fun (s,ty) -> match ty with
        | U64(_,[pe]) ->
          let t = eval_pexpr ms.mcvars pe in
          List.map (expand_arg ms.mcvars (s,ty)) ~f:(fun iname -> (iname,t))
        | _ -> [])
  |> List.fold ~init:ms
    ~f:(fun ms (iname,d) ->
        { ms with
          mstack_last = U64.add ms.mstack_last (U64.mul d u8);
          mregs = Map.add ms.mregs ~key:iname ~data:ms.mstack_last
        }) 

let expand_dest ms d =
  match type_dest ms.mdecls d with
  | Bool -> failwith "Boolean arguments not allowed"
  | U64(dims_expand,_dims_remaining) ->
    let eval = eval_pexpr ms.mcvars in
    let idx_bounds = List.map ~f:eval dims_expand in
    let idx_lists = bounded_idx_lists idx_bounds in
    let rec go iidxs_o aidxs_o iidxs aidxs idx_list =
      match iidxs_o, aidxs_o, idx_list with
      | [],[],[] ->
        { d_pr = { d.d_pr with pr_idxs = List.rev iidxs}; d_aidxs = List.rev aidxs}
      | (Get pe)::iidxs_o,_,_ ->
        go iidxs_o aidxs_o (pe::iidxs) aidxs idx_list
      | [],(Get pe)::aidxs_o,_ ->
        go iidxs_o aidxs_o iidxs (pe::aidxs) idx_list
      | All::iidxs_o,_,i::idx_list ->
        go iidxs_o aidxs_o (Pconst(i)::iidxs) aidxs idx_list
      | [],All::aidxs_o,i::idx_list ->
        go iidxs_o aidxs_o iidxs (Pconst(i)::aidxs) idx_list
      | [],All::_,[]
      | All::_,_,[]
      | [],[],_::_ ->
        assert false
    in
    List.map idx_lists ~f:(go d.d_pr.pr_idxs d.d_aidxs [] [])

let expand_src ms = function
  | Imm(_) as s -> [s]
  | Src(d)      -> List.map (expand_dest ms d) ~f:(fun d -> Src(d))

let expand_pr ms pr =
  match type_pr ms.mdecls pr with
  | Bool -> failwith "Boolean arguments not allowed"
  | U64(dims_expand,_dims_remaining) ->
    let eval = eval_pexpr ms.mcvars in
    let idx_bounds = List.map ~f:eval dims_expand in
    let idx_lists = bounded_idx_lists idx_bounds in
    let rec go iidxs_o iidxs idx_list =
      match iidxs_o, idx_list with
      | [],[] ->
        { pr with pr_idxs = List.rev iidxs}
      | (Get pe)::iidxs_o,_ ->
        go iidxs_o (pe::iidxs) idx_list
      | All::iidxs_o,i::idx_list ->
        go iidxs_o (Pconst(i)::iidxs) idx_list
      | All::_,[]
      | [],_::_ ->
        assert false
    in
    List.map idx_lists ~f:(go pr.pr_idxs [])

let get_addr addr_r offset =
  let c8 = U64.of_int 8 in
  U64.add addr_r (U64.mul c8 offset)

let indexed_name_of_preg cvar_map (pr : preg_e) =
  (pr.pr_name, List.map pr.pr_idxs ~f:(eval_pexpr cvar_map))

let rec read_src ms (s : src_e) =
  match s with

  | Imm i -> i

  | Src({d_pr; d_aidxs=[]}) ->
    let iname = indexed_name_of_preg ms.mcvars d_pr in
    (* F.printf "read_reg: %a\n%!" pp_indexed_name iname; *)
    map_find_exn ms.mregs pp_indexed_name iname

  | Src({d_pr; d_aidxs=[ce]}) ->
    let addr_r = read_src ms (Src({d_pr; d_aidxs=[]})) in
    let offs = eval_pexpr ms.mcvars ce in
    let addr = get_addr addr_r offs in
    (* F.printf "read_mem: %a from %a\n%!" pp_uint64 addr pp_src_e s; *)
    map_find_exn ms.mmem pp_uint64 addr

  | Src({d_aidxs=_::_::_}) ->
    failwith "array access for multiple dimensions not supported yet" 

let write_dest ms {d_pr; d_aidxs} x =
  match d_aidxs with

  | [] ->
    let iname = indexed_name_of_preg ms.mcvars d_pr in
    (* F.printf "write_reg: %a -> %a\n" pp_indexed_name iname pp_uint64 x; *)
    { ms with mregs = Map.add ms.mregs ~key:iname ~data:x }

  | [ce] ->
    let addr_r = read_src ms (Src{d_pr;d_aidxs=[]}) in
    let offs = eval_pexpr ms.mcvars ce in
    let addr = get_addr addr_r offs in
    (* F.printf "write_mem: %a -> %a via %a\n%!" pp_uint64 addr pp_uint64 x pp_dest_e d; *)
    { ms with mmem = Map.add ms.mmem ~key:addr ~data:x }

  | _::_::_ ->
    failwith "array access for multiple dimensions not supported yet" 

let read_flag ms s =
  match s with
  | Src{d_pr;d_aidxs=[]} -> map_find_exn ms.mflags pp_string d_pr.pr_name
  | Src{d_aidxs=_::_}    -> failwith "cannot give array element, flag (in register) expected" 
  | Imm _                -> failwith "cannot give immediate, flag (in register) expected" 

let write_flag ms {d_pr;d_aidxs} b =
  match d_aidxs with
  | []   -> { ms with mflags = Map.add ms.mflags ~key:d_pr.pr_name ~data:b }
  | _::_ -> failwith "cannot give array element, flag (in register) expected" 

let interp_op (ms : mstate) z x y = function

  | UMul(h) ->
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

  | ThreeOp(O_IMul) ->
    assert (is_Simm y);
    let x = read_src ms x in
    let y = read_src ms y in
    write_dest ms z (fst (U64.imul_trunc x y))
    
  | ThreeOp(O_And|O_Xor) ->
    failwith "not implemented"

  | Shift(_dir,_mcf_out) ->
    failwith "not implemented"

let rec interp_instr ms0 efun_map instr =
  match instr with

  | Binstr(Comment(_)) ->
    ms0

  | Binstr(Assgn(d,s)) ->
    let ss = expand_src  ms0 s in
    let ds = expand_dest ms0 d in
    let xs = List.map ~f:(read_src ms0) ss in
    let xs_ds =
      try List.zip_exn xs ds
      with Invalid_argument _ ->
        failwith (fsprintf "assignment %a failed, lhs and rhs have different dimensions"
                    pp_instr instr)
    in
    List.fold xs_ds
      ~init:ms0
      ~f:(fun ms (x,d) -> write_dest ms d x)


  | Binstr(Op(o,d,(s1,s2))) ->
    interp_op ms0 d s1 s2 o

  | If(ccond,stmt1,stmt2) ->
    if eval_ccond ms0.mcvars ccond then
      interp_stmt ms0 efun_map stmt1
    else
      interp_stmt ms0 efun_map stmt2

  | For(cv,clb,cub,stmt) ->
    let lb = eval_pexpr ms0.mcvars clb in
    let ub = eval_pexpr ms0.mcvars cub in
    assert (U64.compare lb ub < 0);
    assert (U64.compare ub (U64.of_int Int.max_value) < 0); 
    let old_val = Map.find ms0.mcvars cv in
    let ms = ref ms0 in
    for i = U64.to_int lb to U64.to_int ub - 1 do
      ms := { !ms with mcvars = Map.add !ms.mcvars ~key:cv ~data:(U64.of_int i) };
      ms := interp_stmt !ms efun_map stmt;
    done;
    { !ms with
      mcvars = Map.change !ms.mcvars cv (fun _ -> old_val) }

  | Call(fname,rets,args) ->
    let efun      = map_find_exn efun_map pp_string fname in
    let efun_args = List.concat_map efun.ef_args ~f:(expand_arg ms0.mcvars) in
    
    let given_rets = List.concat_map rets ~f:(expand_pr ms0) in
    let given_args = List.concat_map args ~f:(expand_pr ms0) in
    
    let mregs_o = ms0.mregs in
    let mflags_o = ms0.mflags in
    let mdecls_o = ms0.mdecls in
    let mstack_last_o = ms0.mstack_last in

    let iname_of_preg = indexed_name_of_preg in
    let arg_alist =
      List.map2_exn given_args efun_args
        ~f:(fun pr efun_arg ->
                (efun_arg,
                 map_find_exn mregs_o pp_indexed_name (iname_of_preg ms0.mcvars pr)))
    in
    let ms =
      { ms0 with
        mdecls = ty_env_of_efun efun;
        mflags = String.Map.empty;
        mregs  = IndexedName.Map.of_alist_exn arg_alist;
      }
    in
    let efun_rets = List.concat_map efun.ef_ret ~f:(fun (pr,_) -> expand_pr ms pr) in
    let ms = setup_stack ms efun in
    let ms = interp_stmt ms efun_map efun.ef_body in
    let mregs =
      List.fold2_exn given_rets efun_rets
        ~f:(fun acc pr efun_pr ->
              Map.add acc ~key:(iname_of_preg ms.mcvars pr)
                ~data:(map_find_exn ms.mregs pp_indexed_name (iname_of_preg ms.mcvars efun_pr)))
        ~init:mregs_o
    in
    { ms with
      mdecls = mdecls_o;
      mflags = mflags_o;
      mregs  = mregs;
      mstack_last = mstack_last_o;
    }

and interp_stmt (ms0 : mstate) efun_map stmt =
  List.fold stmt
    ~f:(fun ms i -> interp_instr ms efun_map i)
    ~init:ms0

let interp_string fname mem cvar_map args ef_name string =
  let open ParserUtil in
  let efuns = parse ~parse:IL_Parse.efuns fname string in
  typecheck_efuns efuns;
  let efun_map = String.Map.of_alist_exn (List.map ~f:(fun ef -> (ef.ef_name,ef)) efuns) in
  let efun = map_find_exn efun_map pp_string ef_name in
  let stmt = efun.ef_body in

  let arg_regs = List.concat_map ~f:(expand_arg cvar_map) efun.ef_args in
  let regs = IndexedName.Map.of_alist_exn (List.zip_exn arg_regs args) in
  let flags = String.Map.of_alist_exn [] in
  let decls = ty_env_of_efun efun in
  let ms =
    { mregs = regs;
      mcvars = cvar_map;
      mflags = flags;
      mmem = mem;
      mdecls = decls;
      mstack_last = U64.of_int 100000;
    }
  in
  let ms = setup_stack ms efun in
 
  (* print_mstate ms; *)
  interp_stmt ms efun_map stmt
