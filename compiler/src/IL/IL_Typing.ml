(* * Typing of IL *)

(* ** Imports *)
open IL_Lang
open IL_Utils
open Util
open Arith
open Core_kernel.Std

module P = ParserUtil

(* ** Check type information and propagate to pregs
 * ------------------------------------------------------------------------ *)

(* *** Typing environment
 * ------------------------------------------------------------------------ *)

exception TypeError of P.loc * string

type penv = ty   String.Map.t
type fenv = func String.Map.t
type tenv = ty   String.Map.t

type env = {
  e_penv : penv;
  e_fenv : fenv;
  e_tenv : tenv;
}

let tenv_of_func func (fdef : fundef) =
  String.Map.of_alist_exn (func.f_args @ fdef.fd_decls)

let type_error pr s =
 raise (TypeError (pr.pr_loc,s))

(* *** Compute types of registers taking (array) indexes into account
 * ------------------------------------------------------------------------ *)

let get_dim (dim : pexpr) idx =
  match idx with  (* FIXME: check [lb..ub] <= [0..dim]? *)
  | Get _          -> None
  | All(lb_o,ub_o) ->
    let zero = Pconst U64.zero in
    let lb = get_opt zero lb_o in
    let ub = get_opt dim ub_o in
    if equal_pexpr lb zero
    then Some(ub)
    else Some(Pbinop(Pminus,ub,lb))

(** [type_pr_app_g pr ty] takes a pseudo-register pr<ies> and the
    type of pr and returns the type of pr<ies>.
    Example: for pr<3,0..n> with pr : u64<5,n>[n], the result is u64<n>[n] *)
let type_pr_app pr ty =
  match ty with
  | Bool ->
    if pr.pr_idxs<>[] then
      type_error pr "register has type bool, invalid usage";
    Bool
  | U64(idx_dims,arr_dims) ->
    let new_idx_dims =
      list_map2_exn idx_dims pr.pr_idxs ~f:get_dim
        ~err:(fun l_exp l_got ->
            type_error pr
              (fsprintf "indexed register %s must be fully applied (got %i, expected %i)"
                 pr.pr_name l_got l_exp))
      |> List.filter_opt
    in
    U64(new_idx_dims,arr_dims)

(** Same as [ty_pr_app] except that it looks up the type from [tenv] *)
let type_pr (tenv : tenv) pr =
  type_pr_app pr (map_find_exn ~err:(type_error pr) tenv pp_string pr.pr_name)

(** Same as [type_pr] except that it asserts that type is equal to [ty_exp] *)
let typecheck_pr (tenv : tenv) pr ty_exp =
  let ty = type_pr tenv pr in
  if not (equal_ty ty ty_exp) then
    type_error pr (fsprintf "type mismatch (got %a, expected %a)" pp_ty ty pp_ty ty_exp)

(** Takes destination pr<iidxs>[aidxs] and computes its type by looking up
    the type of [pr] in [tenv] and accounting for the applications.
    Example: pr<1,..>[3,..] where pr : u64<5,n1>[5,n2,n3], result u64<n1,n2>[n3].
             Note that it's partially applied, hence all elements are arrays. *)
let type_dest (tenv : tenv) {d_pr; d_aidxs} =
  match type_pr tenv d_pr with
  | Bool ->
    if d_aidxs<>[] then
      type_error d_pr ("register has type bool, invalid usage");
    Bool

  | U64(_,dims) as ty when List.length d_aidxs > List.length dims ->
    type_error d_pr (fsprintf "too many array indexes given, has type %a" pp_ty ty)

  | U64(tidxs,adims) as ty ->
    let l_aidxs = List.length d_aidxs in
    let dims_indexed  = List.take adims l_aidxs in
    let dims_noexpand = List.drop adims l_aidxs in
    let dims_expand =
      list_map2_exn dims_indexed d_aidxs ~f:get_dim
        ~err:(fun l_exp l_got -> 
                type_error d_pr
                (fsprintf "indexed register %a:%a must be fully applied (got %i, expected %i)"
                   pp_preg d_pr pp_ty ty l_got l_exp))
        |> List.filter_opt
    in
    U64(tidxs@dims_expand,dims_noexpand)

(** Same as [type_dest] except that it assert that type is equal to [ty_exp] *)
let typecheck_dest (env : env) dest ty_exp =
  let ty = type_dest env.e_tenv dest in
  if not (equal_ty ty ty_exp) then
    type_error dest.d_pr (fsprintf "type mismatch for %a (got %a, expected %a)"
                            pp_dest dest pp_ty ty pp_ty ty_exp)

(** Takes source and computes its type (see [type_dest]) *)
let type_src (env : env) s =
  match s with
  | Imm(_) -> U64([],[])
  | Src(d) -> type_dest env.e_tenv d

(** Same as [type_dest] except that it asserts that type is equal to [ty_exp] *)
let typecheck_src (env : env) s ty_exp =
  match s with
  | Imm(_) -> if not (equal_ty ty_exp (U64([],[]))) then assert false
  | Src(d) -> typecheck_dest env d ty_exp

(* *** Check types for assignments, destinations, and sources
 * ------------------------------------------------------------------------ *)

type base_type = T_U64 | T_Bool

(** Ensures that the source and destination for assignments are compatible *)
let typecheck_assgn (env : env) d s =
  let ty_s = type_src  env s in
  let ty_d = type_dest env.e_tenv d in 
  match ty_s, ty_d with
  | U64(tidxs_s,dims_s), U64(tidxs_d,dims_d)
    (* we allow xp[..] = yp<..> if dims match *)
    when equal_ty (U64(tidxs_s@dims_s,[])) (U64(tidxs_d@dims_d,[])) ->
    ()
  | Bool, Bool ->
    type_error d.d_pr (fsprintf "incompatible types for assignment %a (cannot assign flags)"
                         pp_instr (Binstr(Assgn(d,s))));
  | U64(tidxs_s,[]), U64(tidxs_d,[_s])
    (* FIXME: generalize, assign address to array type *)
    when equal_ty (U64(tidxs_s,[])) (U64(tidxs_d,[])) ->
    ()
  | _ -> 
    if not (equal_ty ty_s ty_d) then
      type_error d.d_pr (fsprintf "incompatible types for assignment %a (lhs %a, rhs %a)"
                           pp_instr (Binstr(Assgn(d,s))) pp_ty ty_d pp_ty ty_s);
    ()

(** Checks that the base type of the given destination is equal to [t] *)
let type_dest_eq (env : env) {d_pr; d_aidxs} (t : base_type) =
  match map_find_exn ~err:(type_error d_pr) env.e_tenv pp_string d_pr.pr_name with
  | Bool     when t=T_U64  -> failwith "got bool, expected u64"
  | Bool                   -> ()
  | U64(_,_) when t=T_Bool -> failwith "got u64<_>[_], expected bool"
  | U64(iidxs,aidxs) as ty ->
    if (   List.length d_pr.pr_idxs<>List.length iidxs
        || List.length d_aidxs<>List.length aidxs) then
      type_error d_pr (fsprintf "expected type u64, register name of type %a not fully applied"
                         pp_ty ty)

(** Checks that the base type of the given source is equal to [t] *)
let type_src_eq (env : env) src (t : base_type) =
  match src, t with
  | Imm _,  T_Bool -> failwith "got u64, expected bool"
  | Imm _,  T_U64  -> ()
  | Src(d), t      -> type_dest_eq env d t

(* *** Check types for ops, instructions, statements, and functions
 * ------------------------------------------------------------------------ *)

(** typecheck operators *)
let typecheck_op (env : env) op z x y =
  let type_src_eq  = type_src_eq  env in
  let type_dest_eq = type_dest_eq env in
  match op with
  
  | Umul(h) ->
    type_src_eq  x T_U64;
    type_src_eq  y T_U64;
    type_dest_eq z T_U64;
    type_dest_eq h T_U64

  | Carry(_,mcf_out,mcf_in) ->
    type_src_eq  x T_U64;
    type_src_eq  y T_U64;
    type_dest_eq z T_U64;
    Option.iter ~f:(fun s -> type_src_eq  s T_Bool) mcf_in;
    Option.iter ~f:(fun d -> type_dest_eq d T_Bool) mcf_out

  | CMov(_,cf_in) ->
    type_src_eq  x     T_U64;
    type_src_eq  y     T_U64;
    type_src_eq  cf_in T_Bool;
    type_dest_eq z     T_U64
      
  | ThreeOp(_) ->
    type_src_eq  x T_U64;
    type_src_eq  y T_U64;
    type_dest_eq z T_U64
    
  | Shift(_dir,mcf_out) ->
    type_src_eq  x T_U64;
    type_src_eq  y T_U64;
    type_dest_eq z T_U64;
    Option.iter ~f:(fun s -> type_dest_eq  s T_Bool) mcf_out

(** typecheck instructions and statements *)
let rec typecheck_instr (env : env) instr =
  let tc_stmt  = typecheck_stmt  env in
  let tc_op    = typecheck_op    env in
  let tc_assgn = typecheck_assgn env in
  match instr with
  | Binstr(Comment _)             -> ()
  | Binstr(Op(op,d,(s1,s2)))      -> tc_op op d s1 s2
  | Binstr(Assgn(d,s))            -> tc_assgn d s
  | If(_,stmt1,stmt2)             -> tc_stmt stmt1; tc_stmt stmt2
  | Binstr(Call(fname,rets,args)) ->
    let cfun = map_find_exn env.e_fenv pp_string fname in
    let tc_src s (_,ty_expected) = typecheck_src env s ty_expected in
    let tc_dest d ty_expected = typecheck_dest env d ty_expected in
    list_iter2_exn args cfun.f_args ~f:tc_src
      ~err:(fun n_g n_e ->
              failwith_ "wrong number of arguments (got %i, exp. %i)" n_g n_e);
    list_iter2_exn rets cfun.f_ret_ty ~f:tc_dest
      ~err:(fun n_g n_e ->
              failwith_ "wrong number of l-values (got %i, exp. %i)" n_g n_e)
  | For(pv,_,_,stmt)              ->
    let env = { env with e_penv = Map.add env.e_penv ~key:pv ~data:(U64([],[])) } in
    typecheck_stmt env stmt
      
and typecheck_stmt (env : env) stmt =
  List.iter ~f:(typecheck_instr env) stmt

(** typecheck return value *)
let typecheck_ret (env : env) ret_ty ret =
  List.iter2_exn ret ret_ty ~f:(typecheck_pr env.e_tenv)

(** typecheck the given function *)
let typecheck_func (penv : penv) (fenv : fenv) func =
  match func.f_def with
  | None      -> ()
  | Some fdef ->
    let tenv = String.Map.of_alist_exn
                 (  (Map.to_alist (tenv_of_func func fdef))
                  @ (Map.to_alist penv))
    in
    let env  = { e_penv = penv; e_fenv = fenv; e_tenv = tenv } in
    typecheck_stmt env fdef.fd_body;
    typecheck_ret env func.f_ret_ty fdef.fd_ret

(** typecheck all functions in module *)
let typecheck_modul modul =
  let funcs = modul.m_funcs in
  let fenv = String.Map.of_alist_exn (List.map funcs ~f:(fun func -> (func.f_name, func))) in
  let penv = String.Map.of_alist_exn modul.m_params in
  let pvars = pvars_modul pvars_get_or_range modul in
  Set.iter pvars
    ~f:(fun pv -> if not (Map.mem penv pv) then
                    raise (TypeError(P.dummy_loc,fsprintf "parameter %s undefined" pv))); 
  List.iter funcs ~f:(typecheck_func penv fenv)
