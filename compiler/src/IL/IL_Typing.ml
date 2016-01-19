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

let tenv_of_func func decls =
  String.Map.of_alist_exn (List.map ~f:(fun (_,m,t) -> (m,t)) (func.f_args@decls))

let type_error d s =
 raise (TypeError (d.d_loc,s))

(* *** Compute types of registers taking (array) indexes into account
 * ------------------------------------------------------------------------ *)

let equiv_ty ty1 ty2 =
  match ty1, ty2 with
  | Bool, Bool                   -> true
  | U64(None)      , U64(None)   -> true
  | U64(Some(d1)), U64(Some(d2)) -> equal_pexpr d1 d2
  | _,               _           -> false

let get_dim (dim : pexpr) (lb_o,ub_o) =
  let zero = Pconst U64.zero in
  let lb = get_opt zero lb_o in
  let ub = get_opt dim ub_o in
  if equal_pexpr lb zero
  then ub
  else Pbinop(Pminus,ub,lb)

(** [type_dest_app pr ty] takes a pseudo-register pr<ies> and the
    type of pr and returns the type of pr<ies>.
    Example: for pr<3,0..n> with pr : u64<5,n>[n], the result is u64<n>[n] *)
let type_dest_app d ty =
  match ty with
  | Bool ->
    if Option.is_some d.d_oidx then
      type_error d "register has type bool, invalid usage";
    Bool
  | U64(odim) as ty ->
    begin match odim, d.d_oidx with
    | _       , None    -> ty
    | Some (_), Some(_) -> U64(None)
    | None    , Some _  ->
      type_error d
        (fsprintf "cannot perform array indexing on scalar %s" d.d_name)
    end

(** Same as [type_dest_app] except that it looks up the type from [tenv] *)
let type_dest (tenv : tenv) d =
  type_dest_app d (map_find_exn ~err:(type_error d) tenv pp_string d.d_name)

(** Same as [type_dest] except that it asserts that type is equal to [ty_exp] *)
let typecheck_dest (tenv : tenv) d ty_exp =
  let ty = type_dest tenv d in
  if not (equiv_ty ty ty_exp) then
    type_error d (fsprintf "type mismatch (got %a, expected %a)" pp_ty ty pp_ty ty_exp)

(** Takes source and computes its type (see [type_dest]) *)
let type_src (env : env) = function
  | Imm(_) -> U64(None)
  | Src(d) -> type_dest env.e_tenv d

(** Same as [type_dest] except that it asserts that type is equal to [ty_exp] *)
let typecheck_src (env : env) s ty_exp =
  match s with
  | Imm(_) -> if not (equal_ty ty_exp (U64(None))) then assert false
  | Src(d) -> typecheck_dest env.e_tenv d ty_exp

(* *** Check types for assignments, destinations, and sources
 * ------------------------------------------------------------------------ *)

type base_type = T_U64 | T_Bool

(** Ensures that the source and destination for assignments are compatible *)
let typecheck_assgn (env : env) d s loc =
  let mk_bi bi = { l_loc = loc; l_val=Binstr(bi) } in
  let ty_s = type_src  env s in
  let ty_d = type_dest env.e_tenv d in
  match ty_s, ty_d with
  | U64(odim1), U64(odim2) ->
    if not (is_some odim1 = is_some odim2) then
      type_error d (fsprintf "incompatible types for assignment %a (lhs %a, rhs %a)"
                           pp_instr (mk_bi (Assgn(d,s,Mv))) pp_ty ty_d pp_ty ty_s)

  | Bool, Bool ->
    type_error d (fsprintf "incompatible types for assignment %a (cannot assign flags)"
                    pp_instr (mk_bi (Assgn(d,s,Mv))))
  | _, _ ->
    type_error d (fsprintf "incompatible types for assignment %a (lhs %a, rhs %a)"
                    pp_instr (mk_bi (Assgn(d,s,Mv))) pp_ty ty_d pp_ty ty_s)



(** Checks that the base type of the given destination [t] is equal to [t] *)
let type_dest_eq (env : env) d (t : base_type) =
  match map_find_exn ~err:(type_error d) env.e_tenv pp_string d.d_name with
  | Bool   when t=T_U64  -> failwith "got bool, expected u64"
  | Bool                 -> ()
  | U64(_) when t=T_Bool -> failwith "got u64<_>/[_], expected bool"
  | U64(odim) as ty ->
    if (Option.is_some odim <> Option.is_some d.d_oidx) then
      type_error d (fsprintf "expected type u64, register name of type %a not fully applied"
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
    Option.iter ~f:(fun s -> type_dest_eq s T_Bool) mcf_out

(** typecheck instructions and statements *)
let rec typecheck_instr (env : env) linstr =
  let tc_stmt  = typecheck_stmt  env in
  let tc_op    = typecheck_op    env in
  let tc_assgn = typecheck_assgn env in
  match linstr.l_val with
  | Binstr(Comment _)             -> ()
  | Binstr(Op(op,d,(s1,s2)))      -> tc_op op d s1 s2
  | Binstr(Assgn(d,s,_))          -> tc_assgn d s linstr.l_loc
  | If(_,stmt1,stmt2)             -> tc_stmt stmt1; tc_stmt stmt2
  | Binstr(Load(d,s,_pe))         -> type_src_eq  env s T_U64; type_dest_eq env d T_U64
  | Binstr(Store(s1,_pe,s2))      -> type_src_eq env s1 T_U64; type_src_eq env s2 T_U64
  | Binstr(Call(fname,rets,args)) ->
    let cfun = map_find_exn env.e_fenv pp_string fname in
    let tc_src s (_,_,ty_expected) = typecheck_src env s ty_expected in
    let tc_dest d (_,ty_expected) = typecheck_dest env.e_tenv d ty_expected in
    list_iter2_exn args cfun.f_args ~f:tc_src
      ~err:(fun n_g n_e ->
              failwith_ "wrong number of arguments (got %i, exp. %i)" n_g n_e);
    list_iter2_exn rets cfun.f_ret_ty ~f:tc_dest
      ~err:(fun n_g n_e ->
              failwith_ "wrong number of l-values (got %i, exp. %i)" n_g n_e)
  | For(_,pv,_,_,stmt) ->
    type_dest_eq env { d_loc = linstr.l_loc; d_name = pv; d_oidx = None} T_U64;
    typecheck_stmt env stmt

and typecheck_stmt (env : env) stmt =
  List.iter ~f:(typecheck_instr env) stmt

(** typecheck return value *)
let typecheck_ret (env : env) ret_ty ret =
  List.iter2_exn ret ret_ty
    ~f:(fun name ty -> typecheck_dest env.e_tenv (mk_dest_name name) ty)

(** typecheck the given function *)
let typecheck_func (penv : penv) (fenv : fenv) func =
  match func.f_def with
  | Undef | Py _ -> ()
  | Def fdef ->
    let tenv = String.Map.of_alist_exn
                 (  (Map.to_alist (tenv_of_func func fdef.fd_decls))
                  @ (Map.to_alist penv))
    in
    let env  = { e_penv = penv; e_fenv = fenv; e_tenv = tenv } in
    typecheck_stmt env fdef.fd_body;
    typecheck_ret env (List.map ~f:snd func.f_ret_ty) fdef.fd_ret

(** typecheck all functions in module *)
let typecheck_modul modul =
  let funcs = modul.m_funcs in
  let fenv = String.Map.of_alist_exn (List.map funcs ~f:(fun func -> (func.f_name, func))) in
  let penv = String.Map.of_alist_exn modul.m_params in
  let params = params_modul modul in
  Set.iter params
    ~f:(fun pv -> if not (Map.mem penv pv) then
                    raise (TypeError(P.dummy_loc,fsprintf "parameter %s undefined" pv)));
  List.iter funcs ~f:(typecheck_func penv fenv)
