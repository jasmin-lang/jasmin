(* * Typing of IL *)

(* ** Imports *)
open IL_Lang
open IL_Pprint
open IL_Utils
open IL_Misc
open Util
open Arith
open Core_kernel.Std

module P = ParserUtil
module L = ParserUtil.Lexing

(* ** Check type information and propagate to pregs
 * ------------------------------------------------------------------------ *)

(* *** Typing environment
 * ------------------------------------------------------------------------ *)

type penv = unit Param.Table.t

type 'info fenv = 'info func Fname.Map.t

type 'info env = {
  e_penv : penv;
  e_fenv : 'info fenv;
}

let type_error_ l fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      failloc l s)
    fbuf fmt

let type_error l s = failloc l s

(* *** Compute types of registers taking (array) indexes into account
 * ------------------------------------------------------------------------ *)

let equiv_ty ty1 ty2 =
  match ty1, ty2 with
  | Bool,    Bool    -> true
  | U64    , U64     -> true
  | Arr(d1), Arr(d2) -> equal_dexpr d1 d2
  | _,       _       -> false

let get_dim (dim : pexpr) (lb_o,ub_o) =
  let zero = Pconst U64.zero in
  let lb = get_opt zero lb_o in
  let ub = get_opt dim ub_o in
  if equal_pexpr lb zero
  then ub
  else Pbinop(Pminus,ub,lb)

(* [type_dest_app pr ty] takes a pseudo-register pr<ies> and the
   type of pr and returns the type of pr<ies>.
   Example: for pr<3,0..n> with pr : u64<5,n>[n], the result is u64<n>[n] *)
let type_dest_app d ty =
  match ty with
  | TInvalid -> assert false
  | Bool | U64 ->
    if None<>d.d_idx then
      type_error_ d.d_loc "register has type %a, cannot access array element"
        pp_ty_nt ty;
    ty
  | Arr(_dim) as ty ->
    begin match d.d_idx with
    | None -> ty
    | _    -> U64
    end

(* Same as [type_dest_app] except that it looks up the type from [tenv] *)
let type_dest d =
  type_dest_app d d.d_var.Var.ty

(* Same as [type_dest] except that it asserts that type is equal to [ty_exp] *)
let typecheck_dest d ty_exp =
  let ty = type_dest d in
  if not (equiv_ty ty ty_exp) then
    type_error_ d.d_loc "type mismatch (got %a, expected %a)" pp_ty_nt ty pp_ty_nt ty_exp

(* Takes source and computes its type (see [type_dest]) *)
let type_src = function
  | Imm(_) -> U64
  | Src(d) -> type_dest d

(* Same as [type_dest] except that it asserts that type is equal to [ty_exp] *)
let typecheck_src s ty_exp =
  match s with
  | Imm(_) -> if not (equal_ty ty_exp (U64)) then assert false
  | Src(d) -> typecheck_dest d ty_exp

(* *** Check types for assignments, destinations, and sources
 * ------------------------------------------------------------------------ *)

(* Ensures that the source and destination for assignments are compatible *)
let typecheck_assgn d s pos =
  let ty_s = type_src s in
  let ty_d = type_dest d in
  if not (equiv_ty ty_s ty_d) then (
    failloc_ pos "incompatible types for assignment: lhs %, rhs %a)"
      pp_ty_nt ty_d pp_ty_nt ty_s
  ) (* FIXME: disallow flag assignments here? *)

(* Checks that the base type of the given source is equal to [t] *)
let type_src_eq src ty_exp =
  match src, ty_exp with
  | _    ,  TInvalid -> assert false
  | Imm _,  Bool     -> failwith "got u64, expected bool"
  | Imm _,  U64      -> ()
  | Imm _,  Arr(_)   -> failwith "got u64, expected u64[..]"
  | Src(d), t        -> typecheck_dest d t

(* *** Check types for ops, instructions, statements, and functions
 * ------------------------------------------------------------------------ *)

(* typecheck operators *)
let typecheck_op op ds ss =
  let type_dest_eq = typecheck_dest in
  match view_op op ds ss with

  | V_Umul(h,l,x,y) ->
    type_src_eq  x U64;
    type_src_eq  y U64;
    type_dest_eq l U64;
    type_dest_eq h U64

  | V_Carry(_,mcf_out,z,x,y,mcf_in) ->
    type_src_eq  x U64;
    type_src_eq  y U64;
    type_dest_eq z U64;
    Option.iter ~f:(fun s -> type_src_eq  s Bool) mcf_in;
    Option.iter ~f:(fun d -> type_dest_eq d Bool) mcf_out

  | V_Cmov(_,z,x,y,cf) ->
    type_src_eq  x     U64;
    type_src_eq  y     U64;
    type_src_eq  cf    Bool;
    type_dest_eq z     U64

  | V_ThreeOp(_,z,x,y) ->
    type_src_eq  x U64;
    type_src_eq  y U64;
    type_dest_eq z U64

  | V_Shift(_dir,mcf_out,z,x,y) ->
    type_src_eq  x U64;
    type_src_eq  y U64;
    type_dest_eq z U64;
    Option.iter ~f:(fun s -> type_dest_eq s Bool) mcf_out

let typecheck_fcond _env _fc = undefined ()
(*
  type_src_eq env (src_of_fcond fc) Bool
*)

let typecheck_fcond_or_pcond env = function
  | Pcond(_)  -> ()
  | Fcond(fc) -> typecheck_fcond env fc

let typecheck_base_instr env binstr =
  let tc_op    = typecheck_op    in
  let tc_assgn = typecheck_assgn in
  match binstr.L.l_val with
  | Comment _             -> ()
  | Op(op,ds,ss)          -> tc_op op ds ss
  | Assgn(d,s,_)          -> tc_assgn d s d.d_loc
  | Load(d,s,_pe)         -> type_src_eq  s U64; typecheck_dest d U64
  | Store(s1,_pe,s2)      -> type_src_eq s1 U64; type_src_eq s2 U64
  | Call(_fname,_rets,_args) ->
    undefined ()
    (*
    let cfun = map_find_exn env.e_fenv pp_string fname in
    let tc_src s (_,_,ty_expected) = typecheck_src env s ty_expected in
    let tc_dest d (_,ty_expected) = typecheck_dest env.e_tenv d ty_expected in
    list_iter2_exn args cfun.f_args ~f:tc_src
      ~err:(fun n_g n_e ->
              failwith_ "wrong number of arguments (got %i, exp. %i)" n_g n_e);
    list_iter2_exn rets cfun.f_ret_ty ~f:tc_dest
      ~err:(fun n_g n_e ->
              failwith_ "wrong number of l-values (got %i, exp. %i)" n_g n_e)
    *)

let rec typecheck_instr env instr =
  let tc_stmt  = typecheck_stmt  env in
  let tc_fcond = typecheck_fcond env in
  let tc_cond  = typecheck_fcond_or_pcond env in
  match instr.L.l_val with
  | Block(bis,_) ->
    List.iter ~f:(typecheck_base_instr env) bis
  | If(c,stmt1,stmt2,_) ->
    tc_cond c; tc_stmt stmt1; tc_stmt stmt2
  | For(pv,_,_,stmt,_) ->
    assert(pv.d_idx=None);
    typecheck_dest pv U64;
    typecheck_stmt env stmt
  | While(_wt,fc,s,_) ->
    tc_fcond fc;
    typecheck_stmt env s

and typecheck_stmt env stmt =
  List.iter ~f:(typecheck_instr env) stmt

let typecheck_ret _env _ret_ty _ret = undefined ()
(*
  List.iter2_exn ret ret_ty
    ~f:(fun name ty -> typecheck_dest env.e_tenv (mk_dest_name name Reg ty) ty)
*)

let typecheck_func _fenv func =
  match func with
  | Foreign(_) -> ()
  | Native(_fd) ->
    ()
    (*
    let decls = extract_decls func.f_args fdef in
    let tenv = Ident.Map.of_alist_exn
                 (  (Map.to_alist (tenv_of_func func decls))
                  @ (Map.to_alist penv))
    in
    let used_vars = idents_stmt fdef.fd_body in
    List.iter decls
      ~f:(fun (_,ident,_) ->
            if not (Set.mem used_vars ident) then
              failwith (fsprintf "variable %a in %s not used" pp_ident ident func.f_name));
    let env  = { e_penv = penv; e_fenv = fenv; e_tenv = tenv } in
    typecheck_stmt env fdef.fd_body;
    typecheck_ret env (List.map ~f:snd func.f_ret_ty) fdef.fd_ret
  *)

let typecheck_modul modul =
  vars_num_unique_modul modul;
  let penv =
    Pname.Table.of_alist_exn
      (List.map ~f:(fun p -> (p.Param.name,(p.Param.ty,p.Param.loc))) modul.m_params)
  in
  params_defined_modul penv (pp_ty ~pp_types:false) modul;
  (* let params_decl = params_modul modul in *)
  (* Set.iter params_decl *)
  (*   ~f:(fun p -> *)
  (*         if not (HT.mem penv p) then *)
  (*           type_error_ p.Param.loc *)
  (*             "parameter %a not declared (env: %a)" *)
  (*                Param.pp p (pp_list "," Param.pp) modul.m_params); *)
  Map.iteri modul.m_funcs
    ~f:(fun ~key:_ ~data:func -> typecheck_func modul.m_funcs func)
