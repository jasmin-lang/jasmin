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

(* *** Compute types of registers taking (array) indexes into account
 * ------------------------------------------------------------------------ *)

let ty_env_of_efun efun = String.Map.of_alist_exn (efun.ef_args @ efun.ef_decls)

let get_dim (_dim : pexpr) idx =
  match idx with  (* FIXME: check [lb..ub] <= [0..dim]? *)
  | Get _      -> None
  | All(lb,ub) ->
    if equal_pexpr lb (Pconst U64.zero)
    then Some(ub)
    else Some(Pbinop(Pminus,ub,lb))


(** [type_pr_app_g pr ty] takes a pseudo-register pr<ies> and the
    type of pr and returns the type of pr<ies>.
    Example: for pr<3,0..n> with pr : u64<5,n>[n], the result is u64<n>[n] *)
let type_pr_app pr ty =
  match ty with
  | Bool ->
    if pr.pr_idxs<>[] then
      preg_error pr ("register has type bool, invalid usage");
    Bool
  | U64(idx_dims,arr_dims) ->
    let new_idx_dims =
      list_map2_exn idx_dims pr.pr_idxs ~f:get_dim
        ~err:(fun l_exp l_got ->
            preg_error pr
              (fsprintf "indexed register %s must be fully applied (got %i, expected %i)"
                 pr.pr_name l_got l_exp))
      |> List.filter_opt
    in
    U64(new_idx_dims,arr_dims)

(** Same as [ty_pr_app] except that it looks up the type from [ty_env] *)
let type_pr ty_env pr =
  type_pr_app pr (map_find_exn ~err:(preg_error pr) ty_env pp_string pr.pr_name)

(** Same as [type_pr] except that it assert that type is equal to [ty_exp] *)
let typecheck_pr ty_env pr ty_exp =
  let ty = type_pr ty_env pr in
  if not (equal_ty ty ty_exp) then
    preg_error pr (fsprintf "type mismatch (got %a, expected %a)" pp_ty ty pp_ty ty_exp)

(** Takes destination pr<iidxs>[aidxs] and computes its type by looking up
    the type of [pr] in [ty_env] and accounting for the applications.
    Example: pr<1,..>[3,..] where pr : u64<5,n>[5,n,n], result u64<n,n>[n].
            Note that partially applied, hence all elements are arrays. *)
let type_dest ty_env {d_pr; d_aidxs} =
  match type_pr ty_env d_pr with
  | Bool ->
    if d_aidxs<>[] then
      preg_error d_pr ("register has type bool, invalid usage");
    Bool

  | U64(_,dims) as ty when List.length d_aidxs > List.length dims ->
    preg_error d_pr (fsprintf "too many array indexes given, has type %a" pp_ty ty)


  | U64(tidxs,adims) as ty ->
    let l_aidxs = List.length d_aidxs in
    let dims_indexed  = List.take adims l_aidxs in
    let dims_noexpand = List.drop adims l_aidxs in
    let dims_expand =
      list_map2_exn dims_indexed d_aidxs
        ~f:(fun tdim id -> match id with Get(_) -> None | All(_lb,_ub) -> Some tdim)
        (* FIXME *)
        ~err:(fun l_exp l_got -> 
                preg_error d_pr
                (fsprintf "indexed register %a:%a must be fully applied (got %i, expected %i)"
                   pp_preg d_pr pp_ty ty l_got l_exp))
        |> List.filter_opt
    in
    U64(tidxs@dims_expand,dims_noexpand)

(** Same as [type_dest] except that it assert that type is equal to [ty_exp] *)
let typecheck_dest ty_env dest ty_exp =
  let ty = type_dest ty_env dest in
  if not (equal_ty ty ty_exp) then
    preg_error dest.d_pr (fsprintf "type mismatch for %a (got %a, expected %a)"
                            pp_dest dest pp_ty ty pp_ty ty_exp)

(** Takes source and computes its type (see [type_dest]) *)
let type_src ty_env s =
  match s with
  | Imm(_) -> U64([],[])
  | Src(d) -> type_dest ty_env d

(** Same as [type_dest] except that it assert that type is equal to [ty_exp] *)
let typecheck_src ty_env s ty_exp =
  match s with
  | Imm(_) -> if not (equal_ty ty_exp (U64([],[]))) then assert false
  | Src(d) -> typecheck_dest ty_env d ty_exp

(* *** Check types for assignments, destinations, and sources
 * ------------------------------------------------------------------------ *)

type base_type = T_U64 | T_Bool

(** Ensures that the source and destination for assignments are compatible *)
let typecheck_assgn ty_env d s =
  let ty_s = type_src  ty_env s in
  let ty_d = type_dest ty_env d in 
  match ty_s, ty_d with
  | U64(tidxs_s,dims_s), U64(tidxs_d,dims_d)
    (* we allow xp[..] = yp<..> if dims match *)
    when equal_ty (U64(tidxs_s@dims_s,[])) (U64(tidxs_d@dims_d,[])) ->
    ()
  | Bool, Bool ->
    preg_error d.d_pr (fsprintf "incompatible types for assignment %a (cannot assign flags)"
                         pp_instr (Binstr(Assgn(d,s))));
  | U64(tidxs_s,[]), U64(tidxs_d,[_s])
    (* FIXME: generalize, assign address to array type *)
    when equal_ty (U64(tidxs_s,[])) (U64(tidxs_d,[])) ->
    ()
  | _ -> 
    if not (equal_ty ty_s ty_d) then
      preg_error d.d_pr (fsprintf "incompatible types for assignment %a (lhs %a, rhs %a)"
                           pp_instr (Binstr(Assgn(d,s))) pp_ty ty_d pp_ty ty_s);
    ()

(** Checks that the base type of the given destination is equal to [t] *)
let type_dest_eq ty_env {d_pr;d_aidxs} (t : base_type) =
  match map_find_exn ~err:(preg_error d_pr) ty_env pp_string d_pr.pr_name with
  | Bool     when t=T_U64  -> failwith "got bool, expected u64"
  | Bool                   -> ()
  | U64(_,_) when t=T_Bool -> failwith "got u64<_>[_], expected bool"
  | U64(iidxs,aidxs) as ty ->
    if (   List.length d_pr.pr_idxs<>List.length iidxs
        || List.length d_aidxs<>List.length aidxs) then
      preg_error d_pr (fsprintf "expected type u64, register name of type %a not fully applied"
                         pp_ty ty)

(** Checks that the base type of the given source is equal to [t] *)
let type_src_eq ty_env src (t : base_type) =
  match src, t with
  | Imm _,  T_Bool -> failwith "got u64, expected bool"
  | Imm _,  T_U64  -> ()
  | Src(d), t      -> type_dest_eq ty_env d t

(* *** Check types for ops, instructions, statements, and functions
 * ------------------------------------------------------------------------ *)

let typecheck_op ty_env op z x y =
  let type_src_eq  = type_src_eq  ty_env in
  let type_dest_eq = type_dest_eq ty_env in
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

let rec typecheck_instr fun_env ty_env instr =
  let typecheck_stmt  = typecheck_stmt fun_env ty_env in
  let typecheck_op    = typecheck_op           ty_env in
  let typecheck_assgn = typecheck_assgn        ty_env in
  match instr with
  | Binstr(Comment _)        -> ()
  | Binstr(Op(op,d,(s1,s2))) -> typecheck_op op d s1 s2
  | Binstr(Assgn(d,s))       -> typecheck_assgn d s
  | If(_,stmt1,stmt2)        -> typecheck_stmt stmt1; typecheck_stmt stmt2
  | For(_,_,_,stmt)          -> typecheck_stmt stmt
  | Call(fname,rets,args)    ->
    let cfun = map_find_exn fun_env pp_string fname in
    let typecheck_src s (_,ty_exp) = typecheck_src ty_env s ty_exp in
    let typecheck_dest d (_,ty_exp) = typecheck_dest ty_env d ty_exp in
    list_iter2_exn args cfun.ef_args ~f:typecheck_src
      ~err:(fun n_g n_e ->
              failwith (fsprintf "arguments have wrong length (got %i, expected %i)" n_g n_e));
    list_iter2_exn rets cfun.ef_ret ~f:typecheck_dest
      ~err:(fun n_g n_e ->
              failwith (fsprintf "l-values have wrong length (got %i, expected %i)" n_g n_e))
      
and typecheck_stmt fun_env ty_env stmt =
  List.iter ~f:(typecheck_instr fun_env ty_env) stmt

let typecheck_ret ty_env ret =
  List.iter ret ~f:(fun (pr,ty) -> typecheck_pr ty_env pr ty)

let typecheck_efun fun_env efun =
  let ty_env = ty_env_of_efun efun in
  typecheck_stmt fun_env ty_env efun.ef_body;
  typecheck_ret ty_env efun.ef_ret

let typecheck_efuns efuns =
  let smap = String.Map.of_alist_exn (List.map efuns ~f:(fun ef -> (ef.ef_name, ef))) in
  List.iter efuns ~f:(typecheck_efun smap)
