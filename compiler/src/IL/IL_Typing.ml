(* * Typing of IL *)

(* ** Imports *)
open IL_Lang
open IL_Pprint
open IL_Utils
open IL_Iter
open Util
open Core_kernel.Std

module P = ParserUtil
module L = ParserUtil.Lexing

(* ** Check type information and propagate to pregs
 * ------------------------------------------------------------------------ *)

(* *** Typing environment
 * ------------------------------------------------------------------------ *)

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
  | Bool,    Bool        -> true
  | U(i)   , U(j)        -> i = j
  | Arr(i,d1), Arr(j,d2) -> i = j && equal_dexpr d1 d2
  | _,       _           -> false

let get_dim (dim : pexpr) (lb_o,ub_o) =
  let zero = Pconst Big_int.zero_big_int in
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
  | Bool | U(_) ->
    if None<>d.d_idx then
      type_error_ d.d_loc "register has type %a, cannot access array element"
        pp_ty_nt ty;
    ty
  | Arr(i,_dim) as ty ->
    begin match d.d_idx with
    | None -> ty
    | _    -> U(i)
    end

(* Same as [type_dest_app] except that it looks up the type from [tenv] *)
let type_dest d =
  type_dest_app d d.d_var.Var.ty

(* Same as [type_dest] except that it asserts that type is equal to [ty_exp] *)
let typecheck_dest d ty_exp =
  let ty = type_dest d in
  if not (equiv_ty ty ty_exp) then
    P.failparse_l
      [ (d.d_loc,
         fsprintf "type mismatch (got %a, expected %a)" pp_ty_nt ty pp_ty_nt ty_exp);
        (d.d_var.Var.dloc, "<-- declared here") ]

(* Takes source and computes its type (see [type_dest]) *)
let type_src = function
  | Imm(n,_) -> U(n)
  | Src(d)   -> type_dest d

(* Same as [type_dest] except that it asserts that type is equal to [ty_exp] *)
let typecheck_src s ty_exp =
  match s with
  | Imm(_) -> if not (equal_ty ty_exp (U(64))) then assert false
  | Src(d) -> typecheck_dest d ty_exp

let type_var_eq v ty os =
  if not (equiv_ty v.Var.ty ty) then
    type_error_ v.Var.uloc "type mismatch (got %a, expected %a)"
      pp_ty_nt v.Var.ty pp_ty_nt ty;
  match os with
  | Some(s) when s<>v.Var.stor->
    type_error_ v.Var.uloc "storage mismatch (got %s, expected %s)"
      (string_of_storage v.Var.stor) (string_of_storage s)
  | _ -> ()

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
  | Imm _,  U(64)    -> ()
  | Imm _,  U(i)     -> failwith_ "got u64, expected u%i" i
  | Imm _,  Arr(_)   -> failwith "got u64, expected u64[..]"
  | Src(d), t        -> typecheck_dest d t

(* *** Check types for ops, instructions, statements, and functions
 * ------------------------------------------------------------------------ *)

(* typecheck operators *)
let typecheck_op op ds ss =
  let type_dest_eq = typecheck_dest in
  match view_op op ds ss with

  | V_Umul(h,l,x,y) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_dest_eq l (U(64));
    type_dest_eq h (U(64))

  | V_Carry(_,mcf_out,z,x,y,mcf_in) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_dest_eq z (U(64));
    Option.iter ~f:(fun s -> type_src_eq  s Bool) mcf_in;
    Option.iter ~f:(fun d -> type_dest_eq d Bool) mcf_out

  | V_Cmov(_,z,x,y,cf) ->
    type_src_eq  x     (U(64));
    type_src_eq  y     (U(64));
    type_src_eq  cf    Bool;
    type_dest_eq z     (U(64))

  | V_ThreeOp(_,z,x,y) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_dest_eq z (U(64))

  | V_Shift(_dir,mcf_out,z,x,y) ->
    type_src_eq  x (U(64));
    type_src_eq  y (U(64));
    type_dest_eq z (U(64));
    Option.iter ~f:(fun s -> type_dest_eq s Bool) mcf_out

let typecheck_fcond fc =
  type_var_eq fc.fc_var Bool (Some(Reg))

let typecheck_fcond_or_pcond = function
  | Pcond(_)  -> ()
  | Fcond(fc) -> typecheck_fcond fc

let typecheck_base_instr ftable lbinstr =
  let tc_op    = typecheck_op    in
  let tc_assgn = typecheck_assgn in
  match lbinstr.L.l_val with
  | Comment _           -> ()
  | Op(op,ds,ss)        -> tc_op op ds ss
  | Assgn(d,s,_)        -> tc_assgn d s d.d_loc
  | Load(d,s,_pe)       -> type_src_eq  s (U(64)); typecheck_dest d (U(64))
  | Store(s1,_pe,s2)    -> type_src_eq s1 (U(64)); type_src_eq s2 (U(64))
  | Call(fname,ret,arg) ->
    let loc = lbinstr.L.l_loc in
    let arg_ty, ret_ty =
      match HT.find ftable fname with
      | None       -> failloc_ loc "call to unknown function %a" Fname.pp fname
      | Some(func) ->
        begin match func with
        | Foreign(fo) -> (fo.fo_arg_ty, fo.fo_ret_ty)
        | Native(fd)  -> (List.map ~f:tinfo_of_var fd.f_arg,List.map ~f:tinfo_of_var fd.f_ret)
        end
    in
    let tc_dest d (sto_exp,ty_exp) =
      typecheck_dest d ty_exp;
      let sto = d.d_var.Var.stor in
      if sto<>sto_exp then
        failloc_ d.d_var.Var.uloc "wrong storage type for call of %a: got ``%s'', expected ``%s''"
          Fname.pp fname (string_of_storage sto) (string_of_storage sto_exp)
    in
    let tc_src s st =
      match s with
      | Imm(_) -> failloc_ loc "cannot call function %a with immediate value" Fname.pp fname
      | Src(d) -> tc_dest d st
    in
    list_iter2_exn arg arg_ty ~f:tc_src
      ~err:(fun n_g n_e -> failloc_ loc "wrong number of arguments: got %i, expected %i" n_g n_e);
    list_iter2_exn ret ret_ty ~f:tc_dest
      ~err:(fun n_g n_e -> failloc_ loc "wrong number of l-values: got %i, expected %i" n_g n_e)

let rec typecheck_instr ftable instr =
  let tc_stmt  = typecheck_stmt ftable in
  let tc_bi    = typecheck_base_instr ftable in
  let tc_dest  = typecheck_dest in
  let tc_fcond = typecheck_fcond in
  let tc_cond  = typecheck_fcond_or_pcond in
  match instr.L.l_val with
  | Block(bis,_)        -> List.iter ~f:tc_bi bis
  | If(c,stmt1,stmt2,_) -> tc_cond c; tc_stmt stmt1; tc_stmt stmt2
  | For(pv,_,_,stmt,_)  -> assert(pv.d_idx=None); tc_dest pv (U(64)); tc_stmt stmt
  | While(_wt,fc,s,_)   -> tc_fcond fc; tc_stmt s

and typecheck_stmt ftable stmt =
  List.iter ~f:(typecheck_instr ftable) stmt

let typecheck_func ftable func =
  match func with
  | Foreign(_) -> ()
  | Native(fd) ->
    typecheck_stmt ftable fd.f_body

let typecheck_modul modul =
  vars_num_unique_modul ~type_only:true modul;
  params_consistent_modul (pp_ty ~pp_types:false) modul;
  let ftable = Fname.Table.of_alist_exn (List.map ~f:(fun nf -> (nf.nf_name, nf.nf_func)) modul) in
  List.iter modul ~f:(fun nf -> typecheck_func ftable nf.nf_func)
