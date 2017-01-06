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

(* *** Type errors
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

(* Return [true] if the types [t1] and [t2] are equivalent. *)
let equiv_ty ty1 ty2 =
  match ty1, ty2 with
  | Bty(bt1), Bty(bt2)       -> equal_base_ty bt1 bt2
  | Arr(bt1,d1), Arr(bt2,d2) -> equal_base_ty bt1 bt2 && equal_dexpr d1 d2
  | _,       _               -> false

(* Compute dimension from [dim] pexpr or upper and lower bound. *)
let get_dim (dim : pexpr) (lb_o,ub_o) =
  let zero = Pconst Big_int.zero_big_int in
  let lb = get_opt zero lb_o in
  let ub = get_opt dim ub_o in
  if equal_pexpr lb zero
  then ub
  else Pbinop(Pminus,ub,lb)

(* Compute the type of sdest [sd] taking indexing into account. *)
let type_sdest sd =
  let ty = sd.d_var.Var.ty in
  match ty with
  | TInvalid -> assert false
  | Bty(bt) ->
    if None<>sd.d_idx then
      type_error_ sd.d_loc "register has type %a, cannot access array element"
        pp_base_ty bt;
    ty
  | Arr(bt,_dim) as ty ->
    begin match sd.d_idx with
    | None -> ty
    | _    -> Bty(bt)
    end

(* Ensure that [sd] has given type [ty_exp]. *)
let typecheck_sdest sd ty_exp =
  let ty = type_sdest sd in
  if not (equiv_ty ty ty_exp) then
    P.failparse_l
      [ (sd.d_loc,
         fsprintf "type mismatch (got %a, expected %a)" pp_ty_nt ty pp_ty_nt ty_exp);
        (sd.d_var.Var.dloc, "<-- declared here") ]

let typecheck_rdest rd ty_exp =
  match rd with
  | Sdest(sd)  -> typecheck_sdest sd ty_exp
  | Mem(sd,_pe) ->
    typecheck_sdest sd (Bty(U(64)));
    if ty_exp<>Bty(U(64)) then
      failloc_ sd.d_var.Var.uloc "Memory access return u64"


(* Ensure that [d] has given type [ty_exp]. *)
let typecheck_dest d ty_exp =
  match d with
  | Ignore(_) -> ()
  | Rdest(rd) -> typecheck_rdest rd ty_exp

(* Return type of [d] and ensure that d well-typed. *)
let type_rdest rd =
  match rd with
  | Sdest(sd)   -> type_sdest sd
  | Mem(sd,_pe) -> typecheck_sdest sd (Bty(U(64))); Bty(U(64))

(* Return type of [d] and ensure that d well-typed. *)
let type_dest d =
  match d with
  | Ignore(_) -> assert false
  | Rdest(rd) -> type_rdest rd

(* Return type of source [s]. *)
let type_src s =
  match s with
  | Imm(n,_) -> Bty(U(n))
  | Src(d)   -> type_rdest d

(* Ensure that type of [s] is equal to [ty_exp]. *)
let typecheck_src s ty_exp =
  match s with
  | Imm(_) -> if not (equal_ty ty_exp (Bty(U(64)))) then assert false
  | Src(d) -> typecheck_rdest d ty_exp

(* Ensure that var [v] has type [ty] and (optional) storage [os]. *)
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
  )

(* Checks that the base type of the given source is equal to [t] *)
let type_src_eq src ty_exp =
  match src, ty_exp with
  | _    ,  TInvalid   -> assert false
  | Imm _,  Bty(Bool)  -> failwith "got u64, expected bool"
  | Imm _,  Bty(U(64)) -> ()
  | Imm _,  Bty(U(i))  -> failwith_ "got u64, expected u%i" i
  | Imm _,  Bty(Int)   -> failwith_ "got u64, expected int"
  | Imm _,  Arr(_)     -> failwith "got u64, expected u64[..]"
  | Src(d), t          -> typecheck_rdest d t

(* *** Check types for ops, instructions, statements, and functions
 * ------------------------------------------------------------------------ *)

let typecheck_op op ds ss =
  let type_dest_eq = typecheck_dest in
  match view_op op ds ss with

  | V_Umul(h,l,x,y) ->
    type_src_eq  x tu64;
    type_src_eq  y tu64;
    type_dest_eq l tu64;
    type_dest_eq h tu64

  | V_Carry(_,mcf_out,z,x,y,mcf_in) ->
    type_src_eq  x tu64;
    type_src_eq  y tu64;
    type_dest_eq z tu64;
    Option.iter ~f:(fun s -> type_src_eq  s tbool) mcf_in;
    Option.iter ~f:(fun d -> type_dest_eq d tbool) mcf_out

  | V_Cmov(_,z,x,y,cf) ->
    type_src_eq  x tu64;
    type_src_eq  y tu64;
    type_src_eq  cf tbool;
    type_dest_eq z  tu64

  | V_ThreeOp(_,z,x,y) ->
    type_src_eq  x tu64;
    type_src_eq  y tu64;
    type_dest_eq z tu64

  | V_Shift(_dir,mcf_out,z,x,y) ->
    type_src_eq  x tu64;
    type_src_eq  y tu64;
    type_dest_eq z tu64;
    Option.iter ~f:(fun s -> type_dest_eq s tbool) mcf_out

let typecheck_fcond fc =
  type_var_eq fc.fc_var tbool (Some(Reg))

let typecheck_fcond_or_pcond = function
  | Pcond(_)  -> ()
  | Fcond(fc) -> typecheck_fcond fc

let typecheck_call fptable ftable loc fname ret arg =
  let arg_ty, ret_ty, stor_dont_care =
    match HT.find ftable fname with
    | None       ->
      begin match HT.find fptable fname with
      | None -> failloc_ loc "call to unknown function %a" Fname.pp fname
      | Some(np) -> np.np_arg_ty, np.np_ret_ty,true
      end
    | Some(func) ->
      List.map ~f:tinfo_of_var func.f_arg,List.map ~f:tinfo_of_var func.f_ret,false
    in
    let tc_rdest rd (sto_exp,ty_exp) =
      typecheck_rdest rd ty_exp;
      let uloc,sto =
        match rd with
        | Mem(sd,_) -> sd.d_loc, Stack (* FIXME: we treat Mem and Stack the same *)
        | Sdest(sd) -> sd.d_loc, sd.d_var.Var.stor
      in
      if not stor_dont_care && sto<>sto_exp then
        failloc_ uloc "wrong storage type for call of %a: got ``%s'', expected ``%s''"
          Fname.pp fname (string_of_storage sto) (string_of_storage sto_exp)
    in
    let tc_imm n (sto_exp,ty_exp) =
      let ty = tuN n in
      let sto = Inline in
      if not (equiv_ty ty ty_exp) then
        failwith_ "wrong type for call of %a: got ``%a'', expected ``%a''"
          Fname.pp fname pp_ty_nt ty pp_ty_nt ty_exp;
      if sto_exp<>sto then
        failwith_ "wrong storage type for call of %a: got ``%s'', expected ``%s''"
          Fname.pp fname (string_of_storage sto) (string_of_storage sto_exp)
    in
    let tc_src s st =
      match s with
      | Src(d)   -> tc_rdest d st
      | Imm(n,_) -> tc_imm n st
    in
    let tc_dest d st =
      match d with
      | Ignore(_) -> ()
      | Rdest(rd) -> tc_rdest rd st
    in
    list_iter2_exn arg arg_ty ~f:tc_src
      ~err:(fun n_g n_e -> failloc_ loc "wrong number of arguments: got %i, expected %i" n_g n_e);
    list_iter2_exn ret ret_ty ~f:tc_dest
      ~err:(fun n_g n_e -> failloc_ loc "wrong number of l-values: got %i, expected %i" n_g n_e)


let typecheck_base_instr fptable ftable lbinstr =
  let loc = lbinstr.L.l_loc in
  match lbinstr.L.l_val with
  | Comment _             -> ()
  | Op(op,ds,ss)          -> typecheck_op op ds ss
  | Assgn(d,s,_)          -> typecheck_assgn d s loc
  | Call(fname,ret,arg,_) -> typecheck_call fptable ftable loc fname ret arg
  (* | Load(d,s,_pe)       -> type_src_eq  s (U(64)); typecheck_dest d (U(64)) *)
  (* | Store(s1,_pe,s2)    -> type_src_eq s1 (U(64)); type_src_eq s2 (U(64)) *)

let rec typecheck_instr fptable ftable instr =
  let tc_stmt  = typecheck_stmt fptable ftable in
  let tc_bi    = typecheck_base_instr fptable ftable in
  let tc_sdest = typecheck_sdest in
  let tc_fcond = typecheck_fcond in
  let tc_cond  = typecheck_fcond_or_pcond in
  match instr.L.l_val with
  | Block(bis,_)        -> List.iter ~f:tc_bi bis
  | If(c,stmt1,stmt2,_) -> tc_cond c; tc_stmt stmt1; tc_stmt stmt2
  | For(sd,_,_,stmt,_)  -> assert(sd.d_idx=None); tc_sdest sd tu64; tc_stmt stmt
  | While(_wt,fc,s,_)   -> tc_fcond fc; tc_stmt s

and typecheck_stmt fptable ftable stmt =
  List.iter ~f:(typecheck_instr fptable ftable) stmt

let typecheck_func fptable ftable func =
  typecheck_stmt fptable ftable func.f_body

let typecheck_modul modul =
  vars_num_unique_modul ~type_only:true modul;
  params_consistent_modul (pp_ty ~pp_types:false) modul;
  let fptable = 
    Fname.Table.of_alist_exn (List.map ~f:(fun np -> (np.np_name, np))
                                (IL_stdlib.std_protos () @ modul.mod_funprotos))
  in
  let ftable =
    Fname.Table.of_alist_exn (List.map ~f:(fun nf -> (nf.nf_name, nf.nf_func)) modul.mod_funcs)
  in
  List.iter modul.mod_funcs ~f:(fun nf -> typecheck_func fptable ftable nf.nf_func)
