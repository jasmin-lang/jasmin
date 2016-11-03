open Core_kernel.Std
open IL_Lang
open IL_Utils
open IL_Misc
open Arith
open Util

(* ** Pretty printing
 * ------------------------------------------------------------------------ *)

type info_ctxt = BlockStart | BlockEnd

let string_of_storage = function
  | SInvalid -> "invalid"
  | Stack    -> "stack"
  | Reg      -> "reg"
  | Inline   -> "inline"


let string_of_call_conv = function
  | Extern -> "extern "
  | _      -> ""

let string_of_pbinop = function
  | Pplus  -> "+"
  | Pmult  -> "*"
  | Pminus -> "-"

let pp_add_suffix fs pp fmt x =
  F.fprintf fmt ("%a"^^fs) pp x

let pp_add_prefix fs pp fmt x =
  F.fprintf fmt (fs^^"%a") pp x

let rec pp_patom ~pp_types fmt pa =
  match pa with
  | Pparam(p) -> F.fprintf fmt "$%a" Param.pp p
  | Pvar(v)   -> pp_var_i ~pp_types fmt v

and pp_var_i ~pp_types fmt v =
  F.fprintf fmt "%a : %s %a"
    Var.pp v
    (string_of_storage v.Var.stor)
    (pp_ty ~pp_types) v.Var.ty

and pp_param_i ~pp_types fmt p =
  F.fprintf fmt "%a : %a"
    Param.pp p
    (pp_ty ~pp_types) p.Param.ty

and pp_param ~pp_types fmt p =
  if pp_types then
    pp_param_i ~pp_types fmt p
  else
    Param.pp fmt p

and pp_ty ~pp_types fmt ty =
  match ty with
  | TInvalid -> F.fprintf fmt "invalid"
  | Bool     -> F.fprintf fmt "bool"
  | U64      -> F.fprintf fmt "u64"
  | Arr(dim) -> F.fprintf fmt "u64[%a]" (pp_dexpr ~pp_types) dim

and pp_dexpr ~pp_types fmt ce =
  let ppd = pp_dexpr ~pp_types in
  match ce with
  | Patom(p)           -> pp_param ~pp_types fmt p
  | Pbinop(op,ie1,ie2) -> F.fprintf fmt "%a %s %a" ppd ie1 (string_of_pbinop op) ppd ie2
  | Pconst(u)          -> pp_string fmt (U64.to_string u)

and pp_var ~pp_types fmt v =
  if pp_types then
    F.fprintf fmt "(%a)" (pp_var_i ~pp_types) v
  else
    Var.pp fmt v

let rec pp_pexpr ~pp_types fmt ce =
  let ppe = pp_pexpr ~pp_types in
  match ce with
  | Patom(pa)          -> pp_patom ~pp_types fmt pa
  | Pbinop(op,ie1,ie2) -> F.fprintf fmt "%a %s %a" ppe ie1 (string_of_pbinop op) ppe ie2
  | Pconst(u)          -> pp_string fmt (U64.to_string u)

let pp_idx ~pp_types fmt = function
  | Iconst(pe) -> pp_pexpr ~pp_types fmt pe
  | Ivar(v)    -> pp_var ~pp_types fmt v

let pp_dest ~pp_types fmt {d_var=v; d_idx=oidx} =
  let ppi = pp_idx ~pp_types in
  match oidx with
  | None      -> F.fprintf fmt "%a"      (pp_var ~pp_types) v
  | Some(idx) -> F.fprintf fmt "%a[$%a]" (pp_var ~pp_types) v ppi idx

let pcondop_to_string = function
  | Peq      -> "="
  | Pineq    -> "!="
  | Pless    -> "<"
  | Pleq     -> "<="
  | Pgreater -> ">"
  | Pgeq     -> ">="

let rec pp_pcond ~pp_types fmt pc =
  let ppc = pp_pcond ~pp_types in
  let ppe = pp_pexpr ~pp_types in
  match pc with
  | Ptrue           -> pp_string fmt "true"
  | Pnot(ic)        -> F.fprintf fmt"!(%a)" ppc ic
  | Pand(c1,c2)     -> F.fprintf fmt"(%a && %a)" ppc c1 ppc c2
  | Pcmp(o,ie1,ie2) -> F.fprintf fmt"(%a %s %a)" ppe ie1 (pcondop_to_string o) ppe ie2

let pp_src ~pp_types fmt = function
  | Src(d)  -> pp_dest ~pp_types fmt d
  | Imm(pe) -> pp_pexpr ~pp_types fmt pe

let pp_fcond ~pp_types fmt fc =
  F.fprintf fmt "%s%a" (if fc.fc_neg then "!" else "") (pp_var ~pp_types) fc.fc_var

let pp_fcond_or_pcond ~pp_types fmt = function
  | Pcond(pc) -> F.fprintf fmt "$%a" (pp_pcond ~pp_types) pc
  | Fcond(fc) -> F.fprintf fmt "(%a)" (pp_fcond ~pp_types) fc

let string_of_carry_op = function O_Add -> "+" | O_Sub -> "-"

let pp_three_op fmt o =
  pp_string fmt
    (match o with
     | O_Imul -> "*"
     | O_And  -> "&"
     | O_Xor  -> "^"
     | O_Or   -> "|")

let pp_op ~pp_types fmt (o,ds,ss) =
  let ppd = pp_dest ~pp_types in
  let pps = pp_src ~pp_types in
  let ppdso ppo fmt (d,s,o) =
    if equal_src (Src(d)) s then
      F.fprintf fmt "%a %a=" ppd d ppo o
    else
      F.fprintf fmt "%a = %a %a" ppd d pps s ppo o
  in
  match view_op o ds ss with
  | V_Umul(d1,d2,s1,s2) ->
    F.fprintf fmt "%a, %a = %a * %a" ppd d1 ppd d2 pps s1 pps s2
  | V_ThreeOp(o,d1,s1,s2) ->
    F.fprintf fmt "%a %a" (ppdso pp_three_op) (d1,s1,o) pps s2
  | V_Carry(cfo,od1,d2,s1,s2,os3) ->
    let so = string_of_carry_op cfo in
    F.fprintf fmt "%a%a %a%a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a, " ppd d
         | None   -> pp_string fmt "")
      od1
      (ppdso pp_string) (d2,s1,so)
      pps s2
      (fun fmt os ->
         match os with
         | Some s -> F.fprintf fmt " %s %a" so pps s
         | None   -> pp_string fmt "")
      os3
  | V_Cmov(neg,d1,s1,s2,s3) ->
    F.fprintf fmt "%a = %a if %s%a else %a"
      ppd d1 pps s2 (if neg then "!" else "") pps s3 pps s1
  | V_Shift(dir,od1,d1,s1,s2) ->
    F.fprintf fmt "%a%a %a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a" ppd d
         | None   -> pp_string fmt "")
      od1
      (ppdso pp_string) (d1,s1,match dir with Left -> "<<" | Right -> ">>")
      pps s2

let pp_base_instr ~pp_types fmt bi =
  let ppd = pp_dest ~pp_types in
  let pps = pp_src ~pp_types in
  let ppe = pp_pexpr ~pp_types in
  let ppo = pp_op ~pp_types in
  match bi.L.l_val with
  | Comment(s)      -> F.fprintf fmt "/* %s */" s
  | Load(d,s,pe)    -> F.fprintf fmt "%a = MEM[%a + %a];" ppd d pps s ppe pe
  | Store(s1,pe,s2) -> F.fprintf fmt "MEM[%a + %a] = %a;" pps s1 ppe pe pps s2
  | Assgn(d1,s1,Mv) -> F.fprintf fmt "%a = %a;" ppd d1 pps s1
  | Assgn(d1,s1,Eq) -> F.fprintf fmt "%a := %a;" ppd d1 pps s1
  | Op(o,ds,ss)     -> F.fprintf fmt "%a;" ppo (o,ds,ss)
  | Call(fn,[],args) ->
    F.fprintf fmt "%a(%a);" Fname.pp fn (pp_list "," pps) args
  | Call(fn,dest,args) ->
    F.fprintf fmt "%a = %a(%a);"
      (pp_list "," ppd) dest
      Fname.pp fn
      (pp_list "," pps) args

let rec pp_instr ?pp_info ~pp_types fmt instr =
  let pp_start, pp_end =
    let cempty fmt _ = pp_empty fmt in
    let cstart pp fmt = F.fprintf fmt "%a@\n" (pp BlockStart) in
    let cend pp fmt = F.fprintf fmt "@\n%a" (pp BlockEnd) in
    match pp_info with
    | Some(pp) -> cstart pp, cend pp
    | None     -> cempty, cempty
  in
  let pps = pp_stmt ?pp_info ~pp_types in
  let ppc = pp_fcond_or_pcond ~pp_types in
  let ppfc = pp_fcond ~pp_types in
  let ppe = pp_pexpr ~pp_types in
  let ppd = pp_dest ~pp_types in
  let ppbi = pp_base_instr ~pp_types in
  let pp fmt () =
    match instr.L.l_val with
    | Block(bis,_) -> pp_list "@\n" ppbi fmt bis
    | If(c,i1,[],_) ->
      F.fprintf fmt "if %a {@\n  @[<v 0>%a@]@\n}" ppc c pps i1
    | If(c,i1,i2,_) ->
      F.fprintf fmt "if %a {@\n  @[<v 0>%a@]@\n} else {@\n  @[<v 0>%a@]@\n}"
        ppc c pps i1 pps i2
    | For(iv,ie1,ie2,i,_) ->
      F.fprintf fmt "for %a in %a..%a {@\n  @[<v 0>%a@]@\n}"
        ppd iv ppe ie1 ppe ie2 pps i
    | While(WhileDo,fc,s,_) ->
      F.fprintf fmt "while %a {@\n  @[<v 0>%a@]@\n}" ppfc fc pps s
    | While(DoWhile,fc,s,_) ->
      F.fprintf fmt "do {@\n  @[<v 0>%a@]@\n} while %a;" pps s ppfc fc
  in
  let info = get_info_instr instr.L.l_val in
  F.fprintf fmt "%a%a%a" pp_start info pp () pp_end info

and pp_stmt  ?pp_info ~pp_types fmt stmt =
  pp_list "@\n" (pp_instr ?pp_info ~pp_types) fmt stmt

let pp_return ~pp_types fmt names =
  match names with
  | [] -> pp_string fmt ""
  | _  -> F.fprintf fmt "return %a;" (pp_list "," (pp_var ~pp_types)) names

let pp_tinfo ~pp_types fmt (sto,ty) =
  F.fprintf fmt "%s %a"
    (string_of_storage sto) (pp_ty ~pp_types) ty

let pp_ret_ty ~pp_types fmt ret_ty =
  if ret_ty=[] then pp_string fmt ""
  else F.fprintf fmt " -> %a" (pp_list " * " (pp_tinfo ~pp_types)) ret_ty

let pp_fundef  ?pp_info ~pp_types fmt (decls,body,ret) =
  let pp_either test fse fsne fmt () =
    if test then  F.fprintf fmt fse
    else F.fprintf fmt fsne
  in
  let ppvi = pp_var_i ~pp_types in
  F.fprintf fmt 
    (  " {%a@[<v 0>%a" (* decls *)
     ^^"%a"            (* body *)
     ^^"%a"            (* body *)
     ^^"%a%a@]@\n}")   (* return *)
    (pp_either ((decls,body,ret)=([],[],[])) "" "@\n  ") ()
    (pp_list "@\n" ppvi) decls
    (pp_either (decls=[] || body=[]) "" "@\n") ()
    (pp_stmt ?pp_info ~pp_types) body
    (pp_either ((decls=[] && body=[]) || ret=[]) "" "@\n") ()
    (pp_return ~pp_types) ret

let pp_foreign ~pp_types fmt name fo =
  F.fprintf fmt "@[<v 0>fn %a(%a)%a%s@]"
    Fname.pp name
    (pp_list "," (pp_tinfo ~pp_types)) fo.fo_arg_ty
    (pp_ret_ty ~pp_types) fo.fo_ret_ty
    (match fo.fo_py_def with
    | None    -> ";"
    | Some(s) ->  " = python "^s^";")

let pp_native ?pp_info ~pp_types fmt (name,fdef) =
  let clean v =
    { v with
      Var.uloc = L.dummy_loc;
      Var.dloc = L.dummy_loc; }
  in
  let decls =
    Set.to_list
      (Set.diff (Set.union
                   (Var.Set.of_list
                      (List.map ~f:clean (Set.to_list (vars_stmt fdef.f_body))))
                   (Var.Set.of_list (List.map ~f:clean fdef.f_ret)))
         (Var.Set.of_list (List.map ~f:clean fdef.f_arg)))
  in
  F.fprintf fmt "@[<v 0>%sfn %a(%a)%a%a@]"
    (string_of_call_conv fdef.f_call_conv)
    Fname.pp name
    (pp_list ", " (pp_var_i ~pp_types)) fdef.f_arg
    (pp_ret_ty ~pp_types) (List.map ~f:tinfo_of_var fdef.f_ret)
    (pp_fundef ?pp_info ~pp_types)
      ( decls
      , fdef.f_body
      , fdef.f_ret
      )

let pp_func ?pp_info ~pp_types fmt nf =
  match nf.nf_func with
  | Foreign(fo)  -> pp_foreign ~pp_types fmt nf.nf_name fo
  | Native(fdef) -> pp_native ?pp_info ~pp_types  fmt (nf.nf_name,fdef)

let pp_param ~pp_types fmt p =
  F.fprintf fmt "param %a : %a;@\n@\n" Param.pp p (pp_ty ~pp_types) p.ty

let pp_modul ?pp_info ~pp_types fmt modul =
  pp_list ""  (pp_param ~pp_types) fmt (Set.to_list @@ params_modul modul);
  pp_list "@\n@\n" (pp_func ?pp_info ~pp_types) fmt modul

let pp_value fmt = function
  | Vu64 u   ->
    pp_uint64 fmt u
  | Varr(vs) ->
    F.fprintf fmt "[%a]" (pp_list "," (pp_pair "->" pp_uint64 pp_uint64))
      (Map.to_alist vs)

let pp_value_py fmt = function
  | Vu64 u   ->
    pp_uint64 fmt u
  | Varr(vs) ->
    F.fprintf fmt "[%a]" (pp_list "," pp_uint64) (List.map ~f:snd (Map.to_alist vs))

let pp_ty_nt = pp_ty ~pp_types:false

let pp_dest_nt = pp_dest ~pp_types:false

let pp_src_nt = pp_src ~pp_types:false
