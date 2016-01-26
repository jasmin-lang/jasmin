(* * Utility functions for intermediate language *)

open Core_kernel.Std
open IL_Lang
open Arith
open Util

module L = ParserUtil.Lexing

(* ** Equality functions and indicator functions
 * ------------------------------------------------------------------------ *)

let dest_to_src d = Src(d)

let equal_pop_u64    x y = compare_pop_u64    x y = 0
let equal_pexpr      x y = compare_pexpr      x y = 0
let equal_dexpr      x y = compare_dexpr      x y = 0
let equal_pop_bool   x y = compare_pop_bool   x y = 0
let equal_pcond      x y = compare_pcond      x y = 0
let equal_cmov_flag  x y = compare_cmov_flag  x y = 0
let equal_op         x y = compare_op         x y = 0
let equal_ty         x y = compare_ty         x y = 0

let equal_src        x y = compare_src        x y = 0
let equal_dest       x y = compare_dest       x y = 0
let equal_base_instr x y = compare_base_instr x y = 0
let equal_instr      x y = compare_instr      x y = 0
let equal_stmt       x y = compare_stmt       x y = 0
let equal_func       x y = compare_func       x y = 0
let equal_fundef     x y = compare_fundef     x y = 0
let equal_modul      x y = compare_modul     x y = 0

let stmt_to_base_instrs st =
  List.map st
    ~f:(function
          | Binstr(i) -> i
          | _ -> failwith "expected macro-expanded statement, got for/if.")

let base_instrs_to_stmt bis =
  List.map ~f:(fun i -> Binstr(i)) bis

let is_src_imm  = function Imm _ -> true | _ -> false

(* ** Collect parameter vars
 * ------------------------------------------------------------------------ *)

let params_patom = function
  | Pparam(s)         -> String.Set.singleton s
  | Pvar(_)           -> String.Set.empty

let rec params_pexpr_g params_atom pe =
  let params_pexpr = params_pexpr_g params_atom in
  match pe with
  | Patom(a)          -> params_atom a
  | Pbinop(_,ce1,ce2) -> Set.union (params_pexpr ce1) (params_pexpr ce2)
  | Pconst _          -> String.Set.empty

let params_pexpr = params_pexpr_g params_patom

let params_dexpr = params_pexpr_g String.Set.singleton

let rec params_pcond = function
  | Ptrue            -> String.Set.empty
  | Pnot(ic)         -> params_pcond ic
  | Pand (ic1,ic2)   -> Set.union (params_pcond ic1) (params_pcond ic2)
  | Pcond(_,ce1,ce2) -> Set.union (params_pexpr ce1) (params_pexpr ce2)

let params_opt f =
  Option.value_map ~default:String.Set.empty ~f:f

let params_ty = function
  | Bool | U64 -> String.Set.empty
  | Arr(dim)   -> params_dexpr dim

let params_dest pr =
  params_opt params_pexpr pr.d_oidx

let params_src = function
  | Imm _ -> String.Set.empty
  | Src d -> params_dest d

let params_op = function
  | ThreeOp(_)       -> String.Set.empty
  | Umul(d1)         -> params_dest d1
  | CMov(_,s)        -> params_src s
  | Shift(_,d1o)     -> params_opt params_dest d1o
  | Carry(_,d1o,s1o) ->
    String.Set.union_list
      [ params_opt params_dest d1o
      ; params_opt params_src s1o
      ]

let params_base_instr = function
  | Comment(_) ->
    String.Set.empty
  | Load(d,s,pe) ->
    String.Set.union (params_pexpr pe)
      (String.Set.union (params_dest d) (params_src s))
  | Store(s1,pe,s2) ->
    String.Set.union (params_pexpr pe)
      (String.Set.union (params_src s1) (params_src s2))
  | Assgn(d,s,_) ->
    String.Set.union (params_dest d) (params_src s)
  | Op(o,d,(s1,s2)) ->
    String.Set.union_list
      [params_op o; params_dest d; params_src s1; params_src s2]
  | Call(_,ds,ss) ->
    String.Set.union_list
     ( (List.map ds ~f:params_dest)
      @(List.map ss ~f:params_src))

let rec params_instr linstr =
  match linstr.L.l_val with
  | Binstr(bi) -> params_base_instr bi
  | If(cond,s1,s2) ->
    String.Set.union_list [params_pcond cond; params_stmt s1; params_stmt s2]
  | For(_,_,pe1,pe2,stmt) ->
    (String.Set.union_list
       [ params_pexpr pe1
       ; params_pexpr pe2
       ; params_stmt stmt ])

and params_stmt stmt =
  String.Set.union_list (List.map stmt ~f:params_instr)

let params_fundef fd =
  String.Set.union
    (String.Set.union_list (List.map fd.fd_decls ~f:(fun (_,_,ty) -> params_ty ty)))
    (params_stmt fd.fd_body)

let params_func func =
  String.Set.union_list
    [ String.Set.union_list (List.map func.f_args ~f:(fun (_,_,ty) -> params_ty ty))
    ; (match func.f_def with
       | Def fdef -> params_fundef fdef
       | _        -> String.Set.empty)
    ; String.Set.union_list (List.map func.f_ret_ty ~f:(fun (_,ty) -> params_ty ty))
    ]

let params_modul modul =
  String.Set.union_list (List.map modul.m_funcs ~f:params_func)

(* ** Collect program variables
 * ------------------------------------------------------------------------ *)

let pvars_patom = function
  | Pparam(_) -> String.Set.empty
  | Pvar(s)   -> String.Set.singleton s

let rec pvars_pexpr_g pvars_atom pe =
  let pvars_pexpr = pvars_pexpr_g pvars_atom in
  match pe with
  | Patom(a)          -> pvars_patom a
  | Pbinop(_,ce1,ce2) -> Set.union (pvars_pexpr ce1) (pvars_pexpr ce2)
  | Pconst _          -> String.Set.empty

let pvars_pexpr = pvars_pexpr_g pvars_patom

let pvars_dexpr de = pvars_pexpr_g String.Set.singleton de

let rec pvars_pcond = function
  | Ptrue            -> String.Set.empty
  | Pnot(ic)         -> pvars_pcond ic
  | Pand (ic1,ic2)   -> Set.union (pvars_pcond ic1) (pvars_pcond ic2)
  | Pcond(_,ce1,ce2) -> Set.union (pvars_pexpr ce1) (pvars_pexpr ce2)

let pvars_opt f =
  Option.value_map ~default:String.Set.empty ~f:f

let pvars_dest d =
  String.Set.union
    (String.Set.singleton d.d_name)
    (pvars_opt pvars_pexpr d.d_oidx)

let pvars_src = function
  | Imm _ -> String.Set.empty
  | Src d -> pvars_dest d

let pvars_op = function
  | ThreeOp(_)       -> String.Set.empty
  | Umul(d1)         -> pvars_dest d1
  | CMov(_,s)        -> pvars_src s
  | Shift(_,d1o)     -> pvars_opt pvars_dest d1o
  | Carry(_,d1o,s1o) ->
    String.Set.union (pvars_opt pvars_dest d1o) (pvars_opt pvars_src s1o)

let pvars_base_instr = function
  | Comment(_)      -> String.Set.empty
  | Load(d,s,pe)    -> String.Set.union_list [pvars_dest d; pvars_src s; pvars_pexpr pe]
  | Store(s1,pe,s2) -> String.Set.union_list [pvars_src s1; pvars_src s2; pvars_pexpr pe]
  | Assgn(d,s,_)    -> String.Set.union (pvars_dest d) (pvars_src s)
  | Op(o,d,(s1,s2)) ->
    String.Set.union_list [pvars_op o; pvars_dest d; pvars_src s1; pvars_src s2]
  | Call(_,ds,ss) ->
    String.Set.union_list (List.map ds ~f:pvars_dest @ List.map ss ~f:pvars_src)

let rec pvars_instr linstr =
  match linstr.L.l_val with
  | Binstr(bi)        -> pvars_base_instr bi
  | If(c,s1,s2)       -> String.Set.union_list [pvars_stmt s1; pvars_stmt s2; pvars_pcond c]
  | For(_,n,lb,ub,stmt) ->
    String.Set.union_list
      [ pvars_stmt stmt
      ; String.Set.singleton n
      ; pvars_pexpr lb
      ; pvars_pexpr ub ]

and pvars_stmt stmt =
  String.Set.union_list (List.map stmt ~f:pvars_instr)

let pvars_fundef fd =
  String.Set.union
    (String.Set.of_list (List.map fd.fd_decls ~f:(fun (_,s,_) -> s)))
    (pvars_stmt fd.fd_body)

let pvars_func func =
  String.Set.union
    (String.Set.of_list (List.map func.f_args ~f:(fun (_,s,_) -> s)))
    ((match func.f_def with
      | Def fdef -> pvars_fundef fdef
      | _        -> String.Set.empty))

let pvars_modul modul =
  String.Set.union_list (List.map modul.m_funcs ~f:pvars_func)

(* ** Rename program variables
 * ------------------------------------------------------------------------ *)

let rename_patom f pa =
  match pa with
 | Pvar(v)   -> Pvar(f v)
 | Pparam(_) -> pa

let rec rename_pexpr_g rename_atom f pe =
  let rename_pexpr = rename_pexpr_g rename_atom in
  match pe with
  | Patom(a)          -> Patom(rename_patom f a)
  | Pbinop(o,pe1,pe2) -> Pbinop(o,rename_pexpr f pe1,rename_pexpr f pe2)
  | Pconst _          -> pe

let rename_pexpr = rename_pexpr_g rename_patom

let rename_dexpr = rename_pexpr_g (fun f -> f)

let rec rename_pcond f = function
  | Ptrue          -> Ptrue 
  | Pnot(c)        -> Pnot(rename_pcond f c)
  | Pand (c1,c2)   -> Pand(rename_pcond f c1,rename_pcond f c2)
  | Pcond(o,e1,e2) -> Pcond(o,rename_pexpr f e1,rename_pexpr f e2)

let rename_opt f =
  Option.map ~f:f

let rename_dest f d =
  { d with
    d_name = f d.d_name;
    d_oidx = Option.map d.d_oidx ~f:(rename_pexpr f)
  }

let rename_src f = function
  | Imm _ as i -> i
  | Src d      -> Src (rename_dest f d)

let rename_op f op =
  let rnd = rename_dest f in
  let rns = rename_src f in
  match op with
  | ThreeOp(_)         -> op
  | Umul(d1)           -> Umul(rnd d1)
  | CMov(cond,s)       -> CMov(cond,rns s)
  | Shift(dir,d1o)     -> Shift(dir,rename_opt rnd d1o)
  | Carry(cop,d1o,s1o) -> Carry(cop,rename_opt rnd d1o, rename_opt rns s1o)

let rename_base_instr f bi =
  let rnd = rename_dest f in
  let rns = rename_src f in
  let rno = rename_op f in
  let rne = rename_pexpr f in
  match bi with
  | Comment(_) as c -> c
  | Load(d,s,pe)    -> Load(rnd d,rns s,rne pe)
  | Store(s1,pe,s2) -> Store(rns s1,rne pe,rns s2)
  | Assgn(d,s,at)   -> Assgn(rnd d,rns s,at)
  | Op(o,d,(s1,s2)) -> Op(rno o,rnd d,(rns s1,rns s2))
  | Call(fn,ds,ss)  -> Call(fn,List.map ~f:rnd ds,List.map ~f:rns ss)

let rec rename_instr f linstr =
  let rne = rename_pexpr f in
  let rnc = rename_pcond f in
  let rnb = rename_base_instr f in
  let rns = rename_stmt f in
  let instr =
    match linstr.L.l_val with
    | Binstr(bi)       -> Binstr(rnb bi)
    | If(c,s1,s2)      -> If(rnc c,rns s1, rns s2)
    | For(t,v,lb,ub,s) -> For(t,f v,rne lb,rne ub,rns s)
  in
  { linstr with L.l_val = instr }

and rename_stmt f stmt =
  List.map stmt ~f:(rename_instr f)

let rename_decls f decls =
  List.map ~f:(fun (sto,n,ty) -> (sto,f n,ty)) decls

(* ** Constructor functions for destinations and located base instructions
 * ------------------------------------------------------------------------ *)

let mk_dest_name name =
  { d_name = name; d_oidx = None; d_loc = L.dummy_loc }

let mk_base_instr loc bi = { L.l_loc = loc; L.l_val = Binstr(bi) }

(* ** Pretty printing
 * ------------------------------------------------------------------------ *)

let pp_add_suffix fs pp fmt x =
  F.fprintf fmt ("%a"^^fs) pp x

let pp_add_prefix fs pp fmt x =
  F.fprintf fmt (fs^^"%a") pp x

let pbinop_to_string = function
  | Pplus  -> "+"
  | Pmult  -> "*"
  | Pminus -> "-"

let pp_patom fmt pa =
  match pa with
  | Pparam(s) -> F.fprintf fmt "$%s" s
  | Pvar(s)   -> pp_string fmt s

let rec pp_pexpr_g pp_atom fmt ce =
  let pp_pexpr = pp_pexpr_g pp_atom in
  match ce with
  | Patom(pa) ->
    pp_atom fmt pa
  | Pbinop(op,ie1,ie2) ->
    F.fprintf fmt "%a %s %a" pp_pexpr ie1 (pbinop_to_string op) pp_pexpr ie2
  | Pconst(u) ->
    pp_string fmt (U64.to_string u)

let pp_pexpr = pp_pexpr_g pp_patom

let pp_dexpr = pp_pexpr_g pp_string

let pcondop_to_string = function
  | Peq      -> "="
  | Pineq    -> "!="
  | Pless    -> "<"
  | Pleq     -> "<="
  | Pgreater -> ">"
  | Pgeq     -> ">="

let rec pp_pcond fmt = function
  | Ptrue            -> pp_string fmt "true"
  | Pnot(ic)         -> F.fprintf fmt"!(%a)" pp_pcond ic
  | Pand(c1,c2)      -> F.fprintf fmt"(%a && %a)" pp_pcond c1 pp_pcond c2
  | Pcond(o,ie1,ie2) -> F.fprintf fmt"(%a %s %a)" pp_pexpr ie1 (pcondop_to_string o) pp_pexpr ie2

let pp_dest fmt {d_name=r; d_oidx=oidx} =
  match oidx with
  | None      -> F.fprintf fmt "%s" r
  | Some(idx) -> F.fprintf fmt "%s[%a]" r pp_pexpr idx

let pp_src fmt = function
  | Src(d)  -> pp_dest fmt d
  | Imm(pe) -> pp_pexpr fmt pe

let pp_ty fmt ty =
  match ty with
  | Bool     -> F.fprintf fmt "bool"
  | U64      -> F.fprintf fmt "u64"
  | Arr(dim) -> F.fprintf fmt "u64[%a]" pp_dexpr dim

let string_of_carry_op = function O_Add -> "+" | O_Sub -> "-"

let pp_three_op fmt o =
  pp_string fmt
    (match o with
     | O_Imul -> "*"
     | O_And  -> "&"
     | O_Xor  -> "^"
     | O_Or   -> "|")

let pp_op fmt (o,d,s1,s2) =
  match o with
  | Umul(d1) ->
    F.fprintf fmt "%a, %a = %a * %a" pp_dest d1 pp_dest d pp_src s1 pp_src s2
  | ThreeOp(o) ->
    F.fprintf fmt "%a = %a %a %a" pp_dest d pp_src s1 pp_three_op o pp_src s2
  | Carry(cfo,od1,os3) ->
    let so = string_of_carry_op cfo in
    F.fprintf fmt "%a%a = %a %s %a%a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a, " pp_dest d
         | None   -> pp_string fmt "")
      od1
      pp_dest d
      pp_src s1
      so
      pp_src s2
      (fun fmt os ->
         match os with
         | Some s -> F.fprintf fmt " %s %a" so pp_src s
         | None   -> pp_string fmt "")
      os3
  | CMov(CfSet(is_set),s3) ->
    F.fprintf fmt "%a = %a if %s%a else %a"
      pp_dest d pp_src s2 (if is_set then "" else "!") pp_src s3 pp_src s1
  | Shift(dir,od1) ->
    F.fprintf fmt "%a%a = %a %s %a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a" pp_dest d
         | None   -> pp_string fmt "")
      od1
      pp_dest d
      pp_src s1
      (match dir with Left -> "<<" | Right -> ">>")
      pp_src s2

let pp_base_instr fmt bi =
  match bi with
  | Comment(s)      -> F.fprintf fmt "/* %s */" s
  | Load(d,s,pe)    -> F.fprintf fmt "%a = MEM[%a + %a];" pp_dest d pp_src s pp_pexpr pe
  | Store(s1,pe,s2) -> F.fprintf fmt "MEM[%a + %a] = %a;" pp_src s1 pp_pexpr pe pp_src s2
  | Assgn(d1,s1,Mv) -> F.fprintf fmt "%a = %a;" pp_dest d1 pp_src s1
  | Assgn(d1,s1,Eq) -> F.fprintf fmt "%a := %a;" pp_dest d1 pp_src s1
  | Op(o,d,(s1,s2)) -> F.fprintf fmt "%a;" pp_op (o,d,s1,s2)
  | Call(name,[],args) ->
    F.fprintf fmt "%s(%a);" name (pp_list "," pp_src) args
  | Call(name,dest,args) ->
    F.fprintf fmt "%a = %s(%a);"
      (pp_list "," pp_dest) dest
      name
      (pp_list "," pp_src) args

let rec pp_instr fmt li =
  match li.L.l_val with
  | Binstr(i) -> pp_base_instr fmt i
  | If(c,i1,i2) ->
    F.fprintf fmt "if %a {@\n  @[<v 0>%a@]@\n} else {@\n  @[<v 0>%a@]@\n}"
      pp_pcond c pp_stmt i1 pp_stmt i2
  | For(t,iv,ie1,ie2,i) ->
    F.fprintf fmt "for%s %s in %a..%a {@\n  @[<v 0>%a@]@\n}"
      (if t=Loop then ":" else "") iv pp_pexpr ie1 pp_pexpr ie2 pp_stmt i

and pp_stmt fmt is =
  F.fprintf fmt "%a" (pp_list "@\n" pp_instr) is

let pp_return fmt names =
  match names with
  | [] -> pp_string fmt ""
  | _  -> F.fprintf fmt "@\nreturn %a;" (pp_list "," pp_string) names

let string_of_storage = function
  | Stack  -> "stack"
  | Reg    -> "reg"
  | Flag   -> "flag"
  | Inline -> "inline"

let pp_decl fmt (stor,name,ty) =
  F.fprintf fmt "%s %s : %a;"
    (string_of_storage stor)
    name
    pp_ty ty

let pp_fundef fmt fd =
  F.fprintf fmt  " {@\n  @[<v 0>%a%a%a%a@]@\n}"
    (pp_list "@\n" pp_decl) fd.fd_decls
    (fun fmt xs -> match xs with
     | [] -> F.fprintf fmt ""
     | _ -> F.fprintf fmt "@\n") fd.fd_decls
    pp_stmt    fd.fd_body
    pp_return  fd.fd_ret

let call_conv_to_string = function
  | Extern -> "extern "
  | _      -> ""

let pp_decl fmt (sto,name,ty) =
  F.fprintf fmt "%s %s : %a" (string_of_storage sto) name pp_ty ty

let pp_ret fmt (sto,ty) =
  F.fprintf fmt "%s %a" (string_of_storage sto) pp_ty ty

let pp_func fmt f =
  F.fprintf fmt "@[<v 0>%sfn %s(%a)%s%a@]"
    (call_conv_to_string f.f_call_conv)
    f.f_name
    (pp_list "," pp_decl) f.f_args
    (if f.f_ret_ty=[] then ""
     else fsprintf " -> %a" (pp_list "*" pp_ret) f.f_ret_ty)
    (fun fmt ef_def -> match ef_def with
     | Undef  -> pp_string fmt ";"
     | Def ed -> pp_fundef fmt ed
     | Py s   -> F.fprintf fmt " = python %s" s)
    f.f_def

let pp_modul fmt modul =
  pp_list "@\n@\n" pp_func fmt modul.m_funcs

let pp_value fmt = function
  | Vu64 u   ->
    pp_uint64 fmt u
  | Varr(vs) ->
    F.fprintf fmt "[%a]" (pp_list "," (pp_pair "->" pp_uint64 pp_uint64)) (Map.to_alist vs)

let pp_value_py fmt = function
  | Vu64 u   ->
    pp_uint64 fmt u
  | Varr(vs) ->
    F.fprintf fmt "[%a]" (pp_list "," pp_uint64) (List.map ~f:snd (Map.to_alist vs))

(* ** Utility functions
 * ------------------------------------------------------------------------ *)

let parse_value s =
  let open MParser in
  let u64 =
    many1 digit >>= fun s ->
    optional (char 'L') >>
    return (U64.of_string (String.of_char_list s))
  in
  let value =
    choice
      [ (u64 >>= fun u -> return (Vu64 u))
      ; (char '[' >>= fun _ ->
        (sep_by u64 (char ',' >> optional (char ' '))) >>= fun vs ->
        char ']' >>= fun _ ->
        let vs = U64.Map.of_alist_exn (List.mapi vs ~f:(fun i v -> (U64.of_int i, v))) in
        return (Varr(vs))) ]
  in
  match parse_string (value >>= fun x -> eof >>$ x) s () with
  | Success t   -> t
  | Failed(s,_) -> failwith_ "parse_value: failed for %s" s

(* ** Exceptions
 * ------------------------------------------------------------------------ *)

exception TypeError of L.loc * string

let failtype loc s = raise (TypeError(loc,s))

let failtype_ loc fmt =
  let buf  = Buffer.create 127 in
  let fbuf = F.formatter_of_buffer buf in
  F.kfprintf
    (fun _ ->
      F.pp_print_flush fbuf ();
      let s = Buffer.contents buf in
      failtype loc s)
    fbuf fmt

