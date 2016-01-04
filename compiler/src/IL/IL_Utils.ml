(* * Utility functions for intermediate language *)

open Core_kernel.Std
open IL_Lang
open Arith
open Util

(* ** Equality functions and indicator functions
 * ------------------------------------------------------------------------ *)

let dest_to_src d = Src(d)

let equal_pop_u64    x y = compare_pop_u64    x y = 0
let equal_pexpr      x y = compare_pexpr      x y = 0
let equal_pop_bool   x y = compare_pop_bool   x y = 0
let equal_pcond      x y = compare_pcond      x y = 0
let equal_cmov_flag  x y = compare_cmov_flag  x y = 0
let equal_op         x y = compare_op         x y = 0
let equal_ty         x y = compare_ty         x y = 0

let equal_preg       x y = compare_preg       x y = 0
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

(* ** Collect pvars
 * ------------------------------------------------------------------------ *)

let rec pvars_pexpr = function
  | Pvar(s)           -> String.Set.singleton s
  | Pbinop(_,ce1,ce2) -> Set.union (pvars_pexpr ce1) (pvars_pexpr ce2)
  | Pconst _          -> String.Set.empty

let rec pvars_pcond = function
  | Ptrue            -> String.Set.empty
  | Pnot(ic)         -> pvars_pcond ic
  | Pand (ic1,ic2)   -> Set.union (pvars_pcond ic1) (pvars_pcond ic2)
  | Pcond(_,ce1,ce2) -> Set.union (pvars_pexpr ce1) (pvars_pexpr ce2)

let pvars_ty = function
  | Bool           -> String.Set.empty
  | U64(pes1,pes2) -> String.Set.union_list (List.map (pes1@pes2) ~f:pvars_pexpr)

let pvars_opt f =
  Option.value_map ~default:String.Set.empty ~f:f

let pvars_get_or_range = function
  | Get(pe)          -> pvars_pexpr pe
  | All(pe1_o,pe2_o) ->
    let to_set = pvars_opt pvars_pexpr in
    Set.union (to_set pe1_o) (to_set pe2_o)

let pvars_preg_g pvars_g pr =
  String.Set.union_list (List.map pr.pr_idxs ~f:pvars_g)

let pvars_dest_g pvars_g d =
  String.Set.union
    (pvars_preg_g pvars_g d.d_pr)
    (String.Set.union_list (List.map d.d_aidxs ~f:pvars_g))

let pvars_src_g pvars_g = function
  | Imm _ -> String.Set.empty
  | Src d -> pvars_dest_g pvars_g d

let pvars_dest_e = pvars_dest_g pvars_pexpr
let pvars_dest = pvars_dest_g pvars_get_or_range

let pvars_src_e = pvars_src_g pvars_pexpr
let pvars_src = pvars_src_g pvars_get_or_range

let pvars_op = function
  | ThreeOp(_)       -> String.Set.empty
  | Umul(d1)         -> pvars_dest_e d1
  | CMov(_,s)        -> pvars_src_e s
  | Shift(_,d1o)     -> pvars_opt pvars_dest_e d1o
  | Carry(_,d1o,s1o) ->
    String.Set.union_list
      [ pvars_opt pvars_dest_e d1o
      ; pvars_opt pvars_src_e s1o
      ]

let pvars_base_instr_g pvars_g = function
  | Comment(_) ->
    String.Set.empty
  | Assgn(d,s) ->
    String.Set.union (pvars_dest_g pvars_g d) (pvars_src_g pvars_g s)
  | Op(o,d,(s1,s2)) ->
    String.Set.union_list
      [pvars_op o; pvars_dest_e d; pvars_src_e s1; pvars_src_e s2]
  | Call(_,ds,ss) ->
    String.Set.union_list
     ( (List.map ds ~f:(pvars_dest_g pvars_g))
      @(List.map ss ~f:(pvars_src_g pvars_g)))
    
let rec pvars_instr_g pvars_g = function
  | Binstr(bi) -> pvars_base_instr_g pvars_g bi
  | If(cond,s1,s2) ->
    String.Set.union_list
      [pvars_pcond cond; pvars_stmt_g pvars_g s1; pvars_stmt_g pvars_g s2]
  | For(pv,pe1,pe2,stmt) ->
    Set.diff
      (String.Set.union_list
         [ pvars_pexpr pe1
         ; pvars_pexpr pe2
         ; pvars_stmt_g pvars_g stmt ])
      (String.Set.singleton pv)

and pvars_stmt_g pvars_g stmt =
  String.Set.union_list
    (List.map stmt ~f:(pvars_instr_g pvars_g))

let pvars_fundef pvars_g fd =
  String.Set.union_list
    [ String.Set.union_list
        (List.map fd.fd_decls ~f:(fun (_,ty) -> pvars_ty ty))
    ; pvars_stmt_g pvars_g fd.fd_body
    ; String.Set.union_list
        (List.map fd.fd_ret ~f:(pvars_preg_g pvars_g))
    ]

let pvars_func pvars_g func =
  String.Set.union_list
    [ String.Set.union_list
        (List.map func.f_args ~f:(fun (_,ty) -> pvars_ty ty))
    ; (match func.f_def with
       | Def fdef -> pvars_fundef pvars_g fdef 
       | _ -> String.Set.empty)
    ; String.Set.union_list
        (List.map func.f_ret_ty ~f:pvars_ty)
    ]

let pvars_modul pvars_g modul =
  String.Set.union_list
    (List.map modul.m_funcs ~f:(pvars_func pvars_g))

(* ** Constructor functions for pregs
 * ------------------------------------------------------------------------ *)

let mk_preg_name name =
  { pr_name = name; pr_idxs = []; pr_loc = P.dummy_loc }

let mk_preg_index name i =
  { pr_name = name; pr_idxs = [Get (Pconst i)]; pr_loc = P.dummy_loc }

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

let rec pp_pexpr fmt ce =
  match ce with
  | Pvar(s) ->
    pp_string fmt s
  | Pbinop(op,ie1,ie2) ->
    F.fprintf fmt "%a %s %a" pp_pexpr ie1 (pbinop_to_string op) pp_pexpr ie2
  | Pconst(u) ->
    pp_string fmt (U64.to_string u)

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

let pp_get_or_all fmt = function
  | Get i      -> pp_pexpr fmt i
  | All(lb,ub) -> F.fprintf fmt "%a..%a" (pp_opt "" pp_pexpr) lb (pp_opt "" pp_pexpr) ub

let pp_preg_g pp_index fmt {pr_name=r; pr_idxs=ies} =
  match ies with
  | []  -> F.fprintf fmt "%s" r
  | ies -> F.fprintf fmt "%s<%a>" r (pp_list "," pp_index) ies

let pp_dest_g pp_index fmt d =
  if d.d_aidxs = []
  then pp_preg_g pp_index fmt d.d_pr
  else F.fprintf fmt "%a[%a]" (pp_preg_g pp_index) d.d_pr (pp_list "," pp_index) d.d_aidxs

let pp_src_g pp_index fmt = function
  | Src(d)  -> pp_dest_g pp_index fmt d
  | Imm(pe) -> pp_pexpr fmt pe

let pp_ty fmt ty =
  match ty with
  | Bool            -> F.fprintf fmt "bool"
  | U64(idxs,dims)  ->
    F.fprintf fmt "u64%a%a"
      (fun fmt idxs ->
         match idxs with
         | [] -> F.fprintf fmt ""
         | _  -> F.fprintf fmt "<%a>" (pp_list "," pp_pexpr) idxs) idxs
      (fun fmt dims ->
         match dims with
         | [] -> F.fprintf fmt ""
         | _  -> F.fprintf fmt "[%a]" (pp_list "," pp_pexpr) dims) dims

let string_of_carry_op = function O_Add -> "+" | O_Sub -> "-"

let pp_op fmt (o,d,s1,s2) =
  let pp_dest_e = pp_dest_g pp_pexpr in
  let pp_src_e = pp_src_g pp_pexpr in
  match o with
  | Umul(d1) ->
    F.fprintf fmt "%a, %a = %a * %a" pp_dest_e d1 pp_dest_e d pp_src_e s1 pp_src_e s2
  | ThreeOp(O_Imul) ->
    F.fprintf fmt "%a = %a * %a" pp_dest_e d pp_src_e s1 pp_src_e s2
  | ThreeOp(O_And) ->
    F.fprintf fmt "%a = %a & %a" pp_dest_e d pp_src_e s1 pp_src_e s2
  | ThreeOp(O_Xor) ->
    F.fprintf fmt "%a = %a ^ %a" pp_dest_e d pp_src_e s1 pp_src_e s2
  | Carry(cfo,od1,os3) ->
    let so = string_of_carry_op cfo in
    F.fprintf fmt "%a%a = %a %s %a%a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a, " pp_dest_e d 
         | None   -> pp_string fmt "")
      od1
      pp_dest_e d
      pp_src_e s1
      so
      pp_src_e s2
      (fun fmt os ->
         match os with
         | Some s -> F.fprintf fmt " %s %a" so pp_src_e s
         | None   -> pp_string fmt "")
      os3
  | CMov(CfSet(is_set),s3) ->
    F.fprintf fmt "%a = %a if %s%a else %a"
      pp_dest_e d pp_src_e s2 (if is_set then "" else "!") pp_src_e s3 pp_src_e s1
  | Shift(dir,od1) ->
    F.fprintf fmt "%a%a = %a %s %a"
      (fun fmt od ->
         match od with
         | Some d -> F.fprintf fmt "%a" pp_dest_e d 
         | None   -> pp_string fmt "")
      od1
      pp_dest_e d
      pp_src_e s1
      (match dir with Left -> "<<" | Right -> ">>")
      pp_src_e s2

let pp_base_instr_g pp_index fmt bi =
  let pp_dest = pp_dest_g pp_index in
  let pp_src = pp_src_g pp_index in
  match bi with
  | Comment(s)      -> F.fprintf fmt "/* %s */" s
  | Assgn(d1,s1)    -> F.fprintf fmt "%a = %a;" pp_dest d1 pp_src s1
  | Op(o,d,(s1,s2)) -> F.fprintf fmt "%a;" pp_op (o,d,s1,s2)
  | Call(name,[],args) ->
    F.fprintf fmt "%s(%a);" name (pp_list "," pp_src) args
  | Call(name,dest,args) ->
    F.fprintf fmt "%a = %s(%a);"
      (pp_list "," pp_dest) dest
      name
      (pp_list "," pp_src) args

let rec pp_instr_g pp_index fmt bi =
  let pp_stmt = pp_stmt_g pp_index in
  match bi with
  | Binstr(i) -> pp_base_instr_g pp_index fmt i
  | If(c,i1,i2) ->
    F.fprintf fmt "if %a {@\n  @[<hv 0>%a@]@\n} else {@\n  @[<v 0>%a@]@\n}"
      pp_pcond c pp_stmt i1 pp_stmt i2
  | For(iv,ie1,ie2,i) ->
    F.fprintf fmt "for %s in %a..%a {@\n  @[<v 0>%a@]@\n}"
      iv pp_pexpr ie1 pp_pexpr ie2 pp_stmt i

and pp_stmt_g pp_index fmt is =
  F.fprintf fmt "%a" (pp_list "@\n" (pp_instr_g pp_index)) is

let pp_return_g pp_index fmt names =
  match names with
  | [] -> pp_string fmt ""
  | _  -> F.fprintf fmt "@\nreturn %a;" (pp_list "," (pp_preg_g pp_index)) names

let pp_decl fmt (name,ty) =
  F.fprintf fmt "%s %s : %a;"
    (match ty with
     | Bool -> "flag"
     | _    -> "reg")
    name
    pp_ty ty

let pp_fundef_g pp_index fmt fd =
  F.fprintf fmt  " {@\n  @[<v 0>%a%a%a@]@\n}"
    (pp_list "@\n" pp_decl) fd.fd_decls
    (pp_stmt_g pp_index)    fd.fd_body
    (pp_return_g pp_index)  fd.fd_ret

let call_conv_to_string = function
  | Extern -> "extern "
  | _      -> ""

let pp_func_g pp_index fmt f =
  F.fprintf fmt "@[<v 0>fn %s%s(%a)%s%a@]"
            (call_conv_to_string f.f_call_conv)
    f.f_name
    (pp_list "," (pp_pair ":" pp_string pp_ty)) f.f_args
    (if f.f_ret_ty=[] then ""
     else fsprintf " -> %a" (pp_list "*" pp_ty) f.f_ret_ty)
    (fun fmt ef_def -> match ef_def with
     | Undef  -> pp_string fmt ";"
     | Def ed -> pp_fundef_g pp_index fmt ed
     | Py s   -> F.fprintf fmt " = python %s" s)
    f.f_def

let pp_modul_g pp_index fmt modul =
  pp_list "@\n@\n" (pp_func_g pp_index) fmt modul.m_funcs

let pp_indexed_name fmt (s,idxs) =
  F.fprintf fmt "%s<%a>" s (pp_list "," pp_uint64) idxs

let rec pp_value fmt = function
  | Vu64 u   ->
    pp_uint64 fmt u
  | Varr(vs) ->
    F.fprintf fmt "[%a]" (pp_list "," (pp_pair "->" pp_uint64 pp_value)) (Map.to_alist vs)


let rec pp_value_py fmt = function
  | Vu64 u   ->
    pp_uint64 fmt u
  | Varr(vs) ->
    F.fprintf fmt "[%a]" (pp_list "," pp_value_py) (List.map ~f:snd (Map.to_alist vs))

(* ** Specialized pretty printing functions
 * ------------------------------------------------------------------------ *)

let pp_preg   fmt = pp_preg_g pp_get_or_all fmt
let pp_preg_e fmt = pp_preg_g pp_pexpr      fmt

let pp_func   fmt = pp_func_g pp_get_or_all fmt
let pp_func_e fmt = pp_func_g pp_pexpr      fmt

let pp_src   fmt = pp_src_g pp_get_or_all fmt
let pp_src_e fmt = pp_src_g pp_pexpr      fmt

let pp_dest   fmt = pp_dest_g pp_get_or_all fmt
let pp_dest_e fmt = pp_dest_g pp_pexpr      fmt

let pp_instr   fmt = pp_instr_g pp_get_or_all fmt
let pp_instr_e fmt = pp_instr_g pp_pexpr      fmt

let pp_modul   fmt = pp_modul_g pp_get_or_all fmt
let pp_modul_e fmt = pp_modul_g pp_pexpr      fmt

(* ** Utility functions
 * ------------------------------------------------------------------------ *)

let preg_error pr s =
  failwith (fsprintf "%a: %s" P.pp_loc pr.pr_loc s)

let shorten_func _n _func =
  assert false (*
  let fdef = Option.value_exn func.f_def in
  if List.length fdef.fd_body <= n then func
  else
    { func with
      f_def = Some
        { fdef with
          fd_body = List.take fdef.fd_body n;
          fd_ret  = [] };
      f_ret_ty = [] }
  *)

let parse_value s =
  let open MParser in
  let u64 =
    many1 digit >>= fun s ->
    optional (char 'L') >>
    return (U64.of_string (String.of_char_list s))
  in
  let rec value () =
    choice
      [ (u64 >>= fun u -> return (Vu64 u))
      ; (char '[' >>= fun _ ->
        (sep_by (value ()) (char ',' >> optional (char ' '))) >>= fun vs ->
        char ']' >>= fun _ ->
        let vs = U64.Map.of_alist_exn (List.mapi vs ~f:(fun i v -> (U64.of_int i, v))) in
        return (Varr(vs))) ]
  in
  match parse_string (value () >>= fun x -> eof >>$ x) s () with
  | Success t   -> t
  | Failed(s,_) ->
    failwith_ "parse_value: failed for %s" s

(* ** Utility functions for parser
 * ------------------------------------------------------------------------ *)

type decl = Dfun of func | Dparams of (string * ty) list

let mk_modul pfs =
  let params =
    List.filter_map ~f:(function Dparams(ps) -> Some ps | _ -> None) pfs
    |> List.concat
  in
  let funcs =
    List.filter_map ~f:(function Dfun(func) -> Some func | _ -> None) pfs
  in
  { m_funcs = funcs; m_params = params }

let fix_indexes (cstart,cend) idxs =
  List.filter_map idxs
    ~f:(function
          | Get i -> Some i
          | All(_,_) ->
            let scnum = cstart.Lexing.pos_cnum + 1 in
            let ecnum = cend.Lexing.pos_cnum + 1 in
            let err = "range not allowed here" in
            raise (ParserUtil.UParserError(scnum,ecnum,err)))

let pr_e_of_pr pos pr =
  { pr with pr_idxs = fix_indexes pos pr.pr_idxs }

let dest_e_of_dest pos d  =
  let pr = pr_e_of_pr pos d.d_pr in
  { d_pr = pr; d_aidxs = fix_indexes pos d.d_aidxs }

let src_e_of_src pos s =
  match s with
  | Imm(i) -> Imm(i)
  | Src(d) -> Src(dest_e_of_dest pos d)

let failpos _pos msg = (* FIXME: use position in error message here *)
  failwith msg

let mk_fundef decls stmt rets =
  let rets = Option.value ~default:[] rets in
  { fd_ret = rets;
    fd_decls  = List.concat decls;
    fd_body   = get_opt [] stmt;
  }

let mk_func startpos endpos rty name ext args (def : get_or_range fundef_or_py) : func =
  let rtys = Option.value ~default:[] rty in
  let () =
    match def with
    | Undef | Py _ -> ()
    | Def d -> 
      if List.length d.fd_ret <> List.length rtys then (
        let c_start = startpos.Lexing.pos_cnum + 1 in
        let c_end   = endpos.Lexing.pos_cnum + 1 in
        let err = "mismatch between return type and return statement" in
        raise (ParserUtil.UParserError(c_start,c_end,err))
      );
  in
  {
    f_name      = name;
    f_call_conv = if ext=None then Custom else Extern;
    f_args      = List.concat args;
    f_def       = def;
    f_ret_ty    = rtys }

let mk_if c i1s mi2s ies = 
  let ielse =
    List.fold
      ~init:(get_opt [] mi2s)
      ~f:(fun celse (c,bi) -> [If(c,bi,celse)])
      (List.rev ies)
  in
  If(c,i1s,ielse)

let mk_ternop pos (dests : get_or_range dest_g list) op op2 s1 s2 s3 =
  let fail = failpos pos in
  if op<>op2 then fail "operators must be equal";
  let d, dests = match List.rev dests with
    | d::others -> dest_e_of_dest pos d, List.rev others
    | []        -> fail "impossible"
  in
  let s1 = src_e_of_src pos s1 in
  let s2 = src_e_of_src pos s2 in
  let s3 = Option.map ~f:(src_e_of_src pos) s3 in
  let get_one_dest s dests = match dests with
    | []   -> None
    | [d1] -> Some (dest_e_of_dest pos d1)
    | _    -> fail ("invalid args for "^s)
  in
  match op with
  | (`Add | `Sub) as op ->
    let op = match op with `Add -> O_Add | `Sub -> O_Sub in
    let d1 = get_one_dest "add/sub" dests in
    Op(Carry(op,d1,s3),d,(s1,s2))

  | (`And | `Xor) as op  ->
    if dests<>[] then fail "invalid destination for and/xor";
    let op = match op with `And -> O_And | `Xor -> O_Xor in
    Op(ThreeOp(op),d,(s1,s2))

  | `Shift(dir) ->
    let d1 = get_one_dest "shift" dests in
    Op(Shift(dir,d1),d,(s1,s2))

  | `Mul ->
    begin match dests with
    | []   -> Op(ThreeOp(O_Imul),d,(s1,s2))
    | [d1] -> Op(Umul(dest_e_of_dest pos d1),d,(s1,s2))
    | _    -> fail "invalid args for mult"
    end

let mk_cmov pos (dests : get_or_range dest_g list) s cf flg =
  let s = src_e_of_src pos s in
  let cf = src_e_of_src pos cf in
  let d = match dests with
    | [d] -> d
    | _   -> failpos pos "invalid destination for and/xor"
  in
  Op(CMov(flg,cf),dest_e_of_dest pos d,(Src(dest_e_of_dest pos d),s))

let mk_instr (dests : get_or_range dest_g list) (rhs,pos) : instr =
  match dests, rhs with
  | _,   `Call(fname,args)          -> Binstr(Call(fname,dests,args))
  | [d], `Assgn(src)                -> Binstr(Assgn(d,src))
  | _,   `BinOp(o,s1,s2)            -> Binstr(mk_ternop pos dests o  o  s1 s2 None)
  | _,   `TernaryOp(o1,o2,s1,s2,s3) -> Binstr(mk_ternop pos dests o1 o2 s1 s2 (Some s3))
  | _,   `Cmov(s,cf,flg)            -> Binstr(mk_cmov pos dests s cf flg)
  | _,   `Assgn(_)                  -> failpos pos "assignment expects exactly one destination"
