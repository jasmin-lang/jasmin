open Utils
open Wsize
open Prog
open PrintCommon
module E = Expr

let pp_option pp fmt = function
    | Some x -> pp fmt x
    | None -> ()

let pp_list_paren sep pp fmt xs =
    if xs = [] then ()
    else pp_paren (pp_list sep pp) fmt xs

let pp_Tsz sz = Format.asprintf "W%i" (int_of_ws sz)

let pp_sz_t sz = Format.sprintf "W%i.t" (int_of_ws sz)

module Scmp = struct
  type t = string
  let compare = compare
end

module Ss = Set.Make(Scmp)
module Ms = Map.Make(Scmp)

module Tcmp = struct 
  type t = ty 
  let compare = compare 
end

module Mty = Map.Make (Tcmp)

type env = {
    pd : Wsize.wsize;
    model : model;
    alls : Ss.t;
    vars : string Mv.t;
    glob : (string * ty) Ms.t;
    funs : (string * (ty list * ty list)) Mf.t;  
    arrsz  : Sint.t ref;
    warrsz : Sint.t ref;
    auxv  : string list Mty.t;
    randombytes : Sint.t ref;
  }

(* ------------------------------------------------------------------- *)
let add_ptr pd x e = 
  (Prog.tu pd, Papp2 (E.Oadd ( E.Op_w pd), Pvar x, e))

let int_of_word ws e = 
  Papp1 (E.Oint_of_word ws, e)

let rec leaks_e_rec pd leaks e =
  match e with
  | Pconst _ | Pbool _ | Parr_init _ |Pvar _ -> leaks
  | Pload (_,_,x,e) -> leaks_e_rec pd (int_of_word pd (snd (add_ptr pd (gkvar x) e)) :: leaks) e
  | Pget (_,_,_,_, e) | Psub (_,_,_,_,e) -> leaks_e_rec pd (e::leaks) e
  | Papp1 (_, e) -> leaks_e_rec pd leaks e
  | Papp2 (_, e1, e2) -> leaks_e_rec pd (leaks_e_rec pd leaks e1) e2
  | PappN (_, es) -> leaks_es_rec pd leaks es
  | Pif  (_, e1, e2, e3) -> leaks_e_rec pd (leaks_e_rec pd (leaks_e_rec pd leaks e1) e2) e3
and leaks_es_rec pd leaks es = List.fold_left (leaks_e_rec pd) leaks es

let leaks_e pd e = leaks_e_rec pd [] e
let leaks_es pd es = leaks_es_rec pd [] es

let leaks_lval pd = function
  | Lnone _ | Lvar _ -> []
  | Laset (_,_,_,_, e) | Lasub (_,_,_,_,e) -> leaks_e_rec pd [e] e
  | Lmem (_, _, x,e) -> leaks_e_rec pd [int_of_word pd (snd (add_ptr pd (gkvar x) e))] e

(* FIXME: generate this list automatically *)
(* Adapted from EasyCrypt source file src/ecLexer.mll *)
let ec_keyword = 
 [ "admit"
 ; "admitted"

 ; "forall"
 ; "exists"
 ; "fun"
 ; "glob"
 ; "let"
 ; "in"
 ; "for"
 ; "var"
 ; "proc"
 ; "if"
 ; "is"
 ; "match"
 ; "then"
 ; "else"
 ; "elif"
 ; "match"
 ; "for"
 ; "while"
 ; "assert"
 ; "return"
 ; "res"
 ; "equiv"
 ; "hoare"
 ; "ehoare"
 ; "phoare"
 ; "islossless"
 ; "async"

 ; "try"
 ; "first"
 ; "last"
 ; "do"
 ; "expect"

 (* Lambda tactics *)
 ; "beta"
 ; "iota"
 ; "zeta"
 ; "eta"
 ; "logic"
 ; "delta"
 ; "simplify"
 ; "cbv"
 ; "congr"

 (* Logic tactics *)
 ; "change"
 ; "split"
 ; "left"
 ; "right"
 ; "case"

 ; "pose"
 ; "gen"
 ; "have"
 ; "suff"
 ; "elim"
 ; "exlim"
 ; "ecall"
 ; "clear"
 ; "wlog"

 (* Auto tactics *)
 ; "apply"
 ; "rewrite"
 ; "rwnormal"
 ; "subst"
 ; "progress"
 ; "trivial"
 ; "auto"

 (* Other tactics *)
 ; "idtac"
 ; "move"
 ; "modpath"
 ; "field"
 ; "fieldeq"
 ; "ring"
 ; "ringeq"
 ; "algebra"

 ; "exact"
 ; "assumption"
 ; "smt"
 ; "coq"
 ; "check"
 ; "edit"
 ; "fix"
 ; "by"
 ; "reflexivity"
 ; "done"
 ; "solve"

 (* PHL: tactics *)
 ; "replace"
 ; "transitivity"
 ; "symmetry"
 ; "seq"
 ; "wp"
 ; "sp"
 ; "sim"
 ; "skip"
 ; "call"
 ; "rcondt"
 ; "rcondf"
 ; "swap"
 ; "cfold"
 ; "rnd"
 ; "rndsem"
 ; "pr_bounded"
 ; "bypr"
 ; "byphoare"
 ; "byehoare"
 ; "byequiv"
 ; "byupto"
 ; "fel"

 ; "conseq"
 ; "exfalso"
 ; "inline"
 ; "outline"
 ; "interleave"
 ; "alias"
 ; "weakmem"
 ; "fission"
 ; "fusion"
 ; "unroll"
 ; "splitwhile"
 ; "kill"
 ; "eager"

 ; "axiom"
 ; "axiomatized"
 ; "lemma"
 ; "realize"
 ; "proof"
 ; "qed"
 ; "abort"
 ; "goal"
 ; "end"
 ; "from"
 ; "import"
 ; "export"
 ; "include"
 ; "local"
 ; "declare"
 ; "hint"
 ; "module"
 ; "of"
 ; "const"
 ; "op"
 ; "pred"
 ; "inductive"
 ; "notation"
 ; "abbrev"
 ; "require"
 ; "theory"
 ; "abstract"
 ; "section"
 ; "type"
 ; "class"
 ; "instance"
 ; "print"
 ; "search"
 ; "locate"
 ; "as"
 ; "Pr"
 ; "clone"
 ; "with"
 ; "rename"
 ; "prover"
 ; "timeout"
 ; "why3"
 ; "dump"
 ; "remove"
 ; "exit"

 ; "fail"
 ; "time"
 ; "undo"
 ; "debug"
 ; "pragma"

 ; "Top"
 ; "Self" ]

let syscall_mod_arg = "SC"
let syscall_mod_sig = "Syscall_t"
let syscall_mod     = "Syscall"
let internal_keyword = 
  [ "safe"; "leakages"; syscall_mod_arg; syscall_mod_sig; syscall_mod ]

let keywords = 
  Ss.union (Ss.of_list ec_keyword) (Ss.of_list internal_keyword)

let create_name env s = 
  if not (Ss.mem s env.alls) then s
  else
    let rec aux i = 
      let s = Format.sprintf "%s_%i" s i in
      if Ss.mem s env.alls then aux (i+1)
      else s in
    aux 0

let normalize_name n =
  n |> String.uncapitalize_ascii |> escape

let mkfunname env fn =
  fn.fn_name |> normalize_name |> create_name env

let empty_env pd model fds arrsz warrsz randombytes =

  let env = { 
    pd;
    model;
    alls = keywords;
    vars = Mv.empty;
    glob = Ms.empty;
    funs = Mf.empty;
    arrsz;
    warrsz;
    auxv  = Mty.empty;
    randombytes;
  } in

(*  let mk_tys tys = List.map Conv.cty_of_ty tys in *)
  let add_fun env fd = 
    let s = mkfunname env fd.f_name in
    let funs = 
      Mf.add fd.f_name (s, ((*mk_tys*) fd.f_tyout, (*mk_tys*)fd.f_tyin)) env.funs in
    { env with funs; alls = Ss.add s env.alls } in

  List.fold_left add_fun env fds

let get_funtype env f = snd (Mf.find f env.funs)
let get_funname env f = fst (Mf.find f env.funs) 

let ec_syscall env o =
  match o with
  | Syscall_t.RandomBytes p ->
    let n = (Conv.int_of_pos p) in
    env.randombytes := Sint.add n !(env.randombytes);
    Format.sprintf "%s.randombytes_%i" syscall_mod_arg n

let ty_lval = function
  | Lnone (_, ty) -> ty
  | Lvar x -> (L.unloc x).v_ty
  | Lmem (_, ws,_,_) -> Bty (U ws)
  | Laset(_, _, ws, _, _) -> Bty (U ws)
  | Lasub (_,ws, len, _, _) -> Arr(ws, len) 


let add_Array env n =
  env.arrsz := Sint.add n !(env.arrsz)

let add_WArray env n =
  env.warrsz := Sint.add n !(env.warrsz)

let add_aux env tys = 
  let tbl = Hashtbl.create 10 in
  let do1 env ty = 
    let n = try Hashtbl.find tbl ty with Not_found -> 0 in
    let l = try Mty.find ty env.auxv with Not_found -> [] in
    Hashtbl.replace tbl ty (n+1);
    if n < List.length l then env
    else
      let aux = create_name env "aux" in
      {env with auxv = Mty.add ty (aux::l) env.auxv;
                alls = Ss.add aux env.alls } in
  List.fold_left do1 env tys

let get_aux env tys = 
  let tbl = Hashtbl.create 10 in
  let do1 ty = 
    let n = try Hashtbl.find tbl ty with Not_found -> 0 in
    let l = try Mty.find ty env.auxv with Not_found -> assert false in
    Hashtbl.replace tbl ty (n+1);
    assert (n < List.length l);
    List.nth l n in
  List.map do1 tys

let set_var env x s = 
  { env with 
    alls = Ss.add s env.alls;
    vars = Mv.add x s env.vars }

let add_var env x = 
  let s = normalize_name x.v_name in
  let s = create_name env s in
  set_var env x s

let add_glob env x =
  let s = create_name env (normalize_name x.v_name) in
  set_var env x s

let swap_op2 op e1 e2 = 
  match op with 
  | E.Ogt   _ -> e2, e1
  | E.Oge   _ -> e2, e1 
  | _         -> e1, e2

let pp_signed fmt ws is = function 
  | E.Cmp_w (Signed, _)   -> Format.fprintf fmt "\\s%s" ws
  | E.Cmp_w (Unsigned, _) -> Format.fprintf fmt "\\u%s" ws
  | _                     -> Format.fprintf fmt "%s" is

let pp_vop2 fmt (s,ve,ws) = 
  Format.fprintf fmt "\\v%s%iu%i" s (int_of_velem ve) (int_of_ws ws)

let pp_op2 fmt = function
  | E.Obeq   -> Format.fprintf fmt "="
  | E.Oand   -> Format.fprintf fmt "/\\"
  | E.Oor    -> Format.fprintf fmt "\\/"
  | E.Oadd _ -> Format.fprintf fmt "+"
  | E.Omul _ -> Format.fprintf fmt "*"
  | E.Odiv s -> pp_signed fmt "div" "%/" s
  | E.Omod s -> pp_signed fmt "mod" "%%" s

  | E.Osub  _ -> Format.fprintf fmt "-"

  | E.Oland _ -> Format.fprintf fmt "`&`"
  | E.Olor  _ -> Format.fprintf fmt "`|`"
  | E.Olxor _ -> Format.fprintf fmt "`^`"
  | E.Olsr  _ -> Format.fprintf fmt "`>>`"
  | E.Olsl  _ -> Format.fprintf fmt "`<<`"
  | E.Oasr  _ -> Format.fprintf fmt "`|>>`"
  | E.Orol _ -> Format.fprintf fmt "`|<<|`"
  | E.Oror _ -> Format.fprintf fmt "`|>>|`"

  | E.Oeq   _ -> Format.fprintf fmt "="
  | E.Oneq  _ -> Format.fprintf fmt "<>"
  | E.Olt s| E.Ogt s -> pp_signed fmt "lt" "<" s
  | E.Ole s | E.Oge s -> pp_signed fmt "le" "<=" s

  | Ovadd(ve,ws) -> pp_vop2 fmt ("add", ve, ws)
  | Ovsub(ve,ws) -> pp_vop2 fmt ("sub", ve, ws) 
  | Ovmul(ve,ws) -> pp_vop2 fmt ("mul", ve, ws) 
  | Ovlsr(ve,ws) -> pp_vop2 fmt ("shr", ve, ws)
  | Ovlsl(ve,ws) -> pp_vop2 fmt ("shl", ve, ws)
  | Ovasr(ve,ws) -> pp_vop2 fmt ("sar", ve, ws) 
  

let in_ty_op1 op =
  Conv.ty_of_cty (fst  (E.type_of_op1 op))

let in_ty_op2 op =
  let t1, t2 = fst (E.type_of_op2 op) in
  Conv.ty_of_cty t1, Conv.ty_of_cty t2

let out_ty_op1 op =
  Conv.ty_of_cty (snd (E.type_of_op1 op))

let out_ty_op2 op =
  Conv.ty_of_cty (snd (E.type_of_op2 op))

let out_ty_opN op =
  Conv.ty_of_cty (snd (E.type_of_opN op))

let ty_expr = function
  | Pconst _       -> tint 
  | Pbool _        -> tbool
  | Parr_init len  -> Arr (U8, len)
  | Pvar x         -> x.gv.L.pl_desc.v_ty
  | Pload (_, sz,_,_) -> tu sz
  | Pget  (_,_, sz,_,_) -> tu sz
  | Psub (_,ws, len, _, _) -> Arr(ws, len)
  | Papp1 (op,_)   -> out_ty_op1 op
  | Papp2 (op,_,_) -> out_ty_op2 op
  | PappN (op, _)  -> out_ty_opN op
  | Pif (ty,_,_,_) -> ty

let check_array env x = 
  match (L.unloc x).v_ty with
  | Arr(ws, n) -> Sint.mem n !(env.arrsz) && Sint.mem (arr_size ws n) !(env.warrsz)
  | _ -> true

let ec_print_i z = 
  if Z.leq Z.zero z then Z.to_string z 
  else Format.asprintf "(%a)" Z.pp_print z 

let pp_access aa = if aa = Warray_.AAdirect then "_direct" else ""

type ec_op2 =
    | ArrayGet
    | Plus
    | Infix of string

type ec_op3 =
    | Ternary 
    | If 
    | InORange

type ec_ident = string list

type ec_expr = 
    | Econst of Z.t (* int. literal *)
    | Ebool of bool (* bool literal *)
    | Eident of ec_ident (* variable *)
    | Eapp of ec_expr * ec_expr list (* op. application *)
    | Efun1 of string * ec_expr (* fun s => expr *)
    | Eop2 of ec_op2 * ec_expr * ec_expr (* binary operator *)
    | Eop3 of ec_op3 * ec_expr * ec_expr * ec_expr (* ternary operator *)
    | Elist of ec_expr list (* list litteral *)
    | Etuple of ec_expr list (* tuple litteral *)

let ec_ident s = Eident [s]
let ec_aget a i = Eop2 (ArrayGet, a, i)
let ec_int x = Econst (Z.of_int x)

let ec_vars env (x:var) = Mv.find x env.vars
let ec_vari env (x:var) = Eident [ec_vars env x]

let glob_mem = ["Glob"; "mem"]
let glob_memi = Eident glob_mem

let pd_uint env = Eident [Format.sprintf "W%d" (int_of_ws env.pd); "to_uint"]

let ec_apps1 s e = Eapp (ec_ident s, [e])

let iIdent i = ec_ident (Format.sprintf "%i" i)

let fmt_Array n = Format.sprintf "Array%i" n

let fmt_WArray n = Format.sprintf "WArray%i" n

let ec_Array env n = add_Array env n; fmt_Array n

let ec_WArray env n = add_WArray env n; fmt_WArray n

let ec_WArray_init env ws n =
      Eident [ec_WArray env (arr_size ws n); Format.sprintf "init%i" (int_of_ws ws)]

let ec_WArray_initf env ws n f =
    let i = create_name env "i" in
    Eapp (ec_WArray_init env ws n, [Efun1 (i, f i)])

let ec_Array_init env len = Eident [ec_Array env len; "init"]

let ec_initi env (x, n, ws) =
    let f i = ec_aget x (ec_ident i) in
    ec_WArray_initf env ws n f

let ec_initi_var env (x, n, ws) = ec_initi env (ec_vari env x, n, ws)

let ec_zeroext (szo, szi) e =
  let io, ii = int_of_ws szo, int_of_ws szi in
  if ii < io then ec_apps1 (Format.sprintf "zeroextu%i" io) e
  else if ii = io then e
  else (* io < ii *) ec_apps1 (Format.sprintf "truncateu%i" io) e

let ec_wzeroext (tyo, tyi) e =
    if tyi = tyo then e else ec_zeroext (ws_of_ty tyo, ws_of_ty tyi) e

let ec_cast env (ty, ety) e =
    if ety = ty then e
    else
        match ty with
        | Bty _ -> ec_zeroext (ws_of_ty ty, ws_of_ty ety) e
        | Arr(ws, n) ->
            let wse, ne = array_kind ety in
            let i = create_name env "i" in
            let geti = ec_ident (Format.sprintf "get%i" (int_of_ws ws)) in
            let init_fun = Efun1 (i, Eapp (geti, [ec_initi env (e, ne, wse); ec_ident i])) in
            Eapp (ec_Array_init env n, [init_fun])

let ec_op1 op e = match op with
  | E.Oword_of_int sz ->
    ec_apps1 (Format.sprintf "%s.of_int" (pp_Tsz sz)) e
  | E.Oint_of_word sz ->
    ec_apps1 (Format.sprintf "%s.to_uint" (pp_Tsz sz)) e
  | E.Osignext(szo,_szi) -> 
    ec_apps1 (Format.sprintf "sigextu%i" (int_of_ws szo)) e
  | E.Ozeroext(szo,szi) -> ec_zeroext (szo, szi) e
  | E.Onot     -> ec_apps1 "!" e
  | E.Olnot _  -> ec_apps1 "invw" e
  | E.Oneg _   -> ec_apps1 "-" e


let rec toec_expr env (e: expr) =
    match e with
    | Pconst z -> Econst z
    | Pbool b -> Ebool b
    | Parr_init _n -> ec_ident "witness"
    | Pvar x -> ec_vari env (L.unloc x.gv)
    | Pget (a, aa, ws, y, e) ->
        assert (check_array env y.gv);
        let x = L.unloc y.gv in
        let (xws, n) = array_kind x.v_ty in
        if ws = xws && aa = Warray_.AAscale then
            ec_aget (ec_vari env x) (toec_expr env e)
        else
            Eapp (
                (ec_ident (Format.sprintf "get%i%s" (int_of_ws ws) (pp_access aa))),
                [ec_initi_var env (x, n, xws); toec_expr env e]
            )
    | Psub (aa, ws, len, x, e) -> 
        assert (check_array env x.gv);
        let i = create_name env "i" in
        let x = L.unloc x.gv in
        let (xws,n) = array_kind x.v_ty in
        if ws = xws && aa = Warray_.AAscale then
            Eapp (
                ec_Array_init env len,
                [
                    Efun1 (i, ec_aget (ec_vari env x)  (Eop2 (Plus, toec_expr env e, ec_ident i)))
            ])
        else 
            Eapp (
                ec_Array_init env len,
                [
                    Efun1 (i, 
                    Eapp (ec_ident (Format.sprintf "get%i%s" (int_of_ws ws) (pp_access aa)), [
                        ec_initi_var env (x, n, xws); Eop2 (Plus, toec_expr env e, ec_ident i)
                ])
                    )
            ])
    | Pload (_, sz, x, e) ->
        let load = ec_ident (Format.sprintf "loadW%i" (int_of_ws sz)) in
        Eapp (load, [
            glob_memi;
            Eapp (pd_uint env, [ec_wcast env (add_ptr env.pd (gkvar x) e)])
        ])
    | Papp1 (op1, e) -> 
          ec_op1 op1 (ec_wcast env (in_ty_op1 op1, e))
    | Papp2 (op2, e1, e2) ->  
        let ty1,ty2 = in_ty_op2 op2 in
        let te1, te2 = swap_op2 op2 (ty1, e1) (ty2, e2) in
        let op = Infix (Format.asprintf "%a" pp_op2 op2) in
        Eop2 (op, (ec_wcast env te1), (ec_wcast env te2))
    | PappN (op, es) ->
        begin match op with
        | Opack (ws, we) ->
            let i = int_of_pe we in
            let rec aux es = 
                match es with
                | [] -> assert false
                | [e] -> toec_expr env e
                | e::es -> 
                        let exp2i = Eop2 (Infix "^", iIdent 2, iIdent i) in
                        Eop2 (
                            Infix "+",
                            Eop2 (Infix "%%", toec_expr env e, exp2i),
                            Eop2 (Infix "*", exp2i, aux es)
                            )
            in
            ec_apps1 (Format.sprintf "W%i.of_int" (int_of_ws ws)) (aux (List.rev es))
        | Ocombine_flags c -> 
            Eapp (
                ec_ident (Printer.string_of_combine_flags c),
                List.map (toec_expr env) es
            )
        end
    | Pif(_,e1,et,ef) -> 
        let ty = ty_expr e in
        Eop3 (
            Ternary,
            toec_expr env e1,
            ec_wcast env (ty, et),
            ec_wcast env (ty, ef)
        )

and toec_cast env ty e = ec_cast env (ty, ty_expr e) (toec_expr env e)
and ec_wcast env (ty, e) = toec_cast env ty e

let pp_ec_ident fmt ident = Format.fprintf fmt "@[%a@]" (pp_list "." pp_string) ident

let rec pp_ec_ast_expr fmt e = match e with
    | Econst z -> Format.fprintf fmt "%s" (ec_print_i z)
    | Ebool b -> pp_bool fmt b
    | Eident s -> pp_ec_ident fmt s
    | Eapp (f, ops) -> 
            Format.fprintf fmt "@[(@,%a@,)@]"
            (Format.(pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ")) pp_ec_ast_expr)
            (f::ops)
    | Efun1 (var, e) -> 
            Format.fprintf fmt "@[(fun %s => %a)@]" var pp_ec_ast_expr e
    | Eop2 (op, e1, e2) -> pp_ec_op2 fmt (op, e1, e2)
    | Eop3 (op, e1, e2, e3) -> pp_ec_op3 fmt (op, e1, e2, e3)
    | Elist es -> Format.fprintf fmt "@[[%a]@]" (pp_list ";@ " pp_ec_ast_expr) es
    | Etuple es -> Format.fprintf fmt "@[(%a)@]" (pp_list ",@ " pp_ec_ast_expr) es

and pp_ec_op2 fmt (op2, e1, e2) =
    let f fmt = match op2 with
    | ArrayGet -> Format.fprintf fmt "@[%a.[%a]@]"
    | Plus -> Format.fprintf fmt "@[(%a +@ %a)@]"
    | Infix s -> (fun pp1 e1 -> Format.fprintf fmt "@[(%a %s@ %a)@]" pp1 e1 s)
    in
    (f fmt) pp_ec_ast_expr e1 pp_ec_ast_expr e2

and pp_ec_op3 fmt (op, e1, e2, e3) =
    let f fmt = match op with
    | Ternary -> Format.fprintf fmt "@[(%a ? %a : %a)@]"
    | If -> Format.fprintf fmt "@[(if %a then %a else %a)@]"
    | InORange -> Format.fprintf fmt "@[(%a <= %a < %a)@]"
    in
    (f fmt) pp_ec_ast_expr e1 pp_ec_ast_expr e2 pp_ec_ast_expr e3

let base_op = function
  | Sopn.Oasm (Arch_extra.BaseOp (_, o)) -> Sopn.Oasm (Arch_extra.BaseOp(None,o))
  | o -> o

let ty_sopn pd asmOp op es =
  match op with
  (* Do a special case for copy since the Coq type loose information  *)
  | Sopn.Opseudo_op (Pseudo_operator.Ocopy(ws, p)) ->
    let l = [Arr(ws, Conv.int_of_pos p)] in
    l, l
  | Sopn.Opseudo_op (Pseudo_operator.Oswap _) -> 
    let l = List.map ty_expr es in
    l, l
  | _ ->
    List.map Conv.ty_of_cty (Sopn.sopn_tout pd asmOp op),
    List.map Conv.ty_of_cty (Sopn.sopn_tin pd asmOp op)

(* This code replaces for loop that modify the loop counter by while loop,
   it would be nice to prove in Coq the validity of the transformation *) 

let is_write_lv x = function
  | Lnone _ | Lmem _ -> false 
  | Lvar x' | Laset(_, _, _, x', _) | Lasub (_, _, _, x', _) ->
    V.equal x x'.L.pl_desc 

let is_write_lvs x = List.exists (is_write_lv x)

let rec is_write_i x i = 
  match i.i_desc with
  | Cassgn (lv,_,_,_) ->
    is_write_lv x lv
  | Copn(lvs,_,_,_) | Ccall(lvs, _, _) | Csyscall(lvs,_,_) ->
    is_write_lvs x lvs
  | Cif(_, c1, c2) | Cwhile(_, c1, _, c2) -> 
    is_write_c x c1 || is_write_c x c2 
  | Cfor(x',_,c) -> 
    V.equal x x'.L.pl_desc || is_write_c x c

and is_write_c x c = List.exists (is_write_i x) c
  
let rec remove_for_i i =
  let i_desc = 
    match i.i_desc with
    | Cassgn _ | Copn _ | Ccall _ | Csyscall _ -> i.i_desc
    | Cif(e, c1, c2) -> Cif(e, remove_for c1, remove_for c2)
    | Cwhile(a, c1, e, c2) -> Cwhile(a, remove_for c1, e, remove_for c2)
    | Cfor(j,r,c) -> 
      let jd = j.pl_desc in
      if not (is_write_c jd c) then Cfor(j, r, remove_for c)
      else 
        let jd' = V.clone jd in
        let j' = { j with pl_desc = jd' } in
        let ii' = Cassgn (Lvar j, E.AT_inline, jd.v_ty, Pvar (gkvar j')) in
        let ii' = { i with i_desc = ii' } in
        Cfor (j', r, ii' :: remove_for c)
  in
  { i with i_desc }   
and remove_for c = List.map remove_for_i c

type ec_lvalue =
    | LvIdent of ec_ident
    | LvArrItem of ec_ident * ec_expr

type ec_lvalues = ec_lvalue list

type ec_instr =
    | ESasgn of ec_lvalues * ec_expr
    | EScall of ec_lvalues * ec_ident * ec_expr list
    | ESsample of ec_lvalues * ec_expr
    | ESif of ec_expr * ec_stmt * ec_stmt
    | ESwhile of ec_expr * ec_stmt
    | ESreturn of ec_expr
    | EScomment of string (* comment line *)

and ec_stmt = ec_instr list

let pp_ec_lvalue fmt (lval: ec_lvalue) =
    match lval with
    | LvIdent ident -> pp_ec_ident fmt ident
    | LvArrItem (ident, e) -> pp_ec_op2 fmt (ArrayGet, Eident ident, e)

let pp_ec_lvalues fmt (lvalues: ec_lvalues) =
    match lvalues with
    | [] -> assert false
    | [lv] -> pp_ec_lvalue fmt lv
    | _ -> Format.fprintf fmt "@[(%a)@]" (pp_list ",@ " pp_ec_lvalue) lvalues

let rec pp_ec_ast_stmt fmt stmt =
    Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " pp_ec_ast_instr) stmt

and pp_ec_ast_instr fmt instr =
    match instr with
    | ESasgn (lv, e) -> Format.fprintf fmt "@[%a <-@ %a;@]" pp_ec_lvalues lv pp_ec_ast_expr e
    | EScall (lvs, f, args) ->
            let pp_res fmt lvs =
                if lvs = [] then
                    Format.fprintf fmt ""
                else
                    Format.fprintf fmt "%a <%@ " pp_ec_lvalues lvs
            in
            Format.fprintf fmt "@[%a%a (%a);@]"
                pp_res lvs
                pp_ec_ast_expr (Eident f)
                (pp_list ",@ " pp_ec_ast_expr) args
    | ESsample (lv, e) -> Format.fprintf fmt "@[%a <$@ %a;@]" pp_ec_lvalues lv pp_ec_ast_expr e
    | ESif (e, c1, c2) ->
            Format.fprintf fmt "@[<v>if (%a) {@   %a@ } else {@   %a@ }@]"
            pp_ec_ast_expr e pp_ec_ast_stmt c1 pp_ec_ast_stmt c2
    | ESwhile (e, c) ->
            Format.fprintf fmt "@[<v>while (%a) {@   %a@ }@]"
            pp_ec_ast_expr e pp_ec_ast_stmt c
    | ESreturn e -> Format.fprintf fmt "@[return %a;@]" pp_ec_ast_expr e
    | EScomment s -> Format.fprintf fmt "@[(* %s *)@]" s

let ec_opn pd asmOp o = 
  let s = Format.asprintf "%a" (pp_opn pd asmOp) o in
  if Ss.mem s keywords then s^"_" else s

let ec_lval env = function
  | Lnone _ -> assert false
  | Lmem _ -> assert false 
  | Lvar x  -> LvIdent [ec_vars env (L.unloc x)]
  | Laset _  -> assert false 
  | Lasub _ -> assert false 

let ec_lvals env xs = List.map (ec_lval env) xs

let toec_lval1 env lv e =
    match lv with 
    | Lnone _ -> assert false
    | Lmem(_, ws, x, e1) ->
        let storewi = ec_ident (Format.sprintf "storeW%i" (int_of_ws ws)) in
        let addr = Eapp (pd_uint env, [ec_wcast env (add_ptr env.pd (gkvar x) e1)]) in
        ESasgn ([LvIdent glob_mem], Eapp (storewi, [glob_memi; addr; e]))
  | Lvar x  ->
        let lvid = [ec_vars env (L.unloc x)] in
        ESasgn ([LvIdent lvid], e)
  | Laset (_, aa, ws, x, e1) ->
        assert (check_array env x);
        let x = L.unloc x in
        let (xws,n) = array_kind x.v_ty in
        if ws = xws && aa = Warray_.AAscale then
            ESasgn ([LvArrItem ([ec_vars env x], toec_expr env e1)], e)
        else
            let nws = n * int_of_ws xws in
            let warray = ec_WArray env (nws / 8) in
            let waget = Eident [warray; Format.sprintf "get%i" (int_of_ws xws)] in
            let wsi = int_of_ws ws in
            let waset = Eident [warray; Format.sprintf "set%i%s" wsi (pp_access aa)] in
            let updwa = Eapp (waset, [ec_initi_var env (x, n, xws); toec_expr env e1; e]) in
            ESasgn (
                [LvIdent [ec_vars env x]],
                Eapp (ec_Array_init env n, [Eapp (waget, [updwa])])
            )
  | Lasub (aa, ws, len, x, e1) -> 
    assert (check_array env x);
    let x = L.unloc x in
    let (xws, n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
        let i = create_name env "i" in
        let range_ub = Eop2 (Plus, toec_expr env e1, ec_int len) in
        ESasgn (
            [LvIdent [ec_vars env x]],
            Eapp (ec_Array_init env n, [
                Efun1 (i, Eop3 (
                    If,
                    Eop3 (InORange, toec_expr env e1, ec_ident i, range_ub),
                    ec_aget e (Eop2 (Infix "-", ec_ident i, toec_expr env e1)),
                    ec_aget (ec_vari env x) (ec_ident i)
                    ))
            ])
            )
    else 
        let nws = n * int_of_ws xws in
        let nws8 = nws / 8 in
        let start = 
            if aa = Warray_.AAscale then
                Eop2 (Infix "*", ec_int (int_of_ws ws / 8), toec_expr env e1)
            else
                toec_expr env e1
        in
        let len8 = len * int_of_ws ws / 8 in
        let i = create_name env "i" in
        let in_range = Eop3 (InORange, start, ec_ident i, Eop2 (Plus, start, ec_int len8)) in
        let ainit = Eident [ec_WArray env nws8; "init8"] in
        let aw_get8 len = Eident [ec_WArray env len; "get8"] in
        let at = Eapp (aw_get8 len8, [ec_initi env (e, len, ws); Eop2 (Infix "-", ec_ident i, start)]) in
        let ae = Eapp (aw_get8 nws8, [ec_initi_var env (x, n, xws); ec_ident i]) in
        let a = Eapp (ainit, [Efun1 (i, Eop3 (If, in_range, at, ae))]) in
        let wag = Eident [ec_WArray env nws8; Format.sprintf "get%i" (int_of_ws xws)] in
        ESasgn (
            [LvIdent [ec_vars env x]],
            Eapp (ec_Array_init env n, [Eapp (wag, [a])])
        )

(* =================----------=============== *)
let all_vars lvs = 
    let is_lvar = function Lvar _ -> true | _ -> false in
    List.for_all is_lvar lvs

let check_lvals lvs = all_vars lvs

let rec init_aux_i pd asmOp env i =
match i.i_desc with
    | Cassgn (lv, _, _, e) -> (
        match env.model with
        | Normal -> env
        | ConstantTime -> add_aux (add_aux env [ty_lval lv]) [ty_expr e]
    )
    | Copn (lvs, _, op, _) -> (
        match env.model with
        | Normal -> 
            if List.length lvs = 1 then env 
            else
                let tys  = List.map Conv.ty_of_cty (Sopn.sopn_tout pd asmOp op) in
                let ltys = List.map ty_lval lvs in
                if all_vars lvs && ltys = tys then env
                else add_aux env tys
        | ConstantTime ->
            let op = base_op op in
            let tys  = List.map Conv.ty_of_cty (Sopn.sopn_tout pd asmOp op) in
            let env = add_aux env tys in
            add_aux env (List.map ty_lval lvs)
    )
    | Ccall(lvs, f, _) -> (
        match env.model with
        | Normal ->
            if lvs = [] then env 
            else 
                let tys = (*List.map Conv.ty_of_cty *)(fst (get_funtype env f)) in
                let ltys = List.map ty_lval lvs in
                if (check_lvals lvs && ltys = tys) then env
                else add_aux env tys
        | ConstantTime ->
            if lvs = [] then env 
            else add_aux env (List.map ty_lval lvs)
    )
    | Csyscall(lvs, o, _) -> (
        match env.model with
        | Normal ->
            if lvs = [] then env
            else
                let tys = List.map Conv.ty_of_cty (Syscall.syscall_sig_u o).scs_tout in
                let ltys = List.map ty_lval lvs in
                if (check_lvals lvs && ltys = tys) then env
                else add_aux env tys
        | ConstantTime ->
            let s = Syscall.syscall_sig_u o in
            let otys = List.map Conv.ty_of_cty s.scs_tout in
            let env = add_aux env otys in
            add_aux env (List.map ty_lval lvs)
    )
    | Cif(_, c1, c2) | Cwhile(_, c1, _, c2) -> init_aux pd asmOp (init_aux pd asmOp env c1) c2
    | Cfor(_,_,c) -> init_aux pd asmOp (add_aux env [tint]) c

and init_aux pd asmOp env c = List.fold_left (init_aux_i pd asmOp) env c


let ece_leaks_e env e = List.map (toec_expr env) (leaks_e env.pd e)

let ec_newleaks leaks =
    let add_leak lacc l = Eop2 (Infix "::", l, lacc) in
    List.fold_left add_leak (ec_ident "leakages") leaks

let ec_addleaks leaks = [ESasgn ([LvIdent ["leakages"]], ec_newleaks leaks)]

let ec_leaks es = ec_addleaks [Eapp (ec_ident "LeakAddr", [Elist es])]

let ec_leaks_e env e =
    match env.model with
    | ConstantTime -> ec_leaks (ece_leaks_e env e)
    | Normal -> []

let ec_leaks_es env es =
    match env.model with
    | ConstantTime -> ec_leaks (List.map (toec_expr env) (leaks_es env.pd es))
    | Normal -> []

let ec_leaks_opn env es =  ec_leaks_es env es

let ec_leaks_if env e = 
    match env.model with
    | ConstantTime -> 
        ec_addleaks [
            Eapp (ec_ident "LeakAddr", [Elist (ece_leaks_e env e)]);
            Eapp (ec_ident "LeakCond", [toec_expr env e])
        ]
    | Normal -> []

let ec_leaks_for env e1 e2 = 
    match env.model with
    | ConstantTime -> 
        let leaks = List.map (toec_expr env) (leaks_es env.pd [e1;e2]) in
        ec_addleaks [
            Eapp (ec_ident "LeakAddr", [Elist leaks]);
            Eapp (ec_ident "LeakFor", [Etuple [toec_expr env e1; toec_expr env e2]])
            ]
    | Normal -> []

let ec_leaks_lv env lv = 
    match env.model with
    | ConstantTime -> 
        let leaks = leaks_lval env.pd lv in
        if leaks = [] then []
        else ec_leaks (List.map (toec_expr env) leaks)
    | Normal -> []

let ec_assgn env lv (etyo, etyi) e =
    let e = e |> ec_wzeroext (etyo, etyi) |> ec_cast env (ty_lval lv, etyo) in
    (ec_leaks_lv env lv) @ [toec_lval1 env lv e]

let ec_assgn_i env lv ((etyo, etyi), aux) = ec_assgn env lv (etyo, etyi) (ec_ident aux)

let ec_instr_aux env lvs etyso etysi instr =
    let auxs = get_aux env etysi in
    let s2lv s = LvIdent [s] in
    let call = instr (List.map s2lv auxs) in
    let tyauxs = List.combine (List.combine etyso etysi) auxs in
    let assgn_auxs = List.flatten (List.map2 (ec_assgn_i env) lvs tyauxs) in
    call :: assgn_auxs

let ec_pcall env lvs otys f args =
    let ltys = List.map ty_lval lvs in
    if lvs = [] || (env.model = Normal && check_lvals lvs && ltys = otys) then
        [EScall (ec_lvals env lvs, f, args)]
    else
        ec_instr_aux env lvs otys otys (fun lvals -> EScall (lvals, f, args))

let ec_call env lvs etyso etysi e =
    let ltys = List.map ty_lval lvs in
    if lvs = [] || (env.model = Normal && check_lvals lvs && ltys = etyso && etyso = etysi) then
        [ESasgn ((ec_lvals env lvs), e)]
    else
        ec_instr_aux env lvs etyso etysi (fun lvals -> ESasgn (lvals, e))

let rec toec_cmd asmOp env c = List.flatten (List.map (toec_instr asmOp env) c)

and toec_instr asmOp env i =
    match i.i_desc with
    | Cassgn (lv, _, _, (Parr_init _ as e)) ->
        (ec_leaks_e env e) @
        [toec_lval1 env lv (ec_ident "witness")]
    | Cassgn (lv, _, _, e) -> (
        match env.model with
        | Normal ->
            let e = toec_cast env (ty_lval lv) e in
            [toec_lval1 env lv e]
        | ConstantTime ->
            let tys = [ty_expr e] in
            (ec_leaks_e env e) @
            ec_call env [lv] tys tys (toec_expr env e)
    )
    | Copn ([], _, op, es) ->
        (ec_leaks_opn env es) @
        [EScomment (Format.sprintf "Erased call to %s" (ec_opn env.pd asmOp op))]
    | Copn (lvs, _, op, es) ->
        let op' = base_op op in
        (* Since we do not have merge for the moment only the output type can change *)
        let otys,itys = ty_sopn env.pd asmOp op es in
        let otys', _ = ty_sopn env.pd asmOp op' es in
        let ec_op op = ec_ident (ec_opn env.pd asmOp op) in
        let ec_e op = Eapp (ec_op op, List.map (ec_wcast env) (List.combine itys es)) in
        if env.model = Normal && List.length lvs = 1 then
            ec_assgn env (List.hd lvs) (List.hd otys, List.hd otys') (ec_e op')
        else
            (ec_leaks_opn env es) @
            (ec_call env lvs otys otys' (ec_e op))
    | Ccall (lvs, f, es) ->
        let otys, itys = get_funtype env f in
        let args = List.map (ec_wcast env) (List.combine itys es) in
        (ec_leaks_es env es) @
        (ec_pcall env lvs otys [get_funname env f] args)
    | Csyscall (lvs, o, es) ->
        let s = Syscall.syscall_sig_u o in
        let otys = List.map Conv.ty_of_cty s.scs_tout in
        let itys =  List.map Conv.ty_of_cty s.scs_tin in
        let args = List.map (ec_wcast env) (List.combine itys es) in
        (ec_leaks_es env es) @
        (ec_pcall env lvs otys [ec_syscall env o] args)
    | Cif (e, c1, c2) ->
        (ec_leaks_if env e) @
        [ESif (toec_expr env e, toec_cmd asmOp env c1, toec_cmd asmOp env c2)]
    | Cwhile (_, c1, e, c2) ->
        let leak_e = ec_leaks_if env e in
        (toec_cmd asmOp env c1) @ leak_e @
        [ESwhile (toec_expr env e, (toec_cmd asmOp env (c2@c1)) @ leak_e)]
    | Cfor (i, (d,e1,e2), c) ->
        (* decreasing for loops have bounds swaped *)
        let e1, e2 = if d = UpTo then e1, e2 else e2, e1 in 
        let init, ec_e2 = 
            match e2 with
            (* Can be generalized to the case where e2 is not modified by c and i *)
            | Pconst _ -> ([], toec_expr env e2)
            | _ -> 
                let aux = List.hd (get_aux env [tint]) in
                let init = ESasgn ([LvIdent [aux]], toec_expr env e2) in
                let ec_e2 = ec_ident aux in
                [init], ec_e2 in
        let ec_i = [ec_vars env (L.unloc i)] in
        let lv_i = [LvIdent ec_i] in
        let ec_i1, ec_i2 = 
            if d = UpTo then Eident ec_i , ec_e2
            else ec_e2, Eident ec_i in
        let i_upd_op = Infix (if d = UpTo then "+" else "-") in
        let i_upd = ESasgn (lv_i, Eop2 (i_upd_op, Eident ec_i, Econst (Z.of_int 1))) in
        (ec_leaks_for env e1 e2) @ init @ [
            ESasgn (lv_i, toec_expr env e1);
            ESwhile (Eop2 (Infix "<", ec_i1, ec_i2), (toec_cmd asmOp env c) @ [i_upd])
            ]

type ec_ty = string

type ec_var = string * ec_ty

type ec_fun_decl = {
    fname: string;
    args: (string * ec_ty) list;
    rtys: ec_ty list;
}
type ec_fun = {
    decl: ec_fun_decl;
    locals: (string * ec_ty) list;
    stmt: ec_stmt;
}

let toec_ty ty = match ty with
    | Bty Bool -> "bool"
    | Bty Int  -> "int"
    | Bty (U ws) -> (pp_sz_t ws)
    | Arr(ws,n) -> Format.sprintf "%s %s.t" (pp_sz_t ws) (fmt_Array n)

let var2ec_var env x = (List.hd [ec_vars env x], toec_ty x.v_ty)

let pp_ec_vdecl fmt (x, ty) = Format.fprintf fmt "%s:%a" x pp_string ty

let pp_ec_fun_decl fmt fdecl =
    let pp_ec_rty fmt rtys =
        if rtys = [] then Format.fprintf fmt "unit"
        else Format.fprintf fmt "@[%a@]" (pp_list " *@ " pp_string) rtys
    in
    Format.fprintf fmt 
        "@[proc %s (@[%a@]) : @[%a@]@]"
        fdecl.fname
        (pp_list ",@ " pp_ec_vdecl) fdecl.args
        pp_ec_rty fdecl.rtys

let pp_ec_fun fmt f =
    let pp_decl_s fmt v = Format.fprintf fmt "var %a;" pp_ec_vdecl v in
    Format.fprintf fmt 
        "@[<v>@[%a = {@]@   @[<v>%a@ %a@]@ }@]"
        pp_ec_fun_decl f.decl
        (pp_list "@ " pp_decl_s) f.locals
        pp_ec_ast_stmt  f.stmt

let add_ty env = function
    | Bty _ -> ()
    | Arr (_ws, n) -> add_Array env n

let toec_fun asmOp env f = 
    let f = { f with f_body = remove_for f.f_body } in
    let locals = Sv.elements (locals f) in
    let env = List.fold_left add_var env (f.f_args @ locals) in
    (* init auxiliary variables *) 
    let env = init_aux env.pd asmOp env f.f_body
    in
    List.iter (add_ty env) f.f_tyout;
    List.iter (fun x -> add_ty env x.v_ty) (f.f_args @ locals);
    Mty.iter (fun ty _ -> add_ty env ty) env.auxv;
    let ec_locals =
        let locs_ty (ty, vars) = List.map (fun v -> (v, toec_ty ty)) vars in
        (List.flatten (List.map locs_ty (Mty.bindings env.auxv))) @
        (List.map (var2ec_var env) locals)
    in
    let aux_locals_init = locals
        |> List.filter (fun x -> match x.v_ty with Arr _ -> true | _ -> false) 
        |> List.sort (fun x1 x2 -> compare x1.v_name x2.v_name)
        |> List.map (fun x -> ESasgn ([LvIdent [ec_vars env x]], ec_ident "witness"))
    in
    let ret =
        let ec_var x = ec_vari env (L.unloc x) in
        match f.f_ret with
        | [x] -> ESreturn (ec_var x)
        | xs -> ESreturn (Etuple (List.map ec_var xs))
    in
    {
        decl = {
            fname = (get_funname env f.f_name);
            args = List.map (var2ec_var env) f.f_args;
            rtys = List.map toec_ty f.f_tyout;
        };
        locals = ec_locals;
        stmt = aux_locals_init @ (toec_cmd asmOp env f.f_body) @ [ret];
    }

let add_arrsz env f = 
  let add_sz x sz = 
    match x.v_ty with
    | Arr(_ws, n) -> Sint.add n sz 
    | _ -> sz in
  let add_wsz x sz =
    match x.v_ty with
    | Arr(ws, n) -> Sint.add (arr_size ws n) sz 
    | _ -> sz in
    
  let vars = vars_fc f in
  env.arrsz := Sv.fold add_sz vars !(env.arrsz);
  env.warrsz := Sv.fold add_wsz vars !(env.warrsz);
  env

let pp_array_decl ~prefix i =
  let file = Format.sprintf "Array%i.ec" i in
  let path = Filename.concat prefix file in
  let out = open_out path in
  let fmt = Format.formatter_of_out_channel out in
  Format.fprintf fmt "@[<v>from Jasmin require import JArray.@ @ ";
  Format.fprintf fmt "clone export PolyArray as Array%i  with op size <- %i.@]@." i i;
  close_out out

let pp_warray_decl ~prefix i =
  let file = Format.sprintf "WArray%i.ec" i in
  let path = Filename.concat prefix file in
  let out = open_out path in
  let fmt = Format.formatter_of_out_channel out in
  Format.fprintf fmt "@[<v>from Jasmin require import JWord_array.@ @ ";
  Format.fprintf fmt "clone export WArray as WArray%i  with op size <- %i.@]@." i i;
  close_out out

let add_glob_arrsz env (x,d) = 
  match d with 
  | Global.Gword _ -> env
  | Global.Garr(p,t) ->
    let ws, t = Conv.to_array x.v_ty p t in
    let n = Array.length t in
    env.arrsz := Sint.add n !(env.arrsz);
    env.warrsz := Sint.add (arr_size ws n) !(env.warrsz); 
    env

let jmodel () = match !Glob_options.target_arch with
  | X86_64 -> "JModel_x86"
  | ARM_M4 -> "JModel_m4"

let lib_slh () = match !Glob_options.target_arch with
    | X86_64 -> "SLH64"
    | ARM_M4 -> "SLH32"

type ec_modty = string

type ec_module_type = {
    name: ec_modty;
    funs: ec_fun_decl list;
}

type ec_module = {
    name: string;
    params: (string * ec_modty) list;
    ty: ec_modty option;
    vars: (string * string) list;
    funs: ec_fun list;
}

type ec_item =
    | IrequireImport of string list
    | Iimport of string list
    | IfromImport of string * (string list)
    | IfromRequireImport of string * (string list)
    | Iabbrev of string * ec_expr
    | ImoduleType of ec_module_type 
    | Imodule of ec_module

type ec_prog = ec_item list

let pp_ec_item fmt it = match it with
    | IrequireImport is ->
        Format.fprintf fmt "@[require import@ @[%a@].@]" (pp_list "@ " pp_string) is
    | Iimport is ->
        Format.fprintf fmt "@[import@ @[%a@].@]" (pp_list "@ " pp_string) is
    | IfromImport (m, is) ->
        Format.fprintf fmt "@[from %s import@ @[%a@].@]" m (pp_list "@ " pp_string) is
    | IfromRequireImport (m, is) ->
        Format.fprintf fmt "@[from %s require import@ @[%a@].@]" m (pp_list "@ " pp_string) is
    | Iabbrev (a, e) ->
        Format.fprintf fmt "@[abbrev %s =@ @[%a@].@]" a pp_ec_ast_expr e
    | ImoduleType mt ->
        Format.fprintf fmt "@[<v>@[module type %s = {@]@   @[<v>%a@]@ }.@]"
        mt.name (pp_list "@ " pp_ec_fun_decl) mt.funs
    | Imodule m ->
        let pp_mp fmt (m, mt) = Format.fprintf fmt "%s:%s" m mt in
        Format.fprintf fmt "@[<v>@[module %s@[%a@]%a = {@]@   @[<v>%a%a%a@]@ }.@]"
        m.name
        (pp_list_paren ",@ " pp_mp) m.params
        (pp_option (fun fmt s -> Format.fprintf fmt " : %s" s)) m.ty
        (pp_list "@ " (fun fmt (v, t) -> Format.fprintf fmt "@[var %s : %s@]" v t)) m.vars
        (fun fmt _ -> if m.vars = [] then (Format.fprintf fmt "") else (Format.fprintf fmt "@ ")) ()
        (pp_list "@ " pp_ec_fun) m.funs

let pp_ec_prog fmt prog = Format.fprintf fmt "@[<v>%a@]" (pp_list "@ @ " pp_ec_item) prog

let ec_glob_decl env (x,d) =
    let w_of_z ws z = Eapp (Eident [pp_Tsz ws; "of_int"], [ec_ident (ec_print_i z)]) in
    let mk_abbrev e = Iabbrev (ec_vars env x, e) in
  match d with
  | Global.Gword(ws, w) -> mk_abbrev (w_of_z ws (Conv.z_of_word ws w))
  | Global.Garr(p,t) ->
    let ws, t = Conv.to_array x.v_ty p t in
    mk_abbrev (Eapp (
        Eident [ec_Array env (Array.length t); "of_list"],
        [ec_ident "witness"; Elist (List.map (w_of_z ws) (Array.to_list t))]
    ))

let ec_randombytes env =
    let randombytes_decl a n =
        let arr_ty = Format.sprintf "W8.t %s.t" (fmt_Array n) in
        {
            fname = Format.sprintf "randombytes_%i" n;
            args = [(a, arr_ty)];
            rtys = [arr_ty];
        }
    in
    let randombytes_f n = 
        let dmap = 
            let wa = fmt_WArray n in
            let initf = Efun1 ("a", Eapp (Eident [fmt_Array n; "init"], [
                Efun1 ("i", Eapp (Eident [wa; "get8"], [ec_ident "a"; ec_ident "i"]))
            ])) in
            Eapp (ec_ident "dmap", [Eident [wa; "darray"]; initf])
        in
        {
            decl = randombytes_decl "a" n;
            locals = [];
            stmt = [ESsample ([LvIdent ["a"]], dmap); ESreturn (ec_ident "a")];
        }
    in
    if Sint.is_empty !(env.randombytes) then []
    else [
        ImoduleType {
            name = syscall_mod_sig;
            funs = List.map (randombytes_decl "_") (Sint.elements !(env.randombytes));
        };
        Imodule {
            name = syscall_mod;
            params = [];
            ty = Some syscall_mod_sig;
            vars = [];
            funs = List.map randombytes_f (Sint.elements !(env.randombytes));
        }
    ]

let toec_prog pd asmOp model globs funcs arrsz warrsz randombytes array_dir =
    let add_glob_env env (x, d) = add_glob (add_glob_arrsz env (x, d)) x in
    let env = empty_env pd model funcs arrsz warrsz randombytes
        |> fun env -> List.fold_left add_glob_env env globs
        |> fun env -> List.fold_left add_arrsz env funcs
    in

    let funs = List.map (toec_fun asmOp env) funcs in

    begin
      match array_dir with
    | Some prefix ->
        begin
          Sint.iter (pp_array_decl ~prefix) !(env.arrsz);
          Sint.iter (pp_warray_decl ~prefix) !(env.warrsz)
        end
    | None -> ()
    end;

    let pp_arrays arr s = match Sint.elements s with
        | [] -> []
        | l -> [IrequireImport (List.map (Format.sprintf "%s%i" arr) l)]
    in
    let pp_leakages = match model with
        | ConstantTime -> [("leakages", "leakages_t")]
        | Normal -> []
    in
    let mod_arg =
        if Sint.is_empty !(env.randombytes) then []
        else [(syscall_mod_arg, syscall_mod_sig)]
    in
    let import_jleakage = match model with
    | Normal -> []
    | ConstantTime -> [IfromRequireImport ("Jasmin", ["JLeakage"])]
    in
    let glob_imports = [
        IrequireImport ["AllCore"; "IntDiv"; "CoreMap"; "List"; "Distr"];
        IfromRequireImport ("Jasmin", [jmodel ()]);
        Iimport [lib_slh ()];
    ] in
    let top_mod = Imodule {
        name = "M";
        params = mod_arg;
        ty = None;
        vars = pp_leakages;
        funs;
    } in
    glob_imports @
    import_jleakage @
    (pp_arrays "Array" !(env.arrsz)) @
    (pp_arrays "WArray" !(env.warrsz)) @
    (List.map (fun glob -> ec_glob_decl env glob) globs) @
    (ec_randombytes env) @
    [top_mod]

let pp_prog pd asmOp fmt model globs funcs arrsz warrsz randombytes array_dir =
    pp_ec_prog fmt (toec_prog pd asmOp model globs funcs arrsz warrsz randombytes array_dir);
    Format.fprintf fmt "@."

let rec used_func f = 
  used_func_c Ss.empty f.f_body 

and used_func_c used c = 
  List.fold_left used_func_i used c

and used_func_i used i = 
  match i.i_desc with
  | Cassgn _ | Copn _ | Csyscall _ -> used
  | Cif (_,c1,c2)     -> used_func_c (used_func_c used c1) c2
  | Cfor(_,_,c)       -> used_func_c used c
  | Cwhile(_,c1,_,c2)   -> used_func_c (used_func_c used c1) c2
  | Ccall (_,f,_)   -> Ss.add f.fn_name used

let extract ((globs,funcs):('info, 'asm) prog) pd asmOp model fnames array_dir fmt =
  let fnames =
    match fnames with
    | [] -> List.map (fun { f_name ; _ } -> f_name.fn_name) funcs
    | fnames -> fnames
  in
  let funcs = List.map Regalloc.fill_in_missing_names funcs in
  let tokeep = ref (Ss.of_list fnames) in
  let dofun f = 
    if Ss.mem f.f_name.fn_name !tokeep then
      (tokeep := Ss.union (used_func f) !tokeep; true)
    else false in
  let funcs = List.rev (List.filter dofun funcs) in
  let arrsz = ref Sint.empty in
  let warrsz = ref Sint.empty in
  let randombytes = ref Sint.empty in
  pp_prog pd asmOp fmt model globs funcs arrsz warrsz randombytes array_dir
