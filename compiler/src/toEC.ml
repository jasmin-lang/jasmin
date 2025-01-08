open Utils
open Wsize
open Prog
open PrintCommon
module E = Expr

module Ec = struct

  type ec_op2 =
    | ArrayGet
    | Plus
    | Infix of string

  type ec_op3 =
    | Ternary
    | If
    | InORange

  type quantif =
    | Lforall
    | Lexists
    | Llambda

  type ec_ident = string list

  type ec_ty =
    | Base of string
    | Tuple of ec_ty list

  type ec_var = string * ec_ty

  type ec_expr =
    | Equant  of quantif * string list * ec_expr (*use ec_var list for binders*)
    | Econst of Z.t (* int. literal *)
    | Ebool of bool (* bool literal *)
    | Eident of ec_ident (* variable *)
    | Eapp of ec_expr * ec_expr list (* op. application *)
    | Eop2 of ec_op2 * ec_expr * ec_expr (* binary operator *)
    | Eop3 of ec_op3 * ec_expr * ec_expr * ec_expr (* ternary operator *)
    | Elist of ec_expr list (* list litteral *)
    | Etuple of ec_expr list (* tuple litteral *)
    | Eproj  of ec_expr * int  (* projection of a tuple *)
    | EHoare of ec_ident * ec_expr * ec_expr

  type ec_fun_decl = {
    fname: string;
    args: ec_var list;
    rtys: ec_ty;
  }

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

  type ec_fun = {
    decl: ec_fun_decl;
    locals: ec_var list;
    stmt: ec_stmt;
  }

  type ec_modty = string

  type ec_module_type = {
    name: ec_modty;
    funs: ec_fun_decl list;
  }

  type ec_module = {
    name: string;
    params: (string * ec_modty) list;
    ty: ec_modty option;
    vars: ec_var list;
    funs: ec_fun list;
  }

  type ec_proposition =  string * string list * ec_expr

  type ec_tactic_args =
    | Conti of ec_tactic
    | Seq of ec_tactic
    | Param of ec_tactic_args list
    | Form of ec_proposition
    | Ident of ec_ident
    | Pattern of string
    | Prop of string
    | DProp of ec_expr
    | Comment of string

  and ec_tactic =
    { tname : string;
      targs : ec_tactic_args list;
      (* subgoals : ec_tactic list *)
    }

  type ec_proof = ec_tactic list

  type ec_item =
    | IrequireImport of string list
    | Iimport of string list
    | IfromImport of string * (string list)
    | IfromRequireImport of string * (string list)
    | Iabbrev of string * ec_expr
    | ImoduleType of ec_module_type
    | Imodule of ec_module
    | Icomment of string (* comment line *)
    | Axiom of  ec_proposition
    | Lemma of ec_proposition * ec_proof

  type ec_prog = ec_item list

  (* Printer*)

  let ec_print_i z =
    if Z.leq Z.zero z then Z.to_string z
    else Format.asprintf "(%a)" Z.pp_print z

  let pp_option pp fmt = function
    | Some x -> pp fmt x
    | None -> ()

  let pp_list_paren sep pp fmt xs =
    if xs = [] then ()
    else pp_paren (pp_list sep pp) fmt xs

  let pp_Tsz sz = Format.asprintf "W%i" (int_of_ws sz)

  let pp_sz_t sz = Format.sprintf "W%i.t" (int_of_ws sz)

  let pp_ec_ident fmt ident = Format.fprintf fmt "@[%a@]" (pp_list "." pp_string) ident

  let string_of_quant = function
    | Lforall -> "forall"
    | Lexists -> "exists"
    | Llambda -> "fun"

  let rec pp_ec_ty fmt ty =
    match ty with
    | Base t -> Format.fprintf fmt "%s" t
    | Tuple tl ->
      if tl = [] then Format.fprintf fmt "unit"
      else Format.fprintf fmt "@[(%a)@]" (pp_list " *@ " pp_ec_ty) tl

  let rec pp_ec_ast_expr fmt e = match e with
    | Econst z -> Format.fprintf fmt "%s" (ec_print_i z)
    | Ebool b -> pp_bool fmt b
    | Eident s -> pp_ec_ident fmt s
    | Eapp (f, ops) ->
            Format.fprintf fmt "@[(@,%a@,)@]"
            (Format.(pp_print_list ~pp_sep:(fun fmt () -> fprintf fmt "@ ")) pp_ec_ast_expr)
            (f::ops)
    | Eop2 (op, e1, e2) -> pp_ec_op2 fmt (op, e1, e2)
    | Eop3 (op, e1, e2, e3) -> pp_ec_op3 fmt (op, e1, e2, e3)
    | Elist es -> Format.fprintf fmt "@[[%a]@]" (pp_list ";@ " pp_ec_ast_expr) es
    | Etuple es -> Format.fprintf fmt "@[(%a)@]" (pp_list ",@ " pp_ec_ast_expr) es
    | Equant (q, i, f) ->
      begin
        match q with
        | Llambda ->
          Format.fprintf fmt "@[(%s %a =>@ %a)@]"
            (string_of_quant q) (pp_list " " pp_string) i pp_ec_ast_expr f
        | _ ->
          Format.fprintf fmt "@[%s %a,@ %a@]"
            (string_of_quant q) (pp_list " " pp_string) i pp_ec_ast_expr f
      end
    | Eproj (e,i) -> Format.fprintf fmt "@[%a.`%i@]" pp_ec_ast_expr e i
    | EHoare (i,fpre,fpost) ->
      Format.fprintf fmt "@[hoare [%a :@ @[%a ==>@ %a@]]@]"
        pp_ec_ident i
        (pp_ec_ast_expr) fpre
        (pp_ec_ast_expr) fpost

  and pp_ec_op2 fmt (op2, e1, e2) =
    let f = match op2 with
      | ArrayGet -> Format.fprintf fmt "@[%a.[%a]@]"
      | Plus -> Format.fprintf fmt "@[(%a +@ %a)@]"
      | Infix s -> (fun pp1 e1 -> Format.fprintf fmt "@[(%a %s@ %a)@]" pp1 e1 s)
    in
    f pp_ec_ast_expr e1 pp_ec_ast_expr e2

  and pp_ec_op3 fmt (op, e1, e2, e3) =
    let f = match op with
      | Ternary -> Format.fprintf fmt "@[(%a ? %a : %a)@]"
      | If -> Format.fprintf fmt "@[(if %a then %a else %a)@]"
      | InORange -> Format.fprintf fmt "@[(%a <= %a < %a)@]"
    in
    f pp_ec_ast_expr e1 pp_ec_ast_expr e2 pp_ec_ast_expr e3

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
    | ESasgn (lv, e) ->
      Format.fprintf fmt "@[%a <-@ %a;@]" pp_ec_lvalues lv pp_ec_ast_expr e
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
    | ESsample (lv, e) ->
      Format.fprintf fmt "@[%a <$@ %a;@]" pp_ec_lvalues lv pp_ec_ast_expr e
    | ESif (e, c1, c2) ->
      Format.fprintf fmt "@[<v>if (%a) {@   %a@ } else {@   %a@ }@]"
        pp_ec_ast_expr e pp_ec_ast_stmt c1 pp_ec_ast_stmt c2
    | ESwhile (e, c) ->
      Format.fprintf fmt "@[<v>while (%a) {@   %a@ }@]"
        pp_ec_ast_expr e pp_ec_ast_stmt c
    | ESreturn e -> Format.fprintf fmt "@[return %a;@]" pp_ec_ast_expr e
    | EScomment s -> Format.fprintf fmt "@[(* %s *)@]" s

  let pp_ec_vdecl fmt (x, ty) = Format.fprintf fmt "%s:%a" x pp_ec_ty ty

  let pp_ec_fun_decl fmt fdecl =
    Format.fprintf fmt
      "@[proc %s (@[%a@]) : @[%a@]@]"
      fdecl.fname
      (pp_list ",@ " pp_ec_vdecl) fdecl.args
      pp_ec_ty fdecl.rtys

  let pp_ec_fun fmt f =
    let pp_decl_s fmt v = Format.fprintf fmt "var %a;" pp_ec_vdecl v in
    Format.fprintf fmt
      "@[<v>@[%a = {@]@   @[<v>%a@ %a@]@ }@]"
      pp_ec_fun_decl f.decl
      (pp_list "@ " pp_decl_s) f.locals
      pp_ec_ast_stmt  f.stmt

  let pp_ec_propostion fmt (n, b, e) =
    Format.fprintf fmt "@[%s @[%a@] :@ @[%a@]@]"
      n
      (pp_list " " pp_string) b
      pp_ec_ast_expr e

  let rec pp_ec_tatic_args fmt args =
    match args with
    | Conti t -> Format.fprintf fmt "@[%a@]" pp_ec_rtactic t
    | Seq t -> Format.fprintf fmt "@[; %a@]" pp_ec_rtactic t
    | Param a -> Format.fprintf fmt "(@[%a@])" (pp_list " " pp_ec_tatic_args) a
    | Form f -> Format.fprintf fmt "@[%a@]" pp_ec_propostion f
    | Ident i -> Format.fprintf fmt "@[%a@]" pp_ec_ident i
    | Pattern s -> Format.fprintf fmt "@[%s@]" s
    | Prop s -> Format.fprintf fmt "@[%s@]" s
    | DProp e -> Format.fprintf fmt "@[%a@]" pp_ec_ast_expr e
    | Comment s -> Format.fprintf fmt "@[(* %s *)@]" s

  and pp_ec_rtactic fmt t =
    Format.fprintf fmt "@[%s @[%a@]@]" t.tname (pp_list " " pp_ec_tatic_args) t.targs

  let pp_ec_tactic fmt t =
    Format.fprintf fmt "@[%a@]." pp_ec_rtactic t

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
        (pp_list "@ " (fun fmt (v, t) -> Format.fprintf fmt "@[var %s : %a@]" v pp_ec_ty t)) m.vars
        (fun fmt _ -> if m.vars = [] then (Format.fprintf fmt "") else (Format.fprintf fmt "@ ")) ()
        (pp_list "@ " pp_ec_fun) m.funs
    | Icomment s -> Format.fprintf fmt "@[(* %s *)@]" s
    | Axiom p ->
      Format.fprintf fmt "@[axiom @[%a@].@]" pp_ec_propostion p
    | Lemma (p, t) ->
      Format.fprintf fmt "@[lemma @[%a@].@]@ @[proof.@]@ @[<v>%a@]"
        pp_ec_propostion p
        (pp_list "@ "pp_ec_tactic) t

  let pp_ec_prog fmt prog =
    Format.fprintf fmt "@[<v>%a@]" (pp_list "@ @ " pp_ec_item) prog;
    Format.fprintf fmt "@."

end

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

type proofvar = {
  trace_ : Ss.elt;
}

type ('len) env = {
  pd : Wsize.wsize;
  model : model;
  alls : Ss.t;
  vars : string Mv.t;
  glob : (string * ty) Ms.t;
  funs : (string * (ty list * ty list)) Mf.t;
  tmplvs : ('len CoreIdent.gvar list) Mf.t;
  ttmplvs : (Ss.elt * Ec.ec_ty) Mf.t;
  old : (Ss.elt list) Mf.t ref;
  contra : ('len Prog.gfcontract * 'len CoreIdent.gvar list) Mf.t;
  arrsz  : Sint.t ref;
  warrsz : Sint.t ref;
  auxv  : string list Mty.t;
  randombytes : Sint.t ref;
  proofv : proofvar Mf.t ref;
  func : funname option;
  sign : bool
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
  | Pbig (ei, _, _, e, e1, e2) ->
    leaks_e_rec pd (leaks_e_rec pd (leaks_e_rec pd (leaks_e_rec pd leaks e1) e2) ei) e

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
  ; "choare"
  ; "cost"
  ; "phoare"
  ; "islossless"
  ; "async"

  ; "try"
  ; "first"
  ; "last"
  ; "do"
  ; "strict"
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
  ; "schema"
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
  ; "nosmt"
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
  ; "instantiate"
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

let set_name env s =
  let s = create_name env s in
  s , {env with alls = Ss.add s env.alls}

let normalize_name n =
  n |> String.uncapitalize_ascii |> escape

let mkfunname env fn =
  fn.fn_name |> normalize_name |> create_name env

let empty_env pd model fds arrsz warrsz randombytes sign =

  let env = {
    pd;
    model;
    alls = keywords;
    vars = Mv.empty;
    glob = Ms.empty;
    funs = Mf.empty;
    tmplvs = Mf.empty;
    ttmplvs = Mf.empty;
    old = ref Mf.empty;
    contra = Mf.empty;
    arrsz;
    warrsz;
    auxv  = Mty.empty;
    randombytes;
    proofv = ref Mf.empty;
    func = None;
    sign
  } in

  (*  let mk_tys tys = List.map Conv.cty_of_ty tys in *)
  let add_fun env fd =
    let s = mkfunname env fd.f_name in
    let funs =
      Mf.add fd.f_name (s, ((*mk_tys*) fd.f_tyout, (*mk_tys*)fd.f_tyin)) env.funs in
    { env with funs; alls = Ss.add s env.alls } in

  let env = List.fold_left add_fun env fds in

  let add_fun_contra env fd =
    match fd.f_contra with
    | None -> env
    | Some c ->
      begin
        let contra =
          let args = fd.f_args in
          Mf.add fd.f_name (c,args) env.contra
        in
        { env with contra }
      end
  in
  List.fold_left add_fun_contra env fds

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
  Conv.ty_of_cty (snd (E.type_of_opNA op))

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
  | Pbig (_, op, _, _, _, _) -> out_ty_op2 op

let check_array env x =
  match (L.unloc x).v_ty with
  | Arr(ws, n) -> Sint.mem n !(env.arrsz) && Sint.mem (arr_size ws n) !(env.warrsz)
  | _ -> true

let ec_vars env (x:var) = Mv.find x env.vars

module Exp = struct

  open Ec

  let ec_ident s = Eident [s]

  let ec_vari env (x:var) = Eident [ec_vars env x]

  let ec_aget a i = Eop2(ArrayGet, a, i)

  let ec_int x = Econst (Z.of_int x)

  let glob_mem = ["Glob"; "mem"]
  let glob_memi = Eident glob_mem

  let pd_uint env =
    if env.sign then
      Eident [Format.sprintf "W%d" (int_of_ws env.pd); "to_int"]
    else
      Eident [Format.sprintf "W%d" (int_of_ws env.pd); "to_uint"]

  let ec_apps1 s e = Eapp (ec_ident s, [e])

  let iIdent i = ec_ident (Format.sprintf "%i" i)

  let fmt_Array n = Format.sprintf "Array%i" n

  let fmt_WArray n = Format.sprintf "WArray%i" n

  let ec_Array env n = add_Array env n; fmt_Array n

  let ec_WArray env n = add_WArray env n; fmt_WArray n

  let ec_Array_init env len = Eident [ec_Array env len; "init"]

  let ec_WArray_init env ws n =
    Eident [ec_WArray env (arr_size ws n); Format.sprintf "init%i" (int_of_ws ws)]

  let ec_WArray_initf env ws n f =
    let i = create_name env "i" in
    Eapp (ec_WArray_init env ws n, [Equant (Llambda ,[i], f i)])

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
        let init_fun =
          Equant (Llambda, [i], Eapp (geti, [ec_initi env (e, ne, wse); ec_ident i]))
        in
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

  let pp_access aa = if aa = Warray_.AAdirect then "_direct" else ""

  let toec_ty ty = match ty with
    | Bty Bool -> "bool"
    | Bty Int  -> "int"
    | Bty (U ws) -> (pp_sz_t ws)
    | Bty (Abstract s) -> s
    | Arr(ws,n) -> Format.sprintf "%s %s.t" (pp_sz_t ws) (fmt_Array n)

  let rec toec_cast env ty e = ec_cast env (ty, ty_expr e) (toec_expr env e)

  and ec_wcast env (ty, e) = toec_cast env ty e

  and toec_expr env (e: expr) =
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
            Equant (Llambda, [i],
                    ec_aget (ec_vari env x)  (Eop2 (Plus, toec_expr env e, ec_ident i)))
          ])
      else
        Eapp (
          ec_Array_init env len,
          [
            Equant (Llambda, [i],
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

    | PappN (OopN op, es) ->

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

    | PappN (Oabstract opa, es) ->
      Eapp (ec_ident opa.pa_name, List.map (toec_expr env) es)

    | Pbig (i, op, v, e, a, b) ->
      let v = L.unloc v in
      let env = add_var env v in
      let op = Infix (Format.asprintf "%a" pp_op2 op) in
      let acc = "acc" and x = "x" in
      let ty = ty_expr i in
      let ty = toec_ty ty in
      let facc = "(" ^ acc ^ ":" ^ ty ^  ")" in
      let expr = Eop2 (op, Eident [x], Eident [acc]) in
      let lambda1 = Equant (Llambda, [facc], expr) in
      let lambda1 = Equant (Llambda, [x], lambda1) in
      let i = toec_expr env i in
      let a = toec_expr env a in
      let b = toec_expr env b in
      let e = toec_expr env e in
      let lambda2 = Equant(Llambda, [ec_vars env v],e) in
      let iota = Eapp (ec_ident "iota_", [a; b]) in
      let map = Eapp (ec_ident "map", [lambda2;iota]) in
      Eapp (ec_ident "foldr", [lambda1;i; map])
end

open Ec
open Exp

let base_op = function
  | Sopn.Oasm (Arch_extra.BaseOp (_, o)) -> Sopn.Oasm (Arch_extra.BaseOp(None,o))
  | o -> o

let all_vars lvs =
  let is_lvar = function Lvar _ -> true | _ -> false in
  List.for_all is_lvar lvs

let check_lvals lvs = all_vars lvs

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
    let addr =
      Eapp (pd_uint env, [ec_wcast env (add_ptr env.pd (gkvar x) e1)])
    in
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
      let updwa =
        Eapp (waset, [ec_initi_var env (x, n, xws); toec_expr env e1; e])
      in
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
            Equant (Llambda, [i], Eop3 (
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
      let in_range =
        Eop3 (InORange, start, ec_ident i, Eop2 (Plus, start, ec_int len8))
      in
      let ainit = Eident [ec_WArray env nws8; "init8"] in
      let aw_get8 len = Eident [ec_WArray env len; "get8"] in
      let at =
        Eapp (aw_get8 len8,
              [ec_initi env (e, len, ws); Eop2 (Infix "-",
                                                ec_ident i,
                                                start)])
      in
      let ae =
        Eapp (aw_get8 nws8, [ec_initi_var env (x, n, xws); ec_ident i])
      in
      let a = Eapp (ainit, [Equant (Llambda, [i], Eop3 (If, in_range, at, ae))]) in
      let wag = Eident [ec_WArray env nws8; Format.sprintf "get%i" (int_of_ws xws)] in
      ESasgn (
        [LvIdent [ec_vars env x]],
        Eapp (ec_Array_init env n, [Eapp (wag, [a])])
      )

module Annotations  = struct

  let fand a b = Eop2 (Infix "/\\", a, b)

  let ec_kind = function
    | Expr.Assume -> ["Assume"]
    | Assert -> ["Assert"]
    | _ -> assert false

  let ec_trace env k e =
    let k = ec_kind k in
    let f = Option.get env.func in
    let p = Mf.find f !(env.proofv) in
    let e = toec_expr env e in
    let e1 = Eop2 (Infix "++", Eident [p.trace_], Elist [Etuple [Eident k;e]]) in
    let i = ESasgn ([LvIdent ([p.trace_])],e1) in
    [i]

  let sub_contra args params =
    let aux f =
      List.map (fun (prover,clause) -> prover, f clause)
    in
    let check v vi=
      (L.unloc v.gv).v_name = vi.v_name && (L.unloc v.gv).v_id = vi.v_id
    in
    let aux1 v =
      match List.findi (fun _ vi -> check v vi) args with
      | i,_ ->
        let _,e = List.findi (fun ii _ -> ii = i) params in
        e
      | exception _ ->  Pvar v
    in
    aux (Subst.gsubst_e (fun ?loc:_ x -> x) aux1)


  let toec_fun env lvs f es =
    let otys, itys = get_funtype env f in
    let args = List.map (ec_wcast env) (List.combine itys es) in

    let tmps = Mf.find f env.tmplvs in
    let ttmpt,_ = Mf.find f env.ttmplvs in
    let (contr,formals) = Mf.find f env.contra in

    let lvs2 = List.map (fun v -> Lvar (L.mk_loc L._dummy v)) tmps in

    let elvs2 =
      List.map (fun v ->
          Pvar({gv = L.mk_loc L._dummy v; gs = Expr.Slocal})
        ) tmps
    in

    let iparams = List.map L.unloc contr.f_iparams in
    let pre = sub_contra iparams es contr.f_pre in
    let pre = List.map (fun (_,e) -> e) pre in

    let post = sub_contra iparams es contr.f_post in
    let ires = List.map L.unloc contr.f_ires in
    let tmps =
      List.map
        (fun x-> Pvar {gv=L.mk_loc L._dummy x; gs=E.Slocal})
        tmps
    in
    let post = sub_contra ires tmps post in
    let post = List.map (fun (_,e) -> e) post in

    let i = List.fold (fun acc pre -> ec_trace env Assert pre @ acc ) [] pre in

    let i = i @
      [EScall ([LvIdent [ttmpt] ; LvIdent ["tmp__trace"]], [get_funname env f], args)]
    in
    let i = i @ [ESasgn( ec_lvals env lvs2, Eident [ttmpt])] in
    let current_f = Option.get env.func in
    let p = Mf.find current_f !(env.proofv) in
    let e1 =
      Eop2 (Infix "++", Eident [p.trace_], Eident["tmp__trace"])
    in
    let i = i @ [ESasgn ([LvIdent ([p.trace_])],e1)] in
    let i = List.fold_left (fun acc post -> acc @ ec_trace env Assume post ) i post in
    List.fold_left2
      (fun acc lv e ->
         let e = toec_cast env (ty_lval lv) e in
         acc @ [toec_lval1 env lv e])
      i lvs elvs2

  let contrat env c =
    let c = List.map (fun (_,x) -> x) c in
    if List.is_empty c then
      Ebool true
    else
      let c = List.map (toec_expr env) c in
      List.fold_left (fun acc a -> Eop2 (Infix "/\\", a, acc) ) (List.hd c) (List.tl c)

  let var_eq vars1 vars2 =
    let vars = List.map2 (fun a b -> (a,b)) vars1 vars2 in
    if List.is_empty vars then
      Ebool true
    else
      let eq (var1,var2) =
        Eop2 (Infix "=", ec_ident var1, ec_ident  var2.v_name)
      in
      List.fold_left
        (fun acc a -> Eop2 (Infix "/\\", eq a, acc))
        (eq (List.hd vars))
        (List.tl vars)

  let var_eq2 vars1 vars2 =
    let vars = List.map2 (fun a b -> (a,b)) vars1 vars2 in
    if List.is_empty vars then
      Ebool true
    else
      let eq (var1,var2) =
        Eop2 (Infix "=", ec_ident var1, ec_ident  var2)
      in
      List.fold_left
        (fun acc a -> Eop2 (Infix "/\\", eq a, acc))
        (eq (List.hd vars))
        (List.tl vars)

  let mk_old_param env params iparams =
    List.fold_left2 (fun (env,acc) v iv ->
        let s = String.uncapitalize_ascii v.v_name in
        let s = "_" ^ s in
        let s,env = set_name env s in
        let env = set_var env iv s in
        env, s :: acc
      ) (env,[]) (List.rev params) (List.rev iparams)

  let res = Eident ["res"]

  let get_pre = function
    | None -> []
    | Some f -> f.f_pre

  let get_post = function
    | None -> []
    | Some f -> f.f_post

  let get_iparams = function
    | None -> []
    | Some f -> f.f_iparams

  let get_ires = function
    | None -> []
    | Some f -> f.f_ires


  let update_res_env env f ires =
    List.fold_lefti
      (fun env i res ->
         let s = "res.`1" in
         let s =
           if List.length f.f_tyout > 1 then
             s ^ ".`" ^ string_of_int (i+1)
           else s
         in
         set_var env res s)
      env ires

  
  let pp_valid_post env f =
    let fname = get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let ires = get_ires f.f_contra in
    let ires = List.map L.unloc ires in
    let env1 = update_res_env env f ires in

    let pre = var_eq vars f.f_args in

    let post = contrat env1 (get_post f.f_contra) in

    let rec aux acc = function
      | Equant (_ , _ , e) -> aux acc e
      | Eident i -> i :: acc
      | Eapp (e, el) -> List.fold_left aux (aux acc e) el
      | Eop2 (_, e1, e2) -> aux (aux acc e1) e2
      | Eop3 (_, e1, e2, e3) -> aux (aux (aux acc e1) e2) e3
      | Elist el -> List.fold_left aux acc el
      | Etuple el -> List.fold_left aux acc el
      | Eproj (e, _) -> aux acc e
      | EHoare (_ ,e1, e2) -> aux (aux acc e1) e2
      | _ -> acc
    in

    let acc = aux [] post in

    let filter  = function
      | s :: _ ->
        if String.count_string s "res" > 0 then true else false
      | _ -> false
    in
    let acc = List.filter filter acc in
    let eq a b =
      match a, b with
      | s1 :: _ , s2 :: _ -> String.equal s1 s2
      | _ -> false
    in
    let acc = List.unique ~eq acc in

    let trace = Eapp(Eident ["trace"],[res]) in
    let valid_trace = Eapp(Eident ["valid"], [trace]) in
    let post = Eop2 (Infix "=>", valid_trace, post) in

    let name = Format.asprintf "%s_valid_post" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in

    let tactic = {
      tname = "proc";
      targs = []
    }
    in

    let tactic1 = {
      tname = "wp";
      targs = [Pattern "-1"; Pattern "=>"; Pattern "/="]
    }
    in

    let old = Mf.find f.f_name !(env.old) in
    let e = var_eq2 vars old in

    let tactic2 = {
      tname = "conseq";
      targs = [Param [Pattern ":"; Pattern " _"; Pattern "==>"; DProp e]]
    }
    in

    let i = 1 + List.length acc  in
    let p = string_of_int i ^ "?" in

    let tactic3 =
      {
        tname = "move";
        targs = [Pattern "=>"; Pattern "?"; Pattern "_"; Pattern "/>"; Pattern p]
      }
    in

    let tactic4 =
      {
        tname = "rewrite";
        targs = [Prop "/trace"; Pattern "/="; Prop "valid_cat";
                 Prop "/valid"; Pattern "//="]
      }
    in

    let i = List.length f.f_args in
    let i = string_of_int i in
    let tactic5 =
      {
        tname = "seq";
        targs = [Pattern i; Pattern ":"; Param [DProp e]]
      }
    in
    let tactic6 =
      {
        tname = "auto";
        targs = []
      }
    in

    let tactic7 =
      {
        tname = "by";
        targs = [Conti tactic6]
      }
    in
    let tactic8 =
      {
        tname = "conseq";
        targs = []
      }
    in
    let tactic9 =
      {
        tname = "by";
        targs = [Conti tactic8; Pattern "/>"]
      }
    in
    let tactic10 = {
      tname ="qed";
      targs = []
    }
    in

    Lemma (prop, [tactic; tactic1; tactic2; tactic3; tactic4;
                  tactic5; tactic7; tactic9; tactic10])

  let pp_valid_assume_ env f =
    let fname = get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let pre = var_eq vars f.f_args in

    let p = contrat env (get_pre f.f_contra) in

    let trace = Eapp(Eident ["trace"],[res]) in
    let valid_assume_trace = Eapp(Eident ["validk"], [Eident ["Assume"]; trace]) in
    let post = Eop2 (Infix "=>", p, valid_assume_trace) in

    let name = Format.asprintf "%s_assume_" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in

    let tactic = {
      tname = "admitted";
      targs = [Comment "TODO"];
    }
    in

    Lemma (prop, [tactic])

  let pp_valid_assume env f =
    let fname = get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let ires = get_ires f.f_contra in
    let ires = List.map L.unloc ires in
    let env1 = update_res_env env f ires in

    let pre = var_eq vars f.f_args in
    let p = contrat env (get_pre f.f_contra) in

    let post = contrat env1 (get_post f.f_contra) in
    let trace = Eapp(Eident ["trace"],[res]) in
    let valid_trace = Eapp(Eident ["valid"], [trace]) in
    let post1 = Eop2 (Infix "=>", valid_trace, post) in

    let valid_assume_trace = Eapp(Eident ["validk"], [Eident ["Assume"]; trace]) in
    let post2 = Eop2 (Infix "=>", p, valid_assume_trace) in

    let post = Eop2 (Infix "/\\", post1, post2) in

    let name = Format.asprintf "%s_assume" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in

    let name1 = Format.asprintf "%s_assume_" fname in
    let vars = List.map (fun x -> Ident [x]) vars in
    let param1 = Prop name1 :: vars in
    let name2 = Format.asprintf "%s_valid_post" fname in
    let param2 = Prop name2 :: vars in


    let tactic1 = {
      tname ="conseq";
      targs = [Param (param1); Param (param2) ; Pattern "=>"; Pattern "/>"]
    }
    in

    let tactic2 = {
      tname ="qed";
      targs = []
    }
    in

    Lemma (prop, [tactic1; tactic2])

  let pp_valid_assert env f =
    let fname = get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let f1 = var_eq vars f.f_args in
    let f2 = contrat env (get_pre f.f_contra) in
    let pre = fand f1 f2 in

    let trace = Eapp(Eident ["trace"],[res]) in
    let post = Eapp(Eident ["validk"], [Eident ["Assert"]; trace]) in

    let name = Format.asprintf "%s_assert" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in

    let tactic = {
      tname = "admitted";
      targs = [Comment "Prove by Cryptoline"];
    }
    in

    Lemma (prop, [tactic])

  let pp_spec env f =
    let fname = get_funname env f.f_name in

    let iparams = get_iparams f.f_contra in
    let iparams = List.map L.unloc iparams in
    let env,vars = mk_old_param env f.f_args iparams in

    let ires = get_ires f.f_contra in
    let ires = List.map L.unloc ires in
    let env1 = update_res_env env f ires in

    let f1 = var_eq vars f.f_args in
    let f2 = contrat env (get_pre f.f_contra) in
    let pre = fand f1 f2 in

    let post = contrat env1 (get_post f.f_contra) in

    let name = Format.asprintf "%s_spec" fname in

    let form = EHoare (["M";fname], pre, post) in
    let prop = (name, vars, form) in


    let name1 = Format.asprintf "%s_assume" fname in
    let vars = List.map (fun x -> Ident [x]) vars in
    let param1 = Prop name1 :: vars in
    let name2 = Format.asprintf "%s_assert" fname in
    let param2 = Prop name2 :: vars in


    let tactic1 = {
      tname ="conseq";
      targs = [Param (param1); Param (param2) ; Pattern "=>"; Pattern "/>"]
    }
    in

    let tactic2 ={
      tname = "smt";
      targs = [Param [Prop "all_validk_valid"]]
    }
    in

    let tactic3 = {
      tname ="qed";
      targs = []
    }
    in

    Lemma (prop, [tactic1;tactic2;tactic3])

  let proof env funcs =
    let p1 = List.map (pp_valid_post env) funcs in
    let p2 = List.map (pp_valid_assume_ env) funcs in
    let p3 = List.map (pp_valid_assume env) funcs in
    let p4 = List.map (pp_valid_assert env) funcs in
    let p5 = List.map (pp_spec env) funcs in
    let c1 = Icomment "The post is in the trace." in
    let c2 = Icomment "All assumes are valid." in
    let c3 = Icomment "The post is in the trace and all assumes are valid." in
    let c4 = Icomment "All assert are valid." in
    let c5 = Icomment "Final specification for the functions." in
    (c1 :: p1) @ (c2 :: p2) @ (c3 :: p3) @ (c4 :: p4) @ (c5 :: p5)

  let add_proofv env f p =
    env.proofv := Mf.add f p !(env.proofv)

  let get_funcontr env f = Mf.find f env.contra

  let ec_tmp_lvs env f =
    let fn = f.f_name in
    let otys, itys = get_funtype env fn in
    let env,tmps =
        List.fold_left_map (fun env ty ->
            let name = "tmp__" ^ fn.fn_name in
            let s = normalize_name name in
            let s = create_name env s in
            let v = CoreIdent.GV.mk s (Wsize.Stack Direct) ty L._dummy [] in
            let env =
              { env with
                alls = Ss.add s env.alls;
                vars = Mv.add v s env.vars
              }
            in
            env, v
          ) env otys
    in
    let env = {env with tmplvs = Mf.add fn tmps env.tmplvs} in
    let tmps = List.map (fun x -> x.v_name, Base (toec_ty x.v_ty)) tmps in

    let name = "tmp__data_" ^ fn.fn_name in
    let s = normalize_name name in
    let s, env = set_name env s in
    let tmp =
      (s, Tuple(List.map (fun x -> Base (toec_ty x)) f.f_tyout))
    in
    let env = {env with ttmplvs = Mf.add fn tmp env.ttmplvs} in

    let tmps =
      (s, Tuple(List.map (fun x -> Base (toec_ty x)) f.f_tyout)) :: tmps
    in

    env,tmps

  let ec_vars env f =
    let fname = get_funname env f.f_name in
    let trace_, env = set_name env ("trace_" ^ fname) in

    let proofv = {trace_} in

    add_proofv env f.f_name proofv;

    let env = { env with func = Some f.f_name} in
    let vars =
      [trace_, Base "trace"]
    in
    env, vars

  let proof_var_init env f =
    let proofv = Mf.find f.f_name !(env.proofv) in

    [ESasgn ([LvIdent [proofv.trace_]], Elist [])]

  let check_vars env f =
    let proofv = Mf.find f.f_name !(env.proofv) in
    Eident [proofv.trace_]

  let import = [IfromRequireImport ("Jasmin",["Jcheck"])]

  let trans annot =
    let l =
      ["t", true ; "f", false]
    in
    let mk_trans = Annot.filter_string_list None l in
    let atran annot =
      match Annot.ensure_uniq1 "signed" mk_trans annot with
      | None -> false
      | Some s -> s
    in
    atran annot

  let sign env f =
    let sign = trans f.f_annot.f_user_annot in
    {env with sign}

end

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
    List.map Conv.ty_of_cty (Sopn.sopn_tout Build_Tabstract pd asmOp op),
    List.map Conv.ty_of_cty (Sopn.sopn_tin Build_Tabstract pd asmOp op)

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
  | Cassert _ -> false

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
    | Cassert _ -> i.i_desc
  in
  { i with i_desc }
and remove_for c = List.map remove_for_i c

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
                Equant (Llambda, [i], Eop3 (
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
        let a = Eapp (ainit, [Equant (Llambda, [i], Eop3 (If, in_range, at, ae))]) in
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
        | Normal | Annotations -> env
        | ConstantTime -> add_aux (add_aux env [ty_lval lv]) [ty_expr e]
      )
    | Cassert _ -> env
    | Copn (lvs, _, op, _) -> (
        match env.model with
        | Normal | Annotations ->
            if List.length lvs = 1 then env
            else
                let tys  = List.map Conv.ty_of_cty (Sopn.sopn_tout Build_Tabstract pd asmOp op) in
                let ltys = List.map ty_lval lvs in
                if all_vars lvs && ltys = tys then env
                else add_aux env tys
        | ConstantTime ->
            let op = base_op op in
            let tys  = List.map Conv.ty_of_cty (Sopn.sopn_tout Build_Tabstract pd asmOp op) in
            let env = add_aux env tys in
            add_aux env (List.map ty_lval lvs)
    )
    | Ccall(lvs, f, _) -> (
        match env.model with
        | Normal | Annotations ->
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
        | Normal | Annotations ->
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
    | Normal | Annotations -> []

let ec_leaks_es env es =
    match env.model with
    | ConstantTime -> ec_leaks (List.map (toec_expr env) (leaks_es env.pd es))
    | Normal | Annotations -> []

let ec_leaks_opn env es =  ec_leaks_es env es

let ec_leaks_if env e =
    match env.model with
    | ConstantTime ->
        ec_addleaks [
            Eapp (ec_ident "LeakAddr", [Elist (ece_leaks_e env e)]);
            Eapp (ec_ident "LeakCond", [toec_expr env e])
        ]
    | Normal | Annotations -> []

let ec_leaks_for env e1 e2 =
    match env.model with
    | ConstantTime ->
        let leaks = List.map (toec_expr env) (leaks_es env.pd [e1;e2]) in
        ec_addleaks [
            Eapp (ec_ident "LeakAddr", [Elist leaks]);
            Eapp (ec_ident "LeakFor", [Etuple [toec_expr env e1; toec_expr env e2]])
            ]
    | Normal | Annotations -> []

let ec_leaks_lv env lv =
    match env.model with
    | ConstantTime ->
        let leaks = leaks_lval env.pd lv in
        if leaks = [] then []
        else ec_leaks (List.map (toec_expr env) leaks)
    | Normal | Annotations -> []

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
    if lvs = [] || ((env.model = Normal || env.model = Annotations) && check_lvals lvs && ltys = otys) then
        [EScall (ec_lvals env lvs, f, args)]
    else
        ec_instr_aux env lvs otys otys (fun lvals -> EScall (lvals, f, args))

let ec_call env lvs etyso etysi e =
    let ltys = List.map ty_lval lvs in
    if lvs = [] || ((env.model = Normal || env.model = Annotations) && check_lvals lvs && ltys = etyso && etyso = etysi) then
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
        | Normal | Annotations ->
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
        if (env.model = Normal || env.model = Annotations) && List.length lvs = 1 then
            ec_assgn env (List.hd lvs) (List.hd otys, List.hd otys') (ec_e op')
        else
            (ec_leaks_opn env es) @
            (ec_call env lvs otys otys' (ec_e op))
    | Ccall (lvs, f, es) ->
      begin
        match env.model with
        | Annotations -> Annotations.toec_fun env lvs f es
        | _ ->
          let otys, itys = get_funtype env f in
          let args = List.map (ec_wcast env) (List.combine itys es) in

          (ec_leaks_es env es) @
          (ec_pcall env lvs otys [get_funname env f] args)
      end

    | Cassert (k,_,e) ->
      begin
        match env.model with
        | Annotations ->  Annotations.ec_trace env k e
        | _ -> []
      end

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

let var2ec_var env x = (List.hd [ec_vars env x], Base (toec_ty x.v_ty))

let add_ty env = function
    | Bty _ -> ()
    | Arr (_ws, n) -> add_Array env n

let extend_fun env f =
  let old = List.map V.clone f.f_args in
  let fn = f.f_name in

  let env,old_v =
    List.fold_left (fun (env,acc) v ->
        let s = String.uncapitalize_ascii v.v_name in
        let s = "old_" ^ s in
        let s,env = set_name env s in
        let env = set_var env v s in
        env, s :: acc
      ) (env,[]) old
  in
  let old_v = List.rev old_v in

  env.old := Mf.add fn old_v !(env.old);

  let old_v =
    List.fold_left2
      (fun acc v ty -> (v, Base (toec_ty ty)) :: acc)
      []
      old_v
      f.f_tyin
  in

  let mki i =
    {
      i_desc = i;
      i_loc = L.i_dummy;
      i_info = ();
      i_annot = [];
    }
  in
  let init = List.map2
      (fun o x ->
         let lvar = Lvar (L.mk_loc L._dummy o) in
         let e = Pvar (gkvar (L.mk_loc L._dummy x)) in
         let i = Prog.Cassgn (lvar, E.AT_keep, o.v_ty, e) in
         mki i
      ) old f.f_args
  in
  let clone x =
    let aux v = L.mk_loc L._dummy (V.clone v) in
    List.map aux f.f_args
  in
  let contra = match f.f_contra with
    | None ->
      {f_iparams = clone f.f_args;
       f_ires = clone (List.map L.unloc f.f_ret);
       f_pre = [];
       f_post = [];
      }
    | Some c -> c
  in
  let es = List.map (fun x -> Pvar (gkvar (L.mk_loc L._dummy x))) f.f_args in
  let iparam = List.map L.unloc contra.f_iparams in
  let assume = Annotations.sub_contra iparam es contra.f_pre in
  let es = List.map (fun x -> Pvar (gkvar (L.mk_loc L._dummy x))) old in
  let assert_ = Annotations.sub_contra iparam es contra.f_post in
  let es = List.map (fun x -> Pvar (gkvar x)) f.f_ret in
  let ires = List.map L.unloc contra.f_ires in
  let assert_ = Annotations.sub_contra ires es assert_ in
  let assume = List.map
      (fun (prover,exp) -> mki (Cassert (Assume , prover, exp)))
      assume
  in
  let assert_ = List.map
      (fun (prover,exp) -> mki (Cassert (Assert , prover, exp)))
      assert_
  in
  { f with f_body = assume @ f.f_body @ assert_}, env, old_v, init

let toec_fun asmOp env f =
    let f = { f with f_body = remove_for f.f_body } in

    let env =
      match env.model with
      | Annotations -> Annotations.sign env f
      | _ -> env
    in

    let locals = Sv.elements (locals f) in
    let f, env, old_v, init =
      if env.model = Annotations then extend_fun env f else f,env,[],[]
    in

    let env = List.fold_left add_var env (f.f_args @ locals) in
    (* init auxiliary variables *)
    let env = init_aux env.pd asmOp env f.f_body in
    List.iter (add_ty env) f.f_tyout;
    List.iter (fun x -> add_ty env x.v_ty) (f.f_args @ locals);
    Mty.iter (fun ty _ -> add_ty env ty) env.auxv;
    let ec_locals =
        let locs_ty (ty, vars) = List.map (fun v -> (v, Base (toec_ty ty))) vars in
        (List.flatten (List.map locs_ty (Mty.bindings env.auxv))) @
        (List.map (var2ec_var env) locals)
    in
    let aux_locals_init = locals
        |> List.filter (fun x -> match x.v_ty with Arr _ -> true | _ -> false)
        |> List.sort (fun x1 x2 -> compare x1.v_name x2.v_name)
        |> List.map (fun x -> ESasgn ([LvIdent [ec_vars env x]], ec_ident "witness"))
    in
    let env, ec_locals =
      match env.model with
      | Annotations ->
        let env, vars = Annotations.ec_vars env f in
        env, ec_locals @ old_v @ vars
      | _ -> env, ec_locals
    in

    let cl_vars_init =
      match env.model with
      | Annotations -> (Annotations.proof_var_init env f)
      | _ -> []
    in

    let ret =
      let ec_var x = ec_vari env (L.unloc x) in
      match f.f_ret with
      | [x] ->
        begin
          match env.model with
          | Annotations -> ESreturn (Etuple (ec_var x :: [Annotations.check_vars env f]))
          | _ -> ESreturn (ec_var x)
        end
      | xs ->
        begin
          match env.model with
          | Annotations ->
            ESreturn (Etuple (Etuple (List.map ec_var xs) :: [Annotations.check_vars env f ]))
          | _ -> ESreturn (Etuple (List.map ec_var xs))
        end
    in

    let ret_typ =
      match env.model with
      | Annotations ->
        let ret_typ = [Tuple(List.map (fun x -> Base (toec_ty x)) f.f_tyout)] in
        Tuple (ret_typ @ [Base "trace"])
      | _ -> Tuple(List.map (fun x -> Base (toec_ty x)) f.f_tyout)
    in

    {
        decl = {
            fname = (get_funname env f.f_name);
            args = List.map (var2ec_var env) f.f_args;
            rtys = ret_typ;
        };
        locals = ec_locals;
        stmt = (toec_cmd asmOp env init) @
               cl_vars_init @ aux_locals_init @
               (toec_cmd asmOp env f.f_body) @ [ret];
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
            args = [(a, Base arr_ty)];
            rtys = Base arr_ty;
        }
    in
    let randombytes_f n =
        let dmap =
            let wa = fmt_WArray n in
            let initf = Equant (Llambda, ["a"], Eapp (Eident [fmt_Array n; "init"], [
                Equant (Llambda, ["i"], Eapp (Eident [wa; "get8"], [ec_ident "a"; ec_ident "i"]))
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

let toec_prog pd asmOp model globs funcs arrsz warrsz randombytes =
    let add_glob_env env (x, d) = add_glob (add_glob_arrsz env (x, d)) x in
    let env = empty_env pd model funcs arrsz warrsz randombytes false
        |> fun env -> List.fold_left add_glob_env env globs
        |> fun env -> List.fold_left add_arrsz env funcs
    in

    let env, pp_leakages = match model with
      | ConstantTime -> env, [("leakages", Base"leakages_t")]
      | Normal -> env, []
      | Annotations ->
        let env, tmp =
          List.fold_left
          (fun (env,acc) a ->
             let env, vars = Annotations.ec_tmp_lvs env a in
             env, acc @ vars
          )
          (env,[])
          funcs
        in
        let name = "tmp__trace" in
        let s = normalize_name name in
        let s = create_name env s in
        let env =
          { env with
            alls = Ss.add s env.alls;
          }
        in
        env, (s, Base "trace") :: tmp
    in

    let funs = List.map (toec_fun asmOp env) funcs in

    let prefix = !Glob_options.ec_array_path in
    Sint.iter (pp_array_decl ~prefix) !(env.arrsz);
    Sint.iter (pp_warray_decl ~prefix) !(env.warrsz);

    let pp_arrays arr s = match Sint.elements s with
        | [] -> []
        | l -> [IrequireImport (List.map (Format.sprintf "%s%i" arr) l)]
    in

    let mod_arg =
        if Sint.is_empty !(env.randombytes) then []
        else [(syscall_mod_arg, syscall_mod_sig)]
    in

    let import_jleakage = match model with
      | Normal -> []
      | Annotations -> Annotations.import
      | ConstantTime -> [IfromRequireImport ("Jasmin", ["JLeakage"])]
    in

    let glob_imports = [
        IrequireImport ["AllCore"; "IntDiv"; "CoreMap"; "List"; "Distr"];
        IfromRequireImport ("Jasmin", [jmodel ()]);
        Iimport [lib_slh ()];
      ]
    in

    let top_mod = Imodule {
        name = "M";
        params = mod_arg;
        ty = None;
        vars = pp_leakages;
        funs;
      }
    in

    let proof =
      match env.model with
      | Annotations -> Annotations.proof env funcs
      | _ -> []
    in

    glob_imports @
    import_jleakage @
    (pp_arrays "Array" !(env.arrsz)) @
    (pp_arrays "WArray" !(env.warrsz)) @
    (List.map (fun glob -> ec_glob_decl env glob) globs) @
    (ec_randombytes env) @
    [top_mod] @
    proof


let pp_prog pd asmOp fmt model globs funcs arrsz warrsz randombytes =
    pp_ec_prog fmt (toec_prog pd asmOp model globs funcs arrsz warrsz randombytes);
    Format.fprintf fmt "@."

let rec used_func f =
  used_func_c Ss.empty f.f_body

and used_func_c used c =
  List.fold_left used_func_i used c

and used_func_i used i =
  match i.i_desc with
  | Cassgn _ | Copn _ | Csyscall _ | Cassert _ -> used
  | Cif (_,c1,c2)     -> used_func_c (used_func_c used c1) c2
  | Cfor(_,_,c)       -> used_func_c used c
  | Cwhile(_,c1,_,c2)   -> used_func_c (used_func_c used c1) c2
  | Ccall (_,f,_)   -> Ss.add f.fn_name used

let extract pd asmOp fmt model ((globs,funcs):('info, 'asm) prog) tokeep =

  let funcs = List.map Regalloc.fill_in_missing_names funcs in
  let tokeep = ref (Ss.of_list tokeep) in
  let dofun f =
    if Ss.mem f.f_name.fn_name !tokeep then
      (tokeep := Ss.union (used_func f) !tokeep; true)
    else false in
  let funcs = List.rev (List.filter dofun funcs) in
  let arrsz = ref Sint.empty in
  let warrsz = ref Sint.empty in
  let randombytes = ref Sint.empty in
  pp_prog pd asmOp fmt model globs funcs arrsz warrsz randombytes
