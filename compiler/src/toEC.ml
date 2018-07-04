open Utils
open Type
open Prog
module E = Expr
module B = Bigint

let pp_size fmt sz =
  Format.fprintf fmt "%i" (int_of_ws sz)

let pp_Tsz fmt sz = 
  Format.fprintf fmt "W%a" pp_size sz

module Scmp = struct
  type t = string
  let compare = compare
end

module Ss = Set.Make(Scmp)
module Ms = Map.Make(Scmp)

type env = {
    leaks : bool;
    alls : Ss.t;
    vars : string Mv.t;
    rmem : Sf.t;
    wmem : Sf.t;
    glob : (string * Type.stype) Ms.t
  }
(* --------------------------------------------------------------- *)

let rec read_mem_e = function
  | Pconst _ | Pbool _ | Parr_init _ |Pvar _ | Pglobal _ -> false
  | Pload _ -> true
  | Pcast (_, e) | Papp1 (_, e) | Pget (_, e) -> read_mem_e e  
  | Papp2 (_, e1, e2) -> read_mem_e e1 || read_mem_e e2
  | Pif  (e1, e2, e3) -> read_mem_e e1 || read_mem_e e2 || read_mem_e e3

let read_mem_es = List.exists read_mem_e

let read_mem_lval = function
  | Lnone _ | Lvar _ -> false
  | Lmem (_,_,_) -> true 
  | Laset (_, e) -> read_mem_e e

let write_mem_lval = function
  | Lnone _ | Lvar _ | Laset _ -> false
  | Lmem _ -> true

let read_mem_lvals = List.exists read_mem_lval
let write_mem_lvals = List.exists write_mem_lval

let rec read_mem_i s i =
  match i.i_desc with
  | Cassgn (x, _, _, e) -> read_mem_lval x || read_mem_e e
  | Copn (xs, _, _, es) -> read_mem_lvals xs || read_mem_es es
  | Cif (e, c1, c2)     -> read_mem_e e || read_mem_c s c1 || read_mem_c s c2
  | Cwhile (c1, e, c2)  -> read_mem_c s c1 || read_mem_e e || read_mem_c s c2
  | Ccall (_, xs, fn, es) -> read_mem_lvals xs || Sf.mem fn s || read_mem_es es
  | Cfor (_, (_, e1, e2), c) -> read_mem_e e1 || read_mem_e e2 || read_mem_c s c

and read_mem_c s = List.exists (read_mem_i s)

let read_mem_f s f = read_mem_c s f.f_body

let rec write_mem_i s i =
  match i.i_desc with
  | Cassgn (x, _, _, _)  -> write_mem_lval x 
  | Copn (xs, _, _, _)   -> write_mem_lvals xs 
  | Cif (_, c1, c2)      -> write_mem_c s c1 ||write_mem_c s c2
  | Cwhile (c1, _, c2)   -> write_mem_c s c1 ||write_mem_c s c2
  | Ccall (_, xs, fn, _) -> write_mem_lvals xs || Sf.mem fn s 
  | Cfor (_, _, c)       -> write_mem_c s c 

and write_mem_c s = List.exists (write_mem_i s)

let write_mem_f s f = write_mem_c s f.f_body

let init_use fs = 
  let add t s f = if t s f then Sf.add f.f_name s else s in
  List.fold_left 
    (fun (sr,sw) f -> add read_mem_f sr f, add write_mem_f sw f)
    (Sf.empty, Sf.empty) fs

(* ------------------------------------------------------------------- *)
let add64 x e = 
  (Type.Coq_sword Type.U64, Papp2 (E.Oadd ( E.Op_w Type.U64), Pvar x, e))

type leakage = 
  | LK_MemAccess of expr list
  | LK_Branch of expr
  | LK_For of expr * expr
  | LK_unit of expr * expr

let rec leaks_e_rec leaks e = 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ |Pvar _ | Pglobal _ -> leaks
  | Pload (_,x,e) -> snd (add64 x e) :: leaks_e_rec leaks e
  | Pcast (_, e) | Papp1 (_, e) | Pget (_, e) -> leaks_e_rec leaks e
  | Papp2 (_, e1, e2) -> leaks_e_rec (leaks_e_rec leaks e1) e2
  | Pif  (e1, e2, e3) -> leaks_e_rec (leaks_e_rec (leaks_e_rec leaks e1) e2) e3

let leaks_e e = leaks_e_rec [] e
let leaks_es es = List.fold_left leaks_e_rec [] es

let leaks_lval leaks = function
  | Lnone _ | Lvar _ -> leaks
  | Laset (_, e) -> leaks_e_rec leaks e
  | Lmem (_, x,e) -> snd (add64 x e) :: leaks_e_rec leaks e

(* FIXME: generate this list automatically *)
let ec_keyword = 
 [ "exact"
 ; "assumption"
 ; "smt"
 ; "by"
 ; "reflexivity"
 ; "done"
 ; "admit"
 ; "axiom"
 ; "axiomatized"
 ; "lemma"
 ; "realize"
 ; "choice"
 ; "proof"
 ; "qed"
 ; "goal"
 ; "end"
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
 ; "require"
 ; "theory"
 ; "abstract"
 ; "section"
 ; "type"
 ; "class"
 ; "instance"
 ; "print"
 ; "search"
 ; "as"
 ; "Pr"
 ; "clone"
 ; "with"
 ; "rename"
 ; "prover"
 ; "timeout"
 ; "why3"
 ; "dump"
 ; "Top"
 ; "Self"
 ; "time"
 ; "undo"
 ; "debug"
 ; "pragma"
 ; "forall"
 ; "exists"
 ; "fun"
 ; "glob"
 ; "let"
 ; "in"
 ; "var"
 ; "proc"
 ; "if"
 ; "then"
 ; "else"
 ; "elif"
 ; "while"
 ; "assert"
 ; "return"
 ; "res"
 ; "equiv"
 ; "hoare"
 ; "phoare"
 ; "islossless"
 ; "beta"
 ; "iota"
 ; "zeta"
 ; "logic"
 ; "delta"
 ; "simplify"
 ; "congr"
 ; "change"
 ; "split"
 ; "left"
 ; "right"
 ; "generalize"
 ; "case"
 ; "intros"
 ; "pose"
 ; "cut"
 ; "have"
 ; "elim"
 ; "clear"
 ; "apply"
 ; "rewrite"
 ; "rwnormal"
 ; "subst"
 ; "progress"
 ; "trivial"
 ; "auto"
 ; "idtac"
 ; "move"
 ; "modpath"
 ; "field"
 ; "fieldeq"
 ; "ring"
 ; "ringeq"
 ; "algebra"
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
 ; "pr_bounded"
 ; "bypr"
 ; "byphoare"
 ; "byequiv"
 ; "fel"
 ; "conseq"
 ; "exfalso"
 ; "inline"
 ; "alias"
 ; "fission"
 ; "fusion"
 ; "unroll"
 ; "splitwhile"
 ; "kill"
 ; "eager"
 ; "try"
 ; "first"
 ; "last"
 ; "do"
 ; "strict"
 ; "expect" ]


let empty_env leaks = {
    leaks;
    alls = Ss.of_list ec_keyword;
    vars = Mv.empty;
    rmem = Sf.empty;
    wmem = Sf.empty;
    glob = Ms.empty;
  }

let create_name env s = 
  if not (Ss.mem s env.alls) then s
  else
    let rec aux i = 
      let s = Format.sprintf "%s_%i" s i in
      if Ss.mem s env.alls then aux (i+1)
      else s in
    aux 0
 
let add_var env x = 
  let s = create_name env x.v_name in
  { env with 
    alls = Ss.add s env.alls;
    vars = Mv.add x s env.vars }

let add_glob env x ws = 
  let s = create_name env x in
  let ty = Bty (U ws) in
  { env with
    alls = Ss.add s env.alls;
    glob = Ms.add x (s,Conv.cty_of_ty ty) env.glob }

let pp_var env fmt (x:var) = 
  Format.fprintf fmt "%s" (Mv.find x env.vars)

let pp_glob env fmt x = 
  Format.fprintf fmt "%s" (fst (Ms.find x env.glob))

let ty_glob env x = snd (Ms.find x env.glob)

let pp_op1 fmt = function
  | E.Osignext(sz1,sz2) -> 
    Format.fprintf fmt "sigext_%a_%a" pp_size sz2 pp_size sz1
  | E.Ozeroext(sz1,sz2) -> 
    Format.fprintf fmt "zeroext_%a_%a" pp_size sz2 pp_size sz1
  | E.Onot     -> Format.fprintf fmt "!"
  | E.Olnot _  -> Format.fprintf fmt "!"
  | E.Oneg _   -> Format.fprintf fmt "-"

let swap_op2 op e1 e2 = 
  match op with 
  | E.Ogt   _ -> e2, e1
  | E.Oge   _ -> e2, e1 
  | _         -> e1, e2

let pp_signed fmt = function 
  | E.Cmp_w (Signed, _) -> Format.fprintf fmt "s"
  | _                 -> ()

let pp_op2 fmt = function
  | E.Oand -> Format.fprintf fmt "/\\"
  | E.Oor ->  Format.fprintf fmt "\\/"
  | E.Oadd _ -> Format.fprintf fmt "+"
  | E.Omul _ -> Format.fprintf fmt "*"
  | E.Odiv s -> Format.fprintf fmt "`/%a`" pp_signed s
  | E.Omod s -> Format.fprintf fmt "%%%%%a" pp_signed s 
  | E.Osub  _ -> Format.fprintf fmt "-"

  | E.Oland _ -> Format.fprintf fmt "`&`"
  | E.Olor  _ -> Format.fprintf fmt "`|`"
  | E.Olxor _ -> Format.fprintf fmt "`^`"
  | E.Olsr  _ -> Format.fprintf fmt "`>>`"
  | E.Olsl  _ -> Format.fprintf fmt "`<<`"
  | E.Oasr  _ -> Format.fprintf fmt "`|>>`"

  | E.Oeq   _ -> Format.fprintf fmt "="
  | E.Oneq  _ -> Format.fprintf fmt "<>"
  | E.Olt s| E.Ogt s -> Format.fprintf fmt "`<%a`" pp_signed s
  | E.Ole s | E.Oge s -> Format.fprintf fmt "`<=%a`" pp_signed s

let in_ty_op1 op =
  fst (E.type_of_op1 op)

let in_ty_op2 op =
  fst (E.type_of_op2 op)

let out_ty_op1 op =
  snd (E.type_of_op1 op)

let out_ty_op2 op =
  snd (E.type_of_op2 op)

let min_ty ty1 ty2 = 
  match ty1, ty2 with
  | Coq_sword sz1, Coq_sword sz2 -> 
    Coq_sword (Utils0.cmp_min Type.wsize_cmp sz1 sz2)
  | Coq_sint, Coq_sint -> Coq_sint
  | Coq_sbool, Coq_sbool -> Coq_sbool
  | Coq_sarr(sz1,p1), Coq_sarr(sz2,p2) -> 
    assert (sz1 = sz2 && p1 = p2); ty1
  | _, _ -> assert false

let ty_get x = 
  match Conv.cty_of_ty x.L.pl_desc.v_ty with
  | Coq_sarr(sz,_) -> Coq_sword sz
  | _              -> assert false

let rec ty_expr = function
  | Pconst _ -> Coq_sint
  | Pbool _ -> Coq_sbool
  | Parr_init (sz, n) -> Coq_sarr (sz, Conv.pos_of_bi n)
  | Pcast (sz,_) -> Coq_sword sz
  | Pvar x -> Conv.cty_of_ty x.L.pl_desc.v_ty
  | Pglobal (sz,_) -> Coq_sword sz
  | Pload (sz,_,_) -> Coq_sword sz
  | Pget(x,_) -> ty_get x
  | Papp1 (op,_) -> out_ty_op1 op
  | Papp2 (op,_,_) -> out_ty_op2 op
  | Pif (_,e1,e2) -> min_ty (ty_expr e1) (ty_expr e2)

let wsize = function
  | Coq_sword sz -> sz
  | _ -> assert false

let pp_cast pp fmt (ty,ety,e) = 
  if ety = ty then pp fmt e 
  else 
    Format.fprintf fmt "(zeroext_%a_%a %a)" 
      pp_size (wsize ety) pp_size (wsize ty) pp e

 
let rec pp_expr env fmt (e:expr) = 
  match e with
  | Pconst z -> Format.fprintf fmt "%a" B.pp_print z
  | Pbool b -> Format.fprintf fmt "%a" Printer.pp_bool b
  | Parr_init (sz, n) -> 
    Format.fprintf fmt "(array_init_%a %a)" pp_size sz B.pp_print n
  | Pcast(sz,e) -> 
    Format.fprintf fmt "(%a.of_uint %a)" pp_Tsz sz (pp_expr env) e
  | Pvar x -> pp_var env fmt (L.unloc x)
  | Pglobal(sz, x) -> 
    pp_cast (pp_glob env) fmt (Coq_sword sz, ty_glob env x, x)
  | Pget(x,e) -> 
    Format.fprintf fmt "%a.[%a]" (pp_var env) (L.unloc x) (pp_expr env) e 
  | Pload (sz, x, e) -> 
    Format.fprintf fmt "(load%a global_mem %a)"
      pp_Tsz sz (pp_wcast env) (add64 x e)
  | Papp1 (op1, e) -> 
    Format.fprintf fmt "(%a %a)" pp_op1 op1 (pp_wcast env) (in_ty_op1 op1, e)
  | Papp2 (op2, e1, e2) ->  
    let ty1,ty2 = in_ty_op2 op2 in
    let te1, te2 = swap_op2 op2 (ty1, e1) (ty2, e2) in
    Format.fprintf fmt "(%a %a %a)"
      (pp_wcast env) te1 pp_op2 op2 (pp_wcast env) te2
  | Pif(e1,et,ef) -> 
    let ty = ty_expr e in
    Format.fprintf fmt "(%a ? %a : %a)"
      (pp_expr env) e1 (pp_wcast env) (ty,et) (pp_wcast env) (ty,ef)

and pp_wcast env fmt (ty, e) = 
  pp_cast (pp_expr env) fmt (ty, ty_expr e, e)

let pp_coq_ty fmt ty = 
  match Conv.cty_of_ty ty with 
  | Coq_sbool -> Format.fprintf fmt "bool"
  | Coq_sint  -> Format.fprintf fmt "int"
  | Coq_sarr(sz,_) -> Format.fprintf fmt "(int,%a.t)map" pp_Tsz sz
  | Coq_sword sz   -> Format.fprintf fmt "%a.t" pp_Tsz sz

let pp_vdecl env fmt x = 
  Format.fprintf fmt "%a:%a" 
    (pp_var env) x 
    pp_coq_ty x.v_ty
  
let pp_params env fmt params = 
  Format.fprintf fmt "@[%a@]"
    (pp_list ",@ " (pp_vdecl env)) params 

let pp_locals env fmt locals = 
  let locarr = 
    List.filter (fun x -> match x.v_ty with Arr _ -> true | _ -> false) 
      locals in
  let locarr = 
    List.sort (fun x1 x2 -> compare x1.v_name x2.v_name) locarr in

  let pp_loc fmt x = Format.fprintf fmt "var %a;" (pp_vdecl env) x in
  let pp_init fmt x = 
    let (sz,n) = match x.v_ty with Arr (sz,n) -> sz,n | _ -> assert false in
    Format.fprintf fmt "%a <- %a;" (pp_var env) x (pp_expr env) (Parr_init(sz,B.of_int n)) in
  Format.fprintf fmt "%a@ %a" 
  (pp_list "@ " pp_loc) locals
  (pp_list "@ " pp_init) locarr 

let pp_rty b fmt tys =
  if b then
    Format.fprintf fmt "@[global_mem_t%s%a@]"
       (if tys = [] then "" else " * ")
       (pp_list "*@ " pp_coq_ty) tys 
  else  
    if tys = [] then
       Format.fprintf fmt "unit"
    else
      Format.fprintf fmt "@[%a@]" 
        (pp_list " *@ " pp_coq_ty) tys 

let pp_ret b env fmt xs = 
  if b then
    if xs = [] then Format.fprintf fmt "return global_mem;"
    else 
      Format.fprintf fmt "@[return (global_mem, %a);@]"
        (pp_list ",@ " (fun fmt x -> pp_var env fmt (L.unloc x))) xs
  else 
  Format.fprintf fmt "@[return (%a);@]"
    (pp_list ",@ " (fun fmt x -> pp_var env fmt (L.unloc x))) xs

let pp_opn fmt op = 
  let s = Printer.pp_opn op in
  let s = String.sub s 1 (String.length s - 1) in
  Format.fprintf fmt "%s" s

let pp_lval env fmt = function
  | Lnone _ -> assert false 
  | Lvar x -> pp_var env fmt (L.unloc x)
  | Lmem _  -> assert false
  | Laset (x,e) -> 
    Format.fprintf fmt "%a.[%a]" (pp_var env) (L.unloc x) (pp_expr env) e

let pp_lvals env fmt xs = 
  match xs with
  | []  -> assert false
  | [x] -> pp_lval env fmt x 
  | _   -> Format.fprintf fmt "(%a)" (pp_list ",@ " (pp_lval env)) xs

let pp_leaks_assgn env fmt lv e =
  if env.leaks then
    let leaks = leaks_lval (leaks_e e) lv in
    Format.fprintf fmt "leakages <- LeakExpr(@[[%a]@]) :: leakages;@ "
      (pp_list ";@ " (pp_expr env)) leaks

let pp_leaks_es env fmt es = 
  if env.leaks then
    let leaks = leaks_es es in
    Format.fprintf fmt "leakages <- LeakExpr(@[[%a]@]) :: leakages;@ "
      (pp_list ";@ " (pp_expr env)) leaks
    
let pp_leaks_if env fmt e = 
  if env.leaks then
    let leaks = leaks_e e in
    Format.fprintf fmt 
      "leakages <- LeakCond(%a) :: LeakExpr(@[[%a]@]) :: leakages;@ "
      (pp_expr env) e
      (pp_list ";@ " (pp_expr env)) leaks

let pp_leaks_for env fmt e1 e2 = 
  if env.leaks then
    let leaks = leaks_es [e1;e2] in
    Format.fprintf fmt 
      "leakages <- LeakFor(%a,%a) :: LeakExpr(@[[%a]@]) :: leakages;@ "
      (pp_expr env) e1 (pp_expr env) e2 
      (pp_list ";@ " (pp_expr env)) leaks

let check_lval = function
  | Lvar _ -> true 
  | Lnone _ | Lmem _ | Laset _ -> false 
  
let check_lvals = List.for_all check_lval

let rec pp_cmd env fmt c = 
  Format.fprintf fmt "@[<v>%a@]"
   (pp_list "@ " (pp_instr env)) c

and pp_instr env fmt i = 
  match i.i_desc with 
  | Cassgn (lv, _, ty, e) ->
    pp_leaks_assgn env fmt lv e;
    begin match lv with
    | Lmem(ws, x, e1) ->
      Format.fprintf fmt "@[global_mem <- store%a global_mem %a %a;@]"
         pp_Tsz ws (pp_wcast env) (add64 x e1) (pp_wcast env) (Type.Coq_sword ws, e)
    | _ -> 
      Format.fprintf fmt "@[%a <- %a;@]" (pp_lval env) lv 
        (pp_wcast env) (Conv.cty_of_ty ty, e)
    end
  | Copn(lvs, _, op, es) ->
    assert (check_lvals lvs);
    pp_leaks_es env fmt es; 
    Format.fprintf fmt "@[%a <- %a %a;@]"
      (pp_lvals env) lvs pp_opn op 
      (pp_list "@ " (pp_expr env)) es
  | Ccall(_, lvs, f, es) ->
    assert (check_lvals lvs);
    pp_leaks_es env fmt es; 
    let pp_vars fmt lvs = 
      if Sf.mem f env.wmem then
        if lvs = [] then
          Format.fprintf fmt "global_mem"
        else 
          Format.fprintf fmt "(global_mem, %a)" 
            (pp_list ",@ " (pp_lval env)) lvs 
      else pp_lvals env fmt lvs in
    let pp_args fmt es = 
      if Sf.mem f env.rmem then
        if es = [] then
          Format.fprintf fmt "global_mem"
        else 
          Format.fprintf fmt "global_mem, %a" (pp_list ",@ " (pp_expr env)) es 
      else pp_list ",@ " (pp_expr env) fmt es in
    
    Format.fprintf fmt "@[%a <%@ %s (%a);@]"
        pp_vars lvs f.fn_name pp_args es

  | Cif(e,c1,c2) ->
    pp_leaks_if env fmt e;
    Format.fprintf fmt "@[<v>if (%a) {@   %a@ } else {@   %a@ }@]"
      (pp_expr env) e (pp_cmd env) c1 (pp_cmd env) c2
  | Cwhile(c1, e,c2) ->
    let pp_leak fmt e = 
      if env.leaks then Format.fprintf fmt "@ %a" (pp_leaks_if env) e in
    Format.fprintf fmt "@[<v>%a%a@ while (%a) {@   %a%a@ }@]"
      (pp_cmd env) c1 pp_leak e (pp_expr env) e 
      (pp_cmd env) (c2@c1) pp_leak e

  | Cfor(i, (d,e1,e2), c) ->
    pp_leaks_for env fmt e1 e2;
    let i1, i2 = 
      if d = UpTo then Pvar i, e2
      else e2, Pvar i in
    Format.fprintf fmt 
      "@[<v>%a <- %a;@ while (%a < %a) {@   @[<v>%a@ %a <- %a %s 1;@]@ }@]"
      (pp_var env) (L.unloc i) (pp_expr env) e1 
      (pp_expr env) i1 (pp_expr env) i2
      (pp_cmd env) c
      (pp_var env) (L.unloc i) (pp_var env) (L.unloc i) 
      (if d = UpTo then "+" else "-")


let pp_fun env fmt f = 
  let locals = Sv.elements (locals f) in
  (* initialize the env *)
  let env = List.fold_left add_var env f.f_args in
  let env = List.fold_left add_var env locals in  
  (* Print the function *)
  let pp_args fmt a =
    if Sf.mem f.f_name env.rmem then
      if a = [] then
        Format.fprintf fmt "global_mem : global_mem_t"
      else
        Format.fprintf fmt "global_mem : global_mem_t, %a"
          (pp_params env) a
    else (pp_params env) fmt a
  in

  let b = Sf.mem f.f_name env.wmem in
  Format.fprintf fmt 
    "@[<v>proc %s (%a) : %a = {@   @[<v>%a@ %a@ %a@]@ }@]"
    f.f_name.fn_name 
    pp_args f.f_args 
    (pp_rty b) f.f_tyout
    (pp_locals env) locals
    (pp_cmd env) f.f_body
    (pp_ret b env) f.f_ret

let pp_glob_decl env fmt (ws,x, z) =
  Format.fprintf fmt "@[abbrev %a = %a.of_uint %a.@]@ "
    (pp_glob env) x pp_Tsz ws B.pp_print z

let pp_prog fmt leaks globs funcs = 
  let rmem, wmem = init_use funcs in
  let env = 
    List.fold_left (fun env (ws, x, _) -> add_glob env x ws)
      (empty_env leaks) globs in
  let env = {env with rmem; wmem} in
  let pp_leakages fmt env = 
    if env.leaks then
      Format.fprintf fmt "var leakages : leakages_t@ @ " in

  Format.fprintf fmt "@[<v>require import List Jasmin_model Int IntDiv CoreMap.@ @ %a@ @ module M = {@   @[<v>%a%a@]@ }.@ @]@." 
    (pp_list "@ @ " (pp_glob_decl env)) globs 
    pp_leakages env 
    (pp_list "@ @ " (pp_fun env)) funcs 
    

let rec used_func f = 
  used_func_c Ss.empty f.f_body 

and used_func_c used c = 
  List.fold_left used_func_i used c

and used_func_i used i = 
  match i.i_desc with
  | Cassgn _ | Copn _ -> used
  | Cif (_,c1,c2)     -> used_func_c (used_func_c used c1) c2
  | Cfor(_,_,c)       -> used_func_c used c
  | Cwhile(c1,_,c2)   -> used_func_c (used_func_c used c1) c2
  | Ccall (_,_,f,_)   -> Ss.add f.fn_name used

let extract fmt ~withleakage ((globs,funcs):'a prog) tokeep = 
  let funcs = List.map Regalloc.fill_in_missing_names funcs in
  let tokeep = ref (Ss.of_list tokeep) in
  let dofun f = 
    if Ss.mem f.f_name.fn_name !tokeep then
      (tokeep := Ss.union (used_func f) !tokeep; true)
    else false in
  let funcs = List.filter dofun funcs in
  pp_prog fmt withleakage globs (List.rev funcs)




