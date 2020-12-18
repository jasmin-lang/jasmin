open Utils
open Wsize
open Type
open Prog
module E = Expr
module B = Bigint

let pp_size fmt sz =
  Format.fprintf fmt "%i" (int_of_ws sz)

let pp_Tsz fmt sz = 
  Format.fprintf fmt "W%a" pp_size sz

let pp_sz_t fmt sz = 
  Format.fprintf fmt "%a.t" pp_Tsz sz 

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
    model : model;
    alls : Ss.t;
    vars : (string * bool) Mv.t;  (* true means option type *)
    glob : (string * ty) Ms.t;
    funs : (string * (ty list * ty list)) Mf.t;  
    arrsz  : Sint.t;
    warrsz : Sint.t;
    auxv  : string list Mty.t;
  }

let for_constTime env = env.model = Utils.ConstantTime
let for_safety    env = env.model = Utils.Safety

(* --------------------------------------------------------------- *)

let rec read_mem_e = function
  | Pconst _ | Pbool _ | Parr_init _ |Pvar _ | Pglobal _ -> false
  | Pload _ -> true
  | Papp1 (_, e) | Pget (_, _, e) -> read_mem_e e
  | Papp2 (_, e1, e2) -> read_mem_e e1 || read_mem_e e2
  | PappN (_, es) -> read_mem_es es
  | Pif  (_, e1, e2, e3) -> read_mem_e e1 || read_mem_e e2 || read_mem_e e3

and read_mem_es es = List.exists read_mem_e es

let read_mem_lval = function
  | Lnone _ | Lvar _ -> false
  | Lmem (_,_,_) -> true 
  | Laset (_,_,e) -> read_mem_e e

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
  | Cwhile (_, c1, e, c2)  -> read_mem_c s c1 || read_mem_e e || read_mem_c s c2
  | Ccall (_, xs, fn, es) -> read_mem_lvals xs || Sf.mem fn s || read_mem_es es
  | Cfor (_, (_, e1, e2), c) -> read_mem_e e1 || read_mem_e e2 || read_mem_c s c

and read_mem_c s = List.exists (read_mem_i s)

let read_mem_f s f = read_mem_c s f.f_body

let rec write_mem_i s i =
  match i.i_desc with
  | Cassgn (x, _, _, _)  -> write_mem_lval x 
  | Copn (xs, _, _, _)   -> write_mem_lvals xs 
  | Cif (_, c1, c2)      -> write_mem_c s c1 ||write_mem_c s c2
  | Cwhile (_, c1, _, c2)   -> write_mem_c s c1 ||write_mem_c s c2
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
  (u64, Papp2 (E.Oadd ( E.Op_w U64), Pvar x, e))

let int_of_word ws e = 
  Papp1 (E.Oint_of_word ws, e)

let rec leaks_e_rec leaks e =
  match e with
  | Pconst _ | Pbool _ | Parr_init _ |Pvar _ | Pglobal _ -> leaks
  | Pload (_,x,e) -> leaks_e_rec (int_of_word U64 (snd (add64 x e)) :: leaks) e
  | Pget (_,_, e) -> leaks_e_rec (e::leaks) e 
  | Papp1 (_, e) -> leaks_e_rec leaks e
  | Papp2 (_, e1, e2) -> leaks_e_rec (leaks_e_rec leaks e1) e2
  | PappN (_, es) -> leaks_es_rec leaks es
  | Pif  (_, e1, e2, e3) -> leaks_e_rec (leaks_e_rec (leaks_e_rec leaks e1) e2) e3
and leaks_es_rec leaks es = List.fold_left leaks_e_rec leaks es

let leaks_e e = leaks_e_rec [] e
let leaks_es es = leaks_es_rec [] es

let leaks_lval = function
  | Lnone _ | Lvar _ -> []
  | Laset (_,_, e) -> leaks_e_rec [e] e
  | Lmem (_, x,e) -> leaks_e_rec [int_of_word U64 (snd (add64 x e))] e

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
 ; "expect"
 ; "interleave" ]

let internal_keyword = 
  [ "safe"; "leakages"]

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
 
let mkfunname env fn = 
  let s = fn.fn_name in
  let s = 
    let c0 = s.[0] in
    let l0 = Char.lowercase_ascii c0 in
    if c0 = l0 then s
    else 
      String.init (String.length s) (fun i -> if i = 0 then l0 else s.[i]) 
  in
  create_name env s

let empty_env model fds = 

  let env = { 
    model;
    alls = keywords;
    vars = Mv.empty;
    glob = Ms.empty;
    funs = Mf.empty;
    arrsz = Sint.empty;
    warrsz = Sint.empty;
    auxv  = Mty.empty ;
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
let pp_fname env fmt f = Format.fprintf fmt "%s" (get_funname env f)

let ty_lval = function
  | Lnone (_, ty) -> ty
  | Lvar x -> (L.unloc x).v_ty
  | Lmem (ws,_,_) -> Bty (U ws)
  | Laset(ws, _, _) -> Bty (U ws)

let pp_ty _option fmt ty = 
  match ty with
  | Bty Bool -> Format.fprintf fmt "bool"
  | Bty Int  -> Format.fprintf fmt "int"
  | Bty (U ws) -> pp_sz_t fmt ws
  | Arr(ws,n) -> Format.fprintf fmt "%a Array%i.t" pp_sz_t ws n

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

let set_var env x option s = 
  { env with 
    alls = Ss.add s env.alls;
    vars = Mv.add x (s,option) env.vars }

let add_var option env x = 
  let s = create_name env x.v_name in
  set_var env x option s

let add_glob env x ws = 
  let s = create_name env x in
  let ty = Bty (U ws) in
  { env with
    alls = Ss.add s env.alls;
    glob = Ms.add x (s, ty) env.glob }

let pp_oget option pp = 
  pp_maybe option (pp_enclose ~pre:"(oget " ~post:")") pp

let pp_var env fmt (x:var) = 
  pp_string fmt (fst (Mv.find x env.vars))

let is_option env (x:var) = 
  snd (Mv.find x env.vars)

let pp_ovar env fmt (x:var) = 
  let (s,option) = Mv.find x env.vars in
  if option then
    let ty = x.v_ty in
    if is_ty_arr ty then
      let (_ws,n) = array_kind ty in
      Format.fprintf fmt "(Array%i.map oget %s)" n s
    else pp_oget true pp_string fmt s
  else pp_string fmt s

let pp_glob env fmt x = 
  Format.fprintf fmt "%s" (fst (Ms.find x env.glob))

let ty_glob env x = snd (Ms.find x env.glob)

let pp_zeroext fmt (szi, szo) = 
  let io, ii = int_of_ws szo, int_of_ws szi in
  if ii < io then Format.fprintf fmt "zeroextu%a" pp_size szo
  else if ii = io then ()
  else (* io < ii *) Format.fprintf fmt "truncateu%a" pp_size szo
  
let pp_op1 fmt = function
  | E.Oword_of_int sz ->
    Format.fprintf fmt "%a.of_int" pp_Tsz sz
  | E.Oint_of_word sz ->
    Format.fprintf fmt "%a.to_uint" pp_Tsz sz
  | E.Osignext(szo,_szi) -> 
    Format.fprintf fmt "sigextu%a" pp_size szo
  | E.Ozeroext(szo,szi) -> 
    pp_zeroext fmt (szi, szo) 
  | E.Onot     -> Format.fprintf fmt "!"
  | E.Olnot _  -> Format.fprintf fmt "invw"
  | E.Oneg _   -> Format.fprintf fmt "-"

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

let rec ty_expr = function
  | Pconst _       -> tint 
  | Pbool _        -> tbool
  | Parr_init _    -> assert false 
  | Pvar x         -> x.L.pl_desc.v_ty
  | Pglobal (sz,_) -> tu sz
  | Pload (sz,_,_) -> tu sz
  | Pget  (sz,_,_) -> tu sz
  | Papp1 (op,_)   -> out_ty_op1 op
  | Papp2 (op,_,_) -> out_ty_op2 op
  | PappN (op, _)  -> out_ty_opN op
  | Pif (ty,_,_,_) -> ty

let wsize = function
  | Coq_sword sz -> sz
  | _ -> assert false

let pp_cast pp fmt (ty,ety,e) = 
  if ety = ty then pp fmt e 
  else 
    Format.fprintf fmt "(%a %a)" pp_zeroext (ws_of_ty ety, ws_of_ty ty) pp e 

let check_array env x = 
  match (L.unloc x).v_ty with
  | Arr(ws, n) -> Sint.mem n env.arrsz && Sint.mem (arr_size ws n) env.warrsz
  | _ -> true
  
let oarray option = if option then "OArray" else "Array"

let pp_oarray env = oarray (for_safety env)

let pp_initi env fmt (x, n, ws) =
  Format.fprintf fmt 
    "@[(WArray%i.init%i (fun i => %a.[i]))@]"
    (arr_size ws n) (int_of_ws ws) (pp_var env) x
    
let pp_print_i fmt z = 
  if B.le B.zero z then B.pp_print fmt z 
  else Format.fprintf fmt "(%a)" B.pp_print z 

let rec pp_expr env fmt (e:expr) = 
  match e with
  | Pconst z -> Format.fprintf fmt "%a" pp_print_i z

  | Pbool b -> Format.fprintf fmt "%a" Printer.pp_bool b

  | Parr_init _n -> 
    assert false
(*    let pp_init fmt sz = 
      if for_safety env then Format.fprintf fmt "None"
      else Format.fprintf fmt "%a.zero" pp_Tsz sz in
    Format.fprintf fmt "%s%a.create %a"
      (pp_oarray env) B.pp_print n pp_init U8 *)

  | Pvar x ->
    pp_ovar env fmt (L.unloc x)

  | Pglobal(sz, x) -> 
    pp_cast (pp_glob env) fmt (tu sz, ty_glob env x, x)

  | Pget(ws, x, e) -> 
    assert (check_array env x);
    let pp fmt (x,e) = 
      let x = L.unloc x in
      let (xws,n) = array_kind x.v_ty in
      if ws = xws then
        Format.fprintf fmt "@[%a.[%a]@]" (pp_var env) x (pp_expr env) e
      else
        Format.fprintf fmt "@[(get%i@ %a@ %a)@]" 
          (int_of_ws ws) (pp_initi env) (x, n, xws) (pp_expr env) e in
    let option = 
      for_safety env &&  snd (Mv.find (L.unloc x) env.vars) in
    pp_oget option pp fmt (x,e)

  | Pload (sz, x, e) -> 
    Format.fprintf fmt "(loadW%a Glob.mem (W64.to_uint %a))" 
      pp_size sz (pp_wcast env) (add64 x e)

  | Papp1 (op1, e) -> 
    Format.fprintf fmt "(%a %a)" pp_op1 op1 (pp_wcast env) (in_ty_op1 op1, e)

  | Papp2 (op2, e1, e2) ->  
    let ty1,ty2 = in_ty_op2 op2 in
    let te1, te2 = swap_op2 op2 (ty1, e1) (ty2, e2) in
    Format.fprintf fmt "(%a %a %a)"
      (pp_wcast env) te1 pp_op2 op2 (pp_wcast env) te2

  | PappN (op, es) ->
    (* FIXME *)
    begin match op with
    | Opack (ws, we) ->
      let i = int_of_pe we in
      let rec aux fmt es = 
        match es with
        | [] -> assert false
        | [e] -> Format.fprintf fmt "%a" (pp_expr env) e
        | e::es -> 
          Format.fprintf fmt "@[(%a %%%% 2^%i +@ 2^%i * %a)@]"
            (pp_expr env) e i i aux es in
      Format.fprintf fmt "(W%a.of_int %a)" pp_size ws aux (List.rev es)
    end

  | Pif(_,e1,et,ef) -> 
    let ty = ty_expr e in
    Format.fprintf fmt "(%a ? %a : %a)"
      (pp_expr env) e1 (pp_wcast env) (ty,et) (pp_wcast env) (ty,ef)

and pp_wcast env fmt (ty, e) = 
  pp_cast (pp_expr env) fmt (ty, ty_expr e, e)

let pp_option option pp = 
  pp_maybe option (pp_enclose ~pre:"" ~post:" option") pp

let pp_vdecl env option fmt x = 
  Format.fprintf fmt "%a:%a" 
    (pp_var env) x 
    (pp_ty option) x.v_ty
  
let pp_params env fmt params = 
  Format.fprintf fmt "@[%a@]"
    (pp_list ",@ " (pp_vdecl env false)) params 

let pp_locals env fmt locals = 
  let locarr = 
    List.filter (fun x -> match x.v_ty with Arr _ -> true | _ -> false) 
      locals in
  let locarr = 
    List.sort (fun x1 x2 -> compare x1.v_name x2.v_name) locarr in 

  let pp_vdecl = pp_vdecl env (for_safety env) in
  let pp_loc fmt x = Format.fprintf fmt "var %a;" pp_vdecl x in

  let pp_init fmt x = 
    Format.fprintf fmt "%a <- witness;"  (pp_var env) x in
  Format.fprintf fmt "%a@ %a" 
  (pp_list "@ " pp_loc) locals
  (pp_list "@ " pp_init) locarr 

let pp_rty env fmt tys =
  if tys = [] then
    Format.fprintf fmt "unit"
  else
    Format.fprintf fmt "@[%a@]" 
      (pp_list " *@ " (pp_ty env)) tys 

let pp_ret env fmt xs = 
  Format.fprintf fmt "@[return (%a);@]"
    (pp_list ",@ " (fun fmt x -> pp_ovar env fmt (L.unloc x))) xs

let pp_opn fmt op =
  let s = Printer.pp_opn op in
  Format.fprintf fmt "%s" s

let pp_lval1 env pp_e fmt (lv, (ety, e)) = 
  let lty = ty_lval lv in
  let pp_e fmt e = pp_e fmt (lty, ety, e) in
  match lv with 
  | Lnone _ -> assert false
  | Lmem(ws, x, e1) -> 
    Format.fprintf fmt "@[Glob.mem <-@ storeW%a Glob.mem (W64.to_uint %a) %a;@]" pp_size ws
      (pp_wcast env) (add64 x e1) pp_e e
  | Lvar x  -> 
    Format.fprintf fmt "@[%a <-@ %a;@]" (pp_var env) (L.unloc x) pp_e e
  | Laset (ws, x,e1) -> 
    assert (check_array env x);
    let x = L.unloc x in
    let (xws,n) = array_kind x.v_ty in
    if ws = xws then
      Format.fprintf fmt "@[%a.[%a] <-@ %a;@]"
        (pp_var env) x (pp_expr env) e1 pp_e e
    else
      let nws = n * int_of_ws xws in
      let nws8 = nws / 8 in
      Format.fprintf fmt 
        "@[%a =@ @[Array%i.init@ (WArray%i.get%i (WArray%i.set%i %a %a %a));@]@]"
        (pp_var env) x n nws8 (int_of_ws xws) nws8 (int_of_ws ws)
        (pp_initi env) (x, n, xws) (pp_expr env) e1 pp_e e
 
let pp_lval env fmt = function
  | Lnone _ -> assert false
  | Lmem _ -> assert false 
  | Lvar x  -> pp_var env fmt (L.unloc x)
  | Laset _  -> assert false 
 
let pp_lvals env fmt xs = 
  match xs with
  | []  -> assert false
  | [x] -> pp_lval env fmt x 
  | _   -> Format.fprintf fmt "(%a)" (pp_list ",@ " (pp_lval env)) xs

let pp_aux_lvs fmt aux = 
  match aux with
  | []  -> assert false
  | [x] -> Format.fprintf fmt "%s" x
  | xs  -> Format.fprintf fmt "(%a)" (pp_list ",@ " pp_string) xs

module Normal = struct  

  let all_vars lvs = 
    let is_lvar = function Lvar _ -> true | _ -> false in
    List.for_all is_lvar lvs

  let check_lvals lvs = 
    match lvs with
    | [] -> assert false
    | [lv] -> begin match lv with Lvar _ | Laset _ -> true | _ -> false end
    | _ -> all_vars lvs 

  let rec init_aux_i env i = 
    match i.i_desc with
    | Cassgn _ -> env
    | Cif(_, c1, c2) | Cwhile(_, c1, _, c2) -> init_aux (init_aux env c1) c2
    | Cfor(_,_,c) -> init_aux (add_aux env [tint]) c
    | Copn (lvs, _, op, _) -> 
      if List.length lvs = 1 then env 
      else
        let tys  = List.map Conv.ty_of_cty (E.sopn_tout op) in
        let ltys = List.map ty_lval lvs in
        if all_vars lvs && ltys = tys then env
        else add_aux env tys
    | Ccall(_, lvs, f, _) ->      
      if lvs = [] then env 
      else 
        let tys = (*List.map Conv.ty_of_cty *)(fst (get_funtype env f)) in
        let ltys = List.map ty_lval lvs in
        if (check_lvals lvs && ltys = tys) then env
        else add_aux env tys
   
  and init_aux env c = List.fold_left init_aux_i env c

  let pp_assgn_i env fmt lv (ety, aux) = 
    Format.fprintf fmt "@ %a" (pp_lval1 env (pp_cast pp_string)) (lv, (ety,aux))

  let pp_call env fmt lvs etys pp a = 
    let ltys = List.map (fun lv -> ty_lval lv) lvs in
    if check_lvals lvs && ltys = etys then 
      Format.fprintf fmt "@[%a %a;@]" (pp_lvals env) lvs pp a
    else
      let auxs = get_aux env etys in
      Format.fprintf fmt "@[%a %a;@]" pp_aux_lvs auxs pp a;
      let tyauxs = List.combine etys auxs in
      List.iter2 (pp_assgn_i env fmt) lvs tyauxs
  
  let rec pp_cmd env fmt c = 
    Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_instr env)) c

  and pp_instr env fmt i = 
    match i.i_desc with 
    | Cassgn (lv, _, _ty, e) ->
      let pp_e = pp_cast (pp_expr env) in
      pp_lval1 env pp_e fmt (lv , (ty_expr e, e))

    | Copn(lvs, _, op, es) ->
      let otys,itys = List.map Conv.ty_of_cty (E.sopn_tout op), List.map Conv.ty_of_cty (E.sopn_tin op) in
      let pp_e fmt (op,es) = 
        Format.fprintf fmt "%a %a" pp_opn op 
          (pp_list "@ " (pp_wcast env)) (List.combine itys es) in
      if List.length lvs = 1 then
        let pp_e = pp_cast pp_e in
        pp_lval1 env pp_e fmt (List.hd lvs , (List.hd otys, (op,es)))
      else
        let pp fmt (op, es) = 
          Format.fprintf fmt "<- %a" pp_e (op,es) in
        pp_call env fmt lvs otys pp (op,es) 
        
    | Ccall(_, lvs, f, es) ->
      let otys, itys = get_funtype env f in
      let pp_args fmt es = 
        pp_list ",@ " (pp_wcast env) fmt (List.combine itys es) in
      if lvs = [] then 
        Format.fprintf fmt "@[%a (%a);@]" (pp_fname env) f pp_args es
      else
        let pp fmt es = 
          Format.fprintf fmt "<%@ %a (%a)" (pp_fname env) f pp_args es in
        pp_call env fmt lvs otys pp es 

    | Cif(e,c1,c2) ->
      Format.fprintf fmt "@[<v>if (%a) {@   %a@ } else {@   %a@ }@]"
        (pp_expr env) e (pp_cmd env) c1 (pp_cmd env) c2
      
    | Cwhile(_, c1, e,c2) ->
      Format.fprintf fmt "@[<v>%a@ while (%a) {@   %a@ }@]"
        (pp_cmd env) c1 (pp_expr env) e (pp_cmd env) (c2@c1)
      
    | Cfor(i, (d,e1,e2), c) ->
      (* decreasing for loops have bounds swaped *)
      let e1, e2 = if d = UpTo then e1, e2 else e2, e1 in 
      let pp_init, pp_e2 = 
        match e2 with
        (* Can be generalized to the case where e2 is not modified by c and i *)
        | Pconst _ -> (fun _fmt () -> ()), (fun fmt () -> pp_expr env fmt e2)
        | _ -> 
          let aux = List.hd (get_aux env [tint]) in
          let pp_init fmt () = 
            Format.fprintf fmt "@[%s <-@ %a@];@ " aux (pp_expr env) e2 in
          let pp_e2 fmt () = pp_string fmt aux in
          pp_init, pp_e2 in
      let pp_i fmt () = pp_var env fmt (L.unloc i) in
      let pp_i1, pp_i2 = 
        if d = UpTo then pp_i , pp_e2
        else pp_e2, pp_i in
      Format.fprintf fmt 
        "@[<v>%a%a <- %a;@ while (%a < %a) {@   @[<v>%a@ %a <- %a %s 1;@]@ }@]"
        pp_init () 
        pp_i () (pp_expr env) e1 
        pp_i1 () pp_i2 ()
        (pp_cmd env) c
        pp_i () pp_i () (if d = UpTo then "+" else "-")

end

module Leak = struct 

  type safe_cond = 
    | Initv of var 
    | Initai of wsize * var * expr 
    | Inita of var * int
    | InBound of wsize * int * expr
    | Valid of wsize * expr 
    | NotZero of wsize * expr 

  let in_bound ws x e = 
    match (L.unloc x).v_ty with
    | Arr(ws1,n) -> InBound(ws, (arr_size ws1 n), e)
    | _ -> assert false

  let safe_op2 safe _e1 e2 = function
    | E.Oand    | E.Oor     
    | E.Oadd _  | E.Omul _  | E.Osub _ 
    | E.Oland _ | E.Olor _  | E.Olxor _ 
    | E.Olsr _  | E.Olsl _  | E.Oasr _
    | E.Oeq _   | E.Oneq _  | E.Olt _  | E.Ole _ | E.Ogt _ | E.Oge _ 
    | E.Ovadd _ | E.Ovsub _ | E.Ovmul _
    | E.Ovlsr _ | E.Ovlsl _ | E.Ovasr _ -> safe

    | E.Odiv E.Cmp_int -> safe 
    | E.Omod Cmp_int  -> safe
    | E.Odiv (E.Cmp_w(_, s)) -> NotZero (s, e2) :: safe 
    | E.Omod (E.Cmp_w(_, s)) -> NotZero (s, e2) :: safe 
    
  let is_init env x safe = 
    let (_s,option) = Mv.find (L.unloc x) env.vars in
    if option then Initv (L.unloc x) :: safe
    else safe
    
  let rec safe_e_rec env safe = function
    | Pconst _ | Pbool _ | Parr_init _ | Pglobal _ -> safe
    | Pvar x -> 
      let (_s,option) = Mv.find (L.unloc x) env.vars in
      if option then
        match (L.unloc x).v_ty with
        | Arr(ws,n) -> Inita (L.unloc x, arr_size ws n) :: safe
        | _ -> Initv(L.unloc x) :: safe 
      else safe 
    | Pload (ws,x,e) -> 
      is_init env x (Valid (ws, snd (add64 x e)) :: safe_e_rec env safe e)
    | Papp1 (_, e) -> safe_e_rec env safe e
    | Pget (ws, x, e) -> 
      let safe = 
        let (_s,option) = Mv.find (L.unloc x) env.vars in
        if option then Initai(ws, L.unloc x, e) :: safe 
        else safe in
      in_bound ws x e :: safe 
    | Papp2 (op, e1, e2) -> 
      safe_op2 (safe_e_rec env (safe_e_rec env safe e1) e2) e1 e2 op
    | PappN (_op, _es) -> assert false (* TODO: nary *)
    | Pif  (_,e1, e2, e3) -> 
      safe_e_rec env (safe_e_rec env (safe_e_rec env safe e1) e2) e3

  let safe_e env = safe_e_rec env [] 

  let safe_es env = List.fold_left (safe_e_rec env) []

  let safe_opn safe opn es = 
    let id = Expr.get_instr opn in
    List.map (fun c ->
        match c with
        | X86_decl.NotZero(sz, i) ->
          NotZero(sz, List.nth es (Conv.int_of_nat i))) id.i_safe @ safe
 
  let safe_lval env = function
    | Lnone _ | Lvar _ -> []
    | Lmem(ws, x, e) -> 
      is_init env x (Valid (ws, snd (add64 x e)) :: safe_e_rec env [] e)
    | Laset(ws, x,e) -> in_bound ws x e :: safe_e_rec env [] e 

  let pp_safe_e env fmt = function
    | Initv x -> Format.fprintf fmt "is_init %a" (pp_var env) x
    | Initai(ws, x,e) -> Format.fprintf fmt "is_init%i %a %a" 
                           (int_of_ws ws) (pp_var env) x (pp_expr env) e
    | Inita(x,n) -> Format.fprintf fmt "Array%i.is_init %a" n (pp_var env) x 
    | Valid (sz, e) -> Format.fprintf fmt "is_valid Glob.mem %a W%a" (pp_expr env) e pp_size sz 
    | NotZero(sz,e) -> Format.fprintf fmt "%a <> W%a.zeros" (pp_expr env) e pp_size sz
    | InBound(ws, n,e)  -> Format.fprintf fmt "in_bound %a %i %i" 
                             (pp_expr env) e (size_of_ws ws) n

  let pp_safe_es env fmt es = pp_list "/\\@ " (pp_safe_e env) fmt es

  let pp_leaks env fmt es = 
    Format.fprintf fmt "leakages <- LeakAddr(@[[%a]@]) :: leakages;@ "
      (pp_list ";@ " (pp_expr env)) es

  let pp_safe_cond env fmt conds = 
    if conds <> [] then 
      Format.fprintf fmt "safe <- @[safe /\\ %a@];@ " (pp_safe_es env) conds 
    
  let pp_leaks_e env fmt e =
    match env.model with
    | ConstantTime -> pp_leaks env fmt (leaks_e e)
    | Safety -> pp_safe_cond env fmt (safe_e env e)
    | _ -> ()

  let pp_leaks_es env fmt es = 
    match env.model with
    | ConstantTime -> pp_leaks env fmt (leaks_es es)
    | Safety -> pp_safe_cond env fmt (safe_es env es)
    | _ -> ()
    
  let pp_leaks_opn env fmt op es = 
    match env.model with
    | ConstantTime -> pp_leaks env fmt (leaks_es es)
    | Safety -> 
      let conds = safe_opn (safe_es env es) op es in
      pp_safe_cond env fmt conds 
    | Normal -> ()

  let pp_leaks_if env fmt e = 
    match env.model with
    | ConstantTime -> 
      let leaks = leaks_e e in
      Format.fprintf fmt 
        "leakages <- LeakCond(%a) :: LeakAddr(@[[%a]@]) :: leakages;@ "
        (pp_expr env) e (pp_list ";@ " (pp_expr env)) leaks
    | Safety -> pp_safe_cond env fmt (safe_e env e)
    | Normal -> ()

  let pp_leaks_for env fmt e1 e2 = 
    match env.model with
    | ConstantTime -> 
      let leaks = leaks_es [e1;e2] in
      Format.fprintf fmt 
        "leakages <- LeakFor(%a,%a) :: LeakAddr(@[[%a]@]) :: leakages;@ "
        (pp_expr env) e1 (pp_expr env) e2 
        (pp_list ";@ " (pp_expr env)) leaks
    | Safety -> pp_safe_cond env fmt (safe_es env [e1;e2])
    | Normal -> ()

  let pp_leaks_lv env fmt lv = 
    match env.model with
    | ConstantTime -> 
      let leaks = leaks_lval lv in
      if leaks <> [] then pp_leaks env fmt leaks
    | Safety -> pp_safe_cond env fmt (safe_lval env lv)
    | _ -> ()

  let rec init_aux_i env i = 
    match i.i_desc with
    | Cassgn (lv, _, _, _) -> add_aux env [ty_lval lv]
    | Copn (lvs, _, _, _) -> add_aux env (List.map ty_lval lvs)
    | Ccall(_, lvs, _, _) -> 
      if lvs = [] then env 
      else add_aux env (List.map ty_lval lvs)
    | Cif(_, c1, c2) | Cwhile(_, c1, _, c2) -> init_aux (init_aux env c1) c2
    | Cfor(_,_,c) -> 
      if for_safety env then
        init_aux (add_aux env [tint; tint]) c
      else
        init_aux (add_aux env [tint]) c

    
  and init_aux env c = List.fold_left init_aux_i env c
 
  let pp_some env pp lv fmt e = 
    if for_safety env then
      match lv with
      | Lnone _ -> ()
      | Lvar x ->
        let x = L.unloc x in
        let _s, option = Mv.find x env.vars in
        if option then
          let ty = x.v_ty in
          if is_ty_arr ty then
            let (_ws,n) = array_kind ty in
            Format.fprintf fmt "(Array%i.map Some %a)" n pp e
          else Format.fprintf fmt "(Some %a)" pp e 
        else pp fmt e 
      | Lmem _ -> pp fmt e
      | Laset _ -> pp fmt e
    else pp fmt e

  let pp_assgn_i env fmt lv (ety, aux) = 
    Format.fprintf fmt "@ "; pp_leaks_lv env fmt lv;
    let pp_e = pp_some env (pp_cast pp_string) lv in
    pp_lval1 env pp_e fmt (lv, (ety,aux))

  let pp_call env fmt lvs etys pp a = 
    let auxs = get_aux env etys in
    Format.fprintf fmt "@[%a %a;@]" pp_aux_lvs auxs pp a;
    let tyauxs = List.combine etys auxs in
    List.iter2 (pp_assgn_i env fmt) lvs tyauxs
        
  let rec pp_cmd env fmt c = 
    Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_instr env)) c

  and pp_instr env fmt i = 
    match i.i_desc with 
    | Cassgn (lv, _, _, e) ->
      pp_leaks_e env fmt e;
      let pp fmt e = Format.fprintf fmt "<- %a" (pp_expr env) e in
      pp_call env fmt [lv] [ty_expr e] pp e 

    | Copn(lvs, _, op, es) ->
      let otys,itys = List.map Conv.ty_of_cty (E.sopn_tout op), List.map Conv.ty_of_cty (E.sopn_tin op) in
      let pp fmt (op, es) = 
        Format.fprintf fmt "<- %a %a" pp_opn op 
          (pp_list "@ " (pp_wcast env)) (List.combine itys es) in
      pp_leaks_opn env fmt op es;
      pp_call env fmt lvs otys pp (op, es)
      
    | Ccall(_, lvs, f, es) ->
      let otys, itys = get_funtype env f in
      let pp_args fmt es = 
        pp_list ",@ " (pp_wcast env) fmt (List.combine itys es) in
      pp_leaks_es env fmt es;
      if lvs = [] then 
        Format.fprintf fmt "@[%a (%a);@]" (pp_fname env) f pp_args es
      else
        let pp fmt es = 
          Format.fprintf fmt "<%@ %a (%a)" (pp_fname env) f pp_args es in
        pp_call env fmt lvs otys pp es 

    | Cif(e,c1,c2) ->
      pp_leaks_if env fmt e;
      Format.fprintf fmt "@[<v>if (%a) {@   %a@ } else {@   %a@ }@]"
        (pp_expr env) e (pp_cmd env) c1 (pp_cmd env) c2
      
    | Cwhile(_, c1, e,c2) ->
      let pp_leak fmt e = 
        Format.fprintf fmt "@ %a" (pp_leaks_if env) e in
      Format.fprintf fmt "@[<v>%a%a@ while (%a) {@   %a%a@ }@]"
        (pp_cmd env) c1 pp_leak e (pp_expr env) e 
        (pp_cmd env) (c2@c1) pp_leak e

    | Cfor(i, (d,e1,e2), c) ->
      pp_leaks_for env fmt e1 e2;
      let aux, env1 = 
        if for_safety env then 
          let auxs = get_aux env [tint;tint] in
          List.hd auxs, set_var env (L.unloc i) false (List.nth auxs 1) 
        else List.hd (get_aux env [tint]), env in
      let pp_init, pp_e2 = 
        match e2 with
        (* Can be generalized to the case where e2 is not modified by c and i *)
        | Pconst _ -> (fun _fmt () -> ()), (fun fmt () -> pp_expr env fmt e2)
        | _ -> 
          let pp_init fmt () = 
            Format.fprintf fmt "@[%s <-@ %a@];@ " aux (pp_expr env) e2 in
          let pp_e2 fmt () = pp_string fmt aux in
          pp_init, pp_e2 in
      let pp_i fmt () = pp_var env1 fmt (L.unloc i) in
      let pp_i1, pp_i2 = 
        if d = UpTo then pp_i , pp_e2
        else pp_e2, pp_i in
      let pp_restore fmt () = 
        if for_safety env then
          Format.fprintf fmt "@ @[%a <- %a;@]"
            (pp_var env) (L.unloc i) (pp_some env pp_i (Lvar i)) () in
      Format.fprintf fmt 
        "@[<v>%a%a <- %a;@ while (%a < %a) {@   @[<v>%a@ %a <- %a %s 1;@]@ }%a@]"
        pp_init () 
        pp_i () (pp_expr env) e1 
        pp_i1 () pp_i2 ()
        (pp_cmd env1) c
        pp_i () pp_i () (if d = UpTo then "+" else "-")
        pp_restore ()
        
end 

let pp_aux fmt env = 
  let pp ty aux = 
    Format.fprintf fmt "@[var %s:@ %a@];@ " aux (pp_ty false) ty in
  Mty.iter (fun ty -> List.iter (pp ty)) env.auxv

let pp_safe_ret env fmt xs =
  if for_safety env then
    let es = List.map (fun x -> Pvar x) xs in
    Leak.pp_safe_cond env fmt (Leak.safe_es env es)

let pp_fun env fmt f = 
  let locals = Sv.elements (locals f) in
  (* initialize the env *)
  let env = List.fold_left (add_var false) env f.f_args in
  let env = List.fold_left (add_var (for_safety env)) env locals in  
  (* init auxiliary variables *) 
  let env = 
    if env.model = Normal then Normal.init_aux env f.f_body
    else Leak.init_aux env f.f_body in

  (* Print the function *)
  (* FIXME ajouter les conditions d'initialisation 
     sur les variables de retour *)
  let pp_cmd = 
    if env.model = Normal then Normal.pp_cmd
    else Leak.pp_cmd in
  Format.fprintf fmt 
    "@[<v>proc %a (%a) : %a = {@   @[<v>%a@ %a@ %a@ %a%a@]@ }@]"
    (pp_fname env) f.f_name
    (pp_params env) f.f_args 
    (pp_rty false) f.f_tyout
    pp_aux env
    (pp_locals env) locals
    (pp_cmd env) f.f_body
    (pp_safe_ret env) f.f_ret 
    (pp_ret env) f.f_ret

let pp_glob_decl env fmt (ws,x, z) =
  Format.fprintf fmt "@[abbrev %a = %a.of_int %a.@]@ "
    (pp_glob env) x pp_Tsz ws pp_print_i z

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
  {env with arrsz = Sv.fold add_sz vars env.arrsz;
            warrsz = Sv.fold add_wsz vars env.warrsz; }

let pp_array_decl i = 
  let file = Format.sprintf "Array%i.ec" i in
  let out = open_out file in
  let fmt = Format.formatter_of_out_channel out in
  Format.fprintf fmt "@[<v>from Jasmin require import JArray.@ @ ";
  Format.fprintf fmt "clone export PolyArray as Array%i  with op size <- %i.@]@." i i;
  close_out out

let pp_warray_decl i = 
  let file = Format.sprintf "WArray%i.ec" i in
  let out = open_out file in
  let fmt = Format.formatter_of_out_channel out in
  Format.fprintf fmt "@[<v>from Jasmin require import JWord_array.@ @ ";
  Format.fprintf fmt "clone export WArray as WArray%i  with op size <- %i.@]@." i i;
  close_out out

let pp_prog fmt model globs funcs = 

  let env = empty_env model funcs in
  let env = 
    List.fold_left (fun env (ws, x, _) -> add_glob env x ws)
      env globs in
  let env = List.fold_left add_arrsz env funcs in

  Sint.iter pp_array_decl env.arrsz;
  Sint.iter pp_warray_decl env.warrsz;

  let pp_arrays arr fmt s = 
    let l = Sint.elements s in
    let pp_i fmt i = Format.fprintf fmt "%s%i" arr i in
    if l <> [] then
      Format.fprintf fmt "require import @[%a@].@ " (pp_list "@ " pp_i) l in

  let pp_leakages fmt env = 
    match env.model with
    | ConstantTime ->
      Format.fprintf fmt "var leakages : leakages_t@ @ " 
    | Safety -> 
      Format.fprintf fmt "var safe : bool@ @ " 
    | Normal -> () in

  Format.fprintf fmt 
     "@[<v>%s.@ %s.@ @ %a%a@ %a@ @ module M = {@   @[<v>%a%a@]@ }.@ @]@." 
    "require import AllCore IntDiv CoreMap List"
    "from Jasmin require import JModel"
    (pp_arrays "Array") env.arrsz
    (pp_arrays "WArray") env.warrsz
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
  | Cwhile(_,c1,_,c2)   -> used_func_c (used_func_c used c1) c2
  | Ccall (_,_,f,_)   -> Ss.add f.fn_name used

let extract fmt model ((globs,funcs):'a prog) tokeep = 
  let funcs = List.map Regalloc.fill_in_missing_names funcs in
  let tokeep = ref (Ss.of_list tokeep) in
  let dofun f = 
    if Ss.mem f.f_name.fn_name !tokeep then
      (tokeep := Ss.union (used_func f) !tokeep; true)
    else false in
  let funcs = List.filter dofun funcs in
  pp_prog fmt model globs (List.rev funcs)

