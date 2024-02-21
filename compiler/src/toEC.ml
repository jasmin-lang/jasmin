open Utils
open Wsize
open Prog
open PrintCommon
module E = Expr

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
    arrsz  : Sint.t ref;
    warrsz : Sint.t ref;
    auxv  : string list Mty.t;
    randombytes : Sint.t ref;
  }

let for_safety    env = env.model = Utils.Safety

(* --------------------------------------------------------------- *)

let rec read_mem_e = function
  | Pconst _ | Pbool _ | Parr_init _ |Pvar _ -> false
  | Pload _ -> true
  | Papp1 (_, e) | Pget (_, _, _, _, e) | Psub (_, _, _, _, e) -> read_mem_e e
  | Papp2 (_, e1, e2) -> read_mem_e e1 || read_mem_e e2
  | PappN (_, es) -> read_mem_es es
  | Pif  (_, e1, e2, e3) -> read_mem_e e1 || read_mem_e e2 || read_mem_e e3

and read_mem_es es = List.exists read_mem_e es

let read_mem_lval = function
  | Lnone _ | Lvar _ -> false
  | Lmem (_,_,_,_) -> true
  | Laset (_,_,_,_,e) | Lasub (_,_,_,_,e)-> read_mem_e e


let write_mem_lval = function
  | Lnone _ | Lvar _ | Laset _ | Lasub _ -> false
  | Lmem _ -> true

let read_mem_lvals = List.exists read_mem_lval
let write_mem_lvals = List.exists write_mem_lval

let rec read_mem_i s i =
  match i.i_desc with
  | Cassgn (x, _, _, e) -> read_mem_lval x || read_mem_e e
  | Copn (xs, _, _, es) | Csyscall (xs, Syscall_t.RandomBytes _, es) -> read_mem_lvals xs || read_mem_es es
  | Cif (e, c1, c2)     -> read_mem_e e || read_mem_c s c1 || read_mem_c s c2
  | Cwhile (_, c1, e, c2)  -> read_mem_c s c1 || read_mem_e e || read_mem_c s c2
  | Ccall (xs, fn, es) -> read_mem_lvals xs || Sf.mem fn s || read_mem_es es
  | Cfor (_, (_, e1, e2), c) -> read_mem_e e1 || read_mem_e e2 || read_mem_c s c

and read_mem_c s = List.exists (read_mem_i s)

let read_mem_f s f = read_mem_c s f.f_body

let rec write_mem_i s i =
  match i.i_desc with
  | Cassgn (x, _, _, _)  -> write_mem_lval x 
  | Copn (xs, _, _, _) | Csyscall(xs, Syscall_t.RandomBytes _, _) -> write_mem_lvals xs
  | Cif (_, c1, c2)      -> write_mem_c s c1 ||write_mem_c s c2
  | Cwhile (_, c1, _, c2)   -> write_mem_c s c1 ||write_mem_c s c2
  | Ccall (xs, fn, _) -> write_mem_lvals xs || Sf.mem fn s
  | Cfor (_, _, c)       -> write_mem_c s c 

and write_mem_c s = List.exists (write_mem_i s)

let write_mem_f s f = write_mem_c s f.f_body

let init_use fs = 
  let add t s f = if t s f then Sf.add f.f_name s else s in
  List.fold_left 
    (fun (sr,sw) f -> add read_mem_f sr f, add write_mem_f sw f)
    (Sf.empty, Sf.empty) fs

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

let normalize_name n =
  n |> String.uncapitalize_ascii |> escape

let mkfunname env fn =
  fn.fn_name |> normalize_name |> create_name env

let empty_env model fds arrsz warrsz randombytes =

  let env = { 
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
let pp_fname env fmt f = Format.fprintf fmt "%s" (get_funname env f)

let pp_syscall env fmt o =
  match o with
  | Syscall_t.RandomBytes p ->
    let n = (Conv.int_of_pos p) in
    env.randombytes := Sint.add n !(env.randombytes);
    Format.fprintf fmt "%s.randombytes_%i" syscall_mod_arg n

let ty_lval = function
  | Lnone (_, ty) -> ty
  | Lvar x -> (L.unloc x).v_ty
  | Lmem (_, ws,_,_) -> Bty (U ws)
  | Laset(_, _, ws, _, _) -> Bty (U ws)
  | Lasub (_,ws, len, _, _) -> Arr(ws, len) 


let add_Array env n =
  env.arrsz := Sint.add n !(env.arrsz)

let pp_Array env fmt n = 
  add_Array env n;
  Format.fprintf fmt "Array%i" n

let add_WArray env n =
  env.warrsz := Sint.add n !(env.warrsz)

let pp_WArray env fmt n = 
  add_WArray env n;
  Format.fprintf fmt "WArray%i" n

let pp_ty env fmt ty = 
  match ty with
  | Bty Bool -> Format.fprintf fmt "bool"
  | Bty Int  -> Format.fprintf fmt "int"
  | Bty (U ws) -> pp_sz_t fmt ws
  | Arr(ws,n) -> Format.fprintf fmt "%a %a.t" pp_sz_t ws (pp_Array env) n

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
  let s = normalize_name x.v_name in
  let s = create_name env s in
  set_var env x option s

let add_glob env x =
  let s = create_name env (normalize_name x.v_name) in
  set_var env x false s

let pp_oget option pp = 
  pp_maybe option (pp_enclose ~pre:"(oget " ~post:")") pp

let pp_var env fmt (x:var) = 
  pp_string fmt (fst (Mv.find x env.vars))

let pp_ovar env fmt (x:var) = 
  let (s,option) = Mv.find x env.vars in
  if option then
    let ty = x.v_ty in
    if is_ty_arr ty then
      let (_ws,n) = array_kind ty in
      Format.fprintf fmt "(%a.map oget %s)" (pp_Array env) n s
    else pp_oget true pp_string fmt s
  else pp_string fmt s

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

let pp_initi env pp fmt (x, n, ws) =
  let i = create_name env "i" in
  Format.fprintf fmt 
    "@[(%a.init%i (fun %s => (%a).[%s]))@]"
    (pp_WArray env) (arr_size ws n) (int_of_ws ws) i pp x i
    
let pp_print_i fmt z = 
  if Z.leq Z.zero z then Z.pp_print fmt z 
  else Format.fprintf fmt "(%a)" Z.pp_print z 

let pp_access aa = if aa = Warray_.AAdirect then "_direct" else ""

let pp_cast env pp fmt (ty,ety,e) = 
  if ety = ty then pp fmt e 
  else 
    match ty with
    | Bty _ ->
      Format.fprintf fmt "(%a %a)" pp_zeroext (ws_of_ty ety, ws_of_ty ty) pp e 
    | Arr(ws, n) ->
      let wse, ne = array_kind ety in
      let i = create_name env "i" in
      Format.fprintf fmt 
        "@[(%a.init@ (fun %s => get%i@ %a@ %s))@]"
        (pp_Array env) n
        i
        (int_of_ws ws)
        (pp_initi env pp) (e, ne, wse)
        i


let rec pp_expr pd env fmt (e:expr) = 
  match e with
  | Pconst z -> Format.fprintf fmt "%a" pp_print_i z

  | Pbool b -> Format.fprintf fmt "%a" pp_bool b

  | Parr_init _n -> Format.fprintf fmt "witness"

  | Pvar x ->
    pp_ovar env fmt (L.unloc x.gv)

  | Pget(_, aa, ws, x, e) ->
    assert (check_array env x.gv);
    let pp fmt (x,e) = 
      let x = x.gv in
      let x = L.unloc x in
      let (xws,n) = array_kind x.v_ty in
      if ws = xws && aa = Warray_.AAscale then
        Format.fprintf fmt "@[%a.[%a]@]" (pp_var env) x (pp_expr pd env) e
      else
        Format.fprintf fmt "@[(get%i%s@ %a@ %a)@]" 
          (int_of_ws ws) 
          (pp_access aa)
          (pp_initi env (pp_var env)) (x, n, xws) (pp_expr pd env) e in
    let option = 
      for_safety env && snd (Mv.find (L.unloc x.gv) env.vars) in
    pp_oget option pp fmt (x,e)

  | Psub (aa, ws, len, x, e) -> 
    assert (check_array env x.gv);
    let i = create_name env "i" in
    let x = x.gv in
    let x = L.unloc x in
    let (xws,n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
      Format.fprintf fmt "@[(%a.init (fun %s => %a.[%a + %s]))@]"
        (pp_Array env) len
        i
        (pp_var env) x
        (pp_expr pd env) e
        i
    else 
      Format.fprintf fmt 
        "@[(%a.init (fun %s => (get%i%s@ %a@ (%a + %s))))@]" 
        (pp_Array env) len
        i
        (int_of_ws ws) 
        (pp_access aa)
        (pp_initi env (pp_var env)) (x, n, xws) 
        (pp_expr pd env) e 
        i 

    
  | Pload (_, sz, x, e) ->
    Format.fprintf fmt "(loadW%a Glob.mem (W%d.to_uint %a))"
      pp_size sz
      (int_of_ws pd)
      (pp_wcast pd env) (add_ptr pd (gkvar x) e)

  | Papp1 (op1, e) -> 
    Format.fprintf fmt "(%a %a)" pp_op1 op1 (pp_wcast pd env) (in_ty_op1 op1, e)

  | Papp2 (op2, e1, e2) ->  
    let ty1,ty2 = in_ty_op2 op2 in
    let te1, te2 = swap_op2 op2 (ty1, e1) (ty2, e2) in
    Format.fprintf fmt "(%a %a %a)"
      (pp_wcast pd env) te1 pp_op2 op2 (pp_wcast pd env) te2

  | PappN (op, es) ->
    (* FIXME *)
    begin match op with
    | Opack (ws, we) ->
      let i = int_of_pe we in
      let rec aux fmt es = 
        match es with
        | [] -> assert false
        | [e] -> Format.fprintf fmt "%a" (pp_expr pd env) e
        | e::es -> 
          Format.fprintf fmt "@[(%a %%%% 2^%i +@ 2^%i * %a)@]"
            (pp_expr pd env) e i i aux es in
      Format.fprintf fmt "(W%a.of_int %a)" pp_size ws aux (List.rev es)
    | Ocombine_flags c -> 
      Format.fprintf fmt "@[(%s@ %a)@]"
        (Printer.string_of_combine_flags c) 
        (pp_list "@ " (pp_expr pd env)) es
    end

  | Pif(_,e1,et,ef) -> 
    let ty = ty_expr e in
    Format.fprintf fmt "(%a ? %a : %a)"
      (pp_expr pd env) e1 (pp_wcast pd env) (ty,et) (pp_wcast pd env) (ty,ef)

and pp_wcast pd env fmt (ty, e) = 
  pp_cast env (pp_expr pd env) fmt (ty, ty_expr e, e)

let pp_vdecl env fmt x = 
  Format.fprintf fmt "%a:%a" 
    (pp_var env) x 
    (pp_ty env) x.v_ty
  
let pp_params env fmt params = 
  Format.fprintf fmt "@[%a@]"
    (pp_list ",@ " (pp_vdecl env)) params 

let pp_locals env fmt locals = 
  let locarr = 
    List.filter (fun x -> match x.v_ty with Arr _ -> true | _ -> false) 
      locals in
  let locarr = 
    List.sort (fun x1 x2 -> compare x1.v_name x2.v_name) locarr in 

  let pp_vdecl = pp_vdecl env in
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

let pp_lval1 pd env pp_e fmt (lv, (ety, e)) = 
  let lty = ty_lval lv in
  let pp_e fmt e = pp_e fmt (lty, ety, e) in
  match lv with 
  | Lnone _ -> assert false
  | Lmem(_, ws, x, e1) ->
    Format.fprintf fmt "@[Glob.mem <-@ storeW%a Glob.mem (W%d.to_uint %a) (%a);@]" pp_size ws
      (int_of_ws pd)
      (pp_wcast pd env) (add_ptr pd (gkvar x) e1) pp_e e
  | Lvar x  -> 
    Format.fprintf fmt "@[%a <-@ %a;@]" (pp_var env) (L.unloc x) pp_e e
  | Laset (_, aa, ws, x, e1) ->
    assert (check_array env x);
    let x = L.unloc x in
    let (xws,n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
      Format.fprintf fmt "@[%a.[%a] <-@ %a;@]"
        (pp_var env) x (pp_expr pd env) e1 pp_e e
    else
      let nws = n * int_of_ws xws in
      let nws8 = nws / 8 in
      Format.fprintf fmt 
        "@[%a <-@ @[%a.init@ (%a.get%i (%a.set%i%s %a %a (%a)));@]@]"
        (pp_var env) x 
        (pp_Array env) n 
        (pp_WArray env) nws8 
        (int_of_ws xws) 
        (pp_WArray env) nws8 (int_of_ws ws)
        (pp_access aa)
        (pp_initi env (pp_var env)) (x, n, xws) (pp_expr pd env) e1 pp_e e
  | Lasub (aa, ws, len, x, e1) -> 
    assert (check_array env x);
    let x = L.unloc x in
    let (xws, n) = array_kind x.v_ty in
    if ws = xws && aa = Warray_.AAscale then
      let i = create_name env "i" in
      Format.fprintf fmt 
      "@[%a <- @[%a.init@ @[(fun %s => if %a <= %s < %a + %i@ then %a.[%s-%a]@ else %a.[%s]);@]@]@]"
      (pp_var env) x 
      (pp_Array env) n 
      i
      (pp_expr pd env) e1 
      i
      (pp_expr pd env) e1 len
      pp_e e 
      i
      (pp_expr pd env) e1
      (pp_var env) x
      i
    else 
      let nws = n * int_of_ws xws in
      let nws8 = nws / 8 in
      let pp_start fmt () = 
        if aa = Warray_.AAscale then
          Format.fprintf fmt "(%i * %a)" (int_of_ws ws / 8) (pp_expr pd env) e1
        else
          Format.fprintf fmt "%a" (pp_expr pd env) e1 in
      let len8 = len * int_of_ws ws / 8 in
      let pp_a fmt () =
        let i = create_name env "i" in
        Format.fprintf fmt 
          "@[(%a.init8@ (fun %s =>@ if %a <= %s < %a + %i@ then %a.get8 %a (%s - %a)@ else %a.get8 %a %s))@]"
        (pp_WArray env) nws8
        i
        pp_start () i pp_start () len8
        (pp_WArray env) len8 (pp_initi env pp_e) (e, len, ws) i pp_start () 
        (pp_WArray env) nws8 (pp_initi env (pp_var env)) (x,n,xws) i
        
        in
        
      Format.fprintf fmt "@[%a <- @[%a.init@ @[(%a.get%i %a);@]"
       (pp_var env) x 
       (pp_Array env) n 
       (pp_WArray env) nws8 (int_of_ws xws)
       pp_a ()
       
let pp_lval env fmt = function
  | Lnone _ -> assert false
  | Lmem _ -> assert false 
  | Lvar x  -> pp_var env fmt (L.unloc x)
  | Laset _  -> assert false 
  | Lasub _ -> assert false 

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

let pp_wzeroext pp_e fmt tyo tyi e =
  if tyi = tyo then pp_e fmt e
  else
    let szi, szo = ws_of_ty tyi, ws_of_ty tyo in
    Format.fprintf fmt "%a(%a)" pp_zeroext (szi, szo) pp_e e

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

let pp_opn pd asmOp fmt o = 
  let s = Format.asprintf "%a" (pp_opn pd asmOp) o in
  let s = if Ss.mem s keywords then s^"_" else s in
  Format.fprintf fmt "%s" s

module Normal = struct  

  let all_vars lvs = 
    let is_lvar = function Lvar _ -> true | _ -> false in
    List.for_all is_lvar lvs

  let check_lvals lvs =
    all_vars lvs

  let rec init_aux_i pd asmOp env i =
    match i.i_desc with
    | Cassgn _ -> env
    | Cif(_, c1, c2)
    | Cwhile(_, c1, _, c2) ->
        init_aux pd asmOp (init_aux pd asmOp env c1) c2
    | Cfor(_,_,c) -> init_aux pd asmOp (add_aux env [tint]) c
    | Copn (lvs, _, op, _) -> 
      if List.length lvs = 1 then env 
      else
        let tys  = List.map Conv.ty_of_cty (Sopn.sopn_tout pd asmOp op) in
        let ltys = List.map ty_lval lvs in
        if all_vars lvs && ltys = tys then env
        else add_aux env tys
    | Ccall(lvs, f, _) ->
      if lvs = [] then env 
      else 
        let tys = (*List.map Conv.ty_of_cty *)(fst (get_funtype env f)) in
        let ltys = List.map ty_lval lvs in
        if (check_lvals lvs && ltys = tys) then env
        else add_aux env tys
    | Csyscall(lvs, o, _) ->
      if lvs = [] then env
      else
        let tys = List.map Conv.ty_of_cty (Syscall.syscall_sig_u o).scs_tout in
        let ltys = List.map ty_lval lvs in
        if (check_lvals lvs && ltys = tys) then env
        else add_aux env tys

  and init_aux pd asmOp env c = List.fold_left (init_aux_i pd asmOp) env c

  let pp_assgn_i pd env fmt lv ((etyo, etyi), aux) =
    let pp_e fmt aux =
      pp_wzeroext pp_string fmt etyo etyi aux in
    Format.fprintf fmt "@ %a" (pp_lval1 pd env (pp_cast env pp_e)) (lv, (etyo,aux))


  let pp_call pd env fmt lvs etyso etysi pp a =
    let ltys = List.map (fun lv -> ty_lval lv) lvs in
    if check_lvals lvs && ltys = etyso && etyso = etysi then
      Format.fprintf fmt "@[%a %a;@]" (pp_lvals env) lvs pp a
    else
      let auxs = get_aux env etysi in
      Format.fprintf fmt "@[%a %a;@]" pp_aux_lvs auxs pp a;
      let tyauxs = List.combine (List.combine etyso etysi) auxs in
      List.iter2 (pp_assgn_i pd env fmt) lvs tyauxs

  let rec pp_cmd pd asmOp env fmt c =
    Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_instr pd asmOp env)) c

  and pp_instr pd asmOp env fmt i =
    match i.i_desc with 
    | Cassgn(v, _, _, Parr_init _) ->
      let pp_e fmt _ = Format.fprintf fmt "witness" in
      pp_lval1 pd env pp_e fmt (v, ((), ()))

    | Cassgn (lv, _, _ty, e) ->
      let pp_e = pp_cast env (pp_expr pd env) in
      pp_lval1 pd env pp_e fmt (lv , (ty_expr e, e))

    | Copn([], _, op, _es) ->
       (* Erase opn without any return values *)
       Format.fprintf fmt "(* Erased call to %a *)" (pp_opn pd asmOp) op

    | Copn(lvs, _, op, es) ->
      let op' = base_op op in
      (* Since we do not have merge for the moment only the output type can change *)
      let otys,itys = ty_sopn pd asmOp op es in
      let otys', _ = ty_sopn pd asmOp op' es in
      let pp_e fmt (op,es) = 
        Format.fprintf fmt "%a %a" (pp_opn pd asmOp) op
          (pp_list "@ " (pp_wcast pd env)) (List.combine itys es) in
      if List.length lvs = 1 then
        let pp_e fmt (op, es) =
          pp_wzeroext pp_e fmt (List.hd otys) (List.hd otys') (op, es) in
        let pp_e  = pp_cast env pp_e in
        pp_lval1 pd env pp_e fmt (List.hd lvs , (List.hd otys,  (op',es)))
      else
        let pp fmt (op, es) = 
          Format.fprintf fmt "<- %a" pp_e (op,es) in
        pp_call pd env fmt lvs otys otys' pp (op,es)
        
    | Ccall(lvs, f, es) ->
      let otys, itys = get_funtype env f in
      let pp_args fmt es = 
        pp_list ",@ " (pp_wcast pd env) fmt (List.combine itys es) in
      if lvs = [] then 
        Format.fprintf fmt "@[%a (%a);@]" (pp_fname env) f pp_args es
      else
        let pp fmt es = 
          Format.fprintf fmt "<%@ %a (%a)" (pp_fname env) f pp_args es in
        pp_call pd env fmt lvs otys otys pp es

    | Csyscall(lvs, o, es) ->
      let s = Syscall.syscall_sig_u o in
      let otys = List.map Conv.ty_of_cty s.scs_tout in
      let itys =  List.map Conv.ty_of_cty s.scs_tin in
      let pp_args fmt es =
        pp_list ",@ " (pp_wcast pd env) fmt (List.combine itys es) in
      if lvs = [] then
        Format.fprintf fmt "@[%a (%a);@]" (pp_syscall env) o pp_args es
      else
        let pp fmt es =
          Format.fprintf fmt "<%@ %a (%a)" (pp_syscall env) o pp_args es in
        pp_call pd env fmt lvs otys otys pp es

    | Cif(e,c1,c2) ->
      Format.fprintf fmt "@[<v>if (%a) {@   %a@ } else {@   %a@ }@]"
        (pp_expr pd env) e (pp_cmd pd asmOp env) c1 (pp_cmd pd asmOp env) c2
      
    | Cwhile(_, c1, e,c2) ->
      Format.fprintf fmt "@[<v>%a@ while (%a) {@   %a@ }@]"
        (pp_cmd pd asmOp env) c1 (pp_expr pd env) e (pp_cmd pd asmOp env) (c2@c1)
      
    | Cfor(i, (d,e1,e2), c) ->
      (* decreasing for loops have bounds swaped *)
      let e1, e2 = if d = UpTo then e1, e2 else e2, e1 in 
      let pp_init, pp_e2 = 
        match e2 with
        (* Can be generalized to the case where e2 is not modified by c and i *)
        | Pconst _ -> (fun _fmt () -> ()), (fun fmt () -> pp_expr pd env fmt e2)
        | _ -> 
          let aux = List.hd (get_aux env [tint]) in
          let pp_init fmt () = 
            Format.fprintf fmt "@[%s <-@ %a@];@ " aux (pp_expr pd env) e2 in
          let pp_e2 fmt () = pp_string fmt aux in
          pp_init, pp_e2 in
      let pp_i fmt () = pp_var env fmt (L.unloc i) in
      let pp_i1, pp_i2 = 
        if d = UpTo then pp_i , pp_e2
        else pp_e2, pp_i in
      Format.fprintf fmt 
        "@[<v>%a%a <- %a;@ while (%a < %a) {@   @[<v>%a@ %a <- %a %s 1;@]@ }@]"
        pp_init () 
        pp_i () (pp_expr pd env) e1 
        pp_i1 () pp_i2 ()
        (pp_cmd pd asmOp env) c
        pp_i () pp_i () (if d = UpTo then "+" else "-")

end

module Leak = struct 

  type safe_cond = 
    | Initv of var 
    | Initai of wsize * var * expr 
    | Inita of var * int
    | InBound of Memory_model.aligned * wsize * int * expr
    | Valid of wsize * expr 
    | NotZero of wsize * expr 

  let in_bound al ws x e =
    match (L.unloc x).v_ty with
    | Arr(ws1,n) -> InBound(al, ws, (arr_size ws1 n), e)
    | _ -> assert false

  let safe_op2 safe _e1 e2 = function
    | E.Obeq    | E.Oand    | E.Oor     
    | E.Oadd _  | E.Omul _  | E.Osub _ 
    | E.Oland _ | E.Olor _  | E.Olxor _ 
    | E.Olsr _  | E.Olsl _  | E.Oasr _
    | E.Orol _ | E.Oror _
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
   
  let rec safe_e_rec pd env safe = function
    | Pconst _ | Pbool _ | Parr_init _ -> safe
    | Pvar x -> 
      let x = x.gv in
      let (_s,option) = Mv.find (L.unloc x) env.vars in
      if option then
        match (L.unloc x).v_ty with
        | Arr(ws,n) -> Inita (L.unloc x, arr_size ws n) :: safe
        | _ -> Initv(L.unloc x) :: safe 
      else safe 
    | Pload (al, ws,x,e) -> (* TODO: alignment *)
      is_init env x (Valid (ws, snd (add_ptr pd (gkvar x) e)) :: safe_e_rec pd env safe e)
    | Papp1 (_, e) -> safe_e_rec pd env safe e
    | Pget (al, aa, ws, x, e) ->
      assert (aa = Warray_.AAscale); (* NOT IMPLEMENTED *)
      let x = x.gv in
      let safe = 
        let (_s,option) = Mv.find (L.unloc x) env.vars in
        if option then Initai(ws, L.unloc x, e) :: safe 
        else safe in
      in_bound al ws x e :: safe
    | Psub _ -> assert false (* NOT IMPLEMENTED *) 
    | Papp2 (op, e1, e2) -> 
      safe_op2 (safe_e_rec pd env (safe_e_rec pd env safe e1) e2) e1 e2 op
    | PappN (_op, _es) -> assert false (* TODO: nary *)
    | Pif  (_,e1, e2, e3) -> 
      safe_e_rec pd env (safe_e_rec pd env (safe_e_rec pd env safe e1) e2) e3

  let safe_e pd env = safe_e_rec pd env [] 

  let safe_es pd env = List.fold_left (safe_e_rec pd env) []

  let safe_opn pd asmOp env safe opn es =
    let id = Sopn.get_instr_desc pd asmOp opn in
    List.pmap (fun c ->
        match c with
        | Wsize.X86Division(sz, _sg) ->
          Some (NotZero(sz, List.nth es 2))
        (* FIXME: there are more properties to check *)
        | Wsize.InRange _ -> None
        (* FIXME: there are properties to check *)
        | Wsize.AllInit (ws, p, i) ->
          let e = List.nth es (Conv.int_of_nat i) in
          let y = match e with Pvar y -> y | _ -> assert false in
          let (_s,option) = Mv.find (L.unloc y.gv) env.vars in 
          if option then Some (Inita (L.unloc y.gv, arr_size ws (Conv.int_of_pos p)))
          else None) id.i_safe @ safe

  let safe_lval pd env = function
    | Lnone _ | Lvar _ -> []
    | Lmem(al, ws, x, e) -> (* TODO: alignment *)
      is_init env x (Valid (ws, snd (add_ptr pd (gkvar x) e)) :: safe_e_rec pd env [] e)
    | Laset(al, aa, ws, x,e) ->
      assert (aa = Warray_.AAscale); (* NOT IMPLEMENTED *)
      in_bound al ws x e :: safe_e_rec pd env [] e
    | Lasub _ -> assert false (* NOT IMPLEMENTED *) 

  let pp_safe_e pd env fmt = function
    | Initv x -> Format.fprintf fmt "is_init %a" (pp_var env) x
    | Initai(ws, x,e) -> Format.fprintf fmt "is_init%i %a %a" 
                           (int_of_ws ws) (pp_var env) x (pp_expr pd env) e
    | Inita(x,n) -> Format.fprintf fmt "%a.is_init %a" (pp_Array env) n (pp_var env) x 
    | Valid (sz, e) -> Format.fprintf fmt "is_valid Glob.mem %a W%a" (pp_expr pd env) e pp_size sz 
    | NotZero(sz,e) -> Format.fprintf fmt "%a <> W%a.zeros" (pp_expr pd env) e pp_size sz
    | InBound(al, ws, n,e)  -> Format.fprintf fmt "in_bound %a %a %i %i"
                             pp_bool (al = Aligned)
                             (pp_expr pd env) e (size_of_ws ws) n

  let pp_safe_es pd env fmt es = pp_list "/\\@ " (pp_safe_e pd env) fmt es

  let pp_leaks pd env fmt es = 
    Format.fprintf fmt "leakages <- LeakAddr(@[[%a]@]) :: leakages;@ "
      (pp_list ";@ " (pp_expr pd env)) es

  let pp_safe_cond pd env fmt conds = 
    if conds <> [] then 
      Format.fprintf fmt "safe <- @[safe /\\ %a@];@ " (pp_safe_es pd env) conds 
    
  let pp_leaks_e pd env fmt e =
    match env.model with
    | ConstantTime -> pp_leaks pd env fmt (leaks_e pd e)
    | Safety -> pp_safe_cond pd env fmt (safe_e pd env e)
    | _ -> ()

  let pp_leaks_es pd env fmt es = 
    match env.model with
    | ConstantTime -> pp_leaks pd env fmt (leaks_es pd es)
    | Safety -> pp_safe_cond pd env fmt (safe_es pd env es)
    | _ -> ()
    
  let pp_leaks_opn pd asmOp env fmt op es = 
    match env.model with
    | ConstantTime -> pp_leaks pd env fmt (leaks_es pd es)
    | Safety -> 
      let conds = safe_opn pd asmOp env (safe_es pd env es) op es in
      pp_safe_cond pd env fmt conds 
    | Normal -> ()

  let pp_leaks_if pd env fmt e = 
    match env.model with
    | ConstantTime -> 
      let leaks = leaks_e pd e in
      Format.fprintf fmt 
        "leakages <- LeakCond(%a) :: LeakAddr(@[[%a]@]) :: leakages;@ "
        (pp_expr pd env) e (pp_list ";@ " (pp_expr pd env)) leaks
    | Safety -> pp_safe_cond pd env fmt (safe_e pd env e)
    | Normal -> ()

  let pp_leaks_for pd env fmt e1 e2 = 
    match env.model with
    | ConstantTime -> 
      let leaks = leaks_es pd [e1;e2] in
      Format.fprintf fmt 
        "leakages <- LeakFor(%a,%a) :: LeakAddr(@[[%a]@]) :: leakages;@ "
        (pp_expr pd env) e1 (pp_expr pd env) e2 
        (pp_list ";@ " (pp_expr pd env)) leaks
    | Safety -> pp_safe_cond pd env fmt (safe_es pd env [e1;e2])
    | Normal -> ()

  let pp_leaks_lv pd env fmt lv = 
    match env.model with
    | ConstantTime -> 
      let leaks = leaks_lval pd lv in
      if leaks <> [] then pp_leaks pd env fmt leaks
    | Safety -> pp_safe_cond pd env fmt (safe_lval pd env lv)
    | _ -> ()

  let rec init_aux_i pd asmOp env i =
    match i.i_desc with
    | Cassgn (lv, _, _, e) -> add_aux (add_aux env [ty_lval lv]) [ty_expr e]
    | Copn (lvs, _, op, _) ->
       let op = base_op op in
       let tys  = List.map Conv.ty_of_cty (Sopn.sopn_tout pd asmOp op) in
       let env = add_aux env tys in
       add_aux env (List.map ty_lval lvs)
    | Csyscall(lvs, o, _)->
      let s = Syscall.syscall_sig_u o in
      let otys = List.map Conv.ty_of_cty s.scs_tout in
      let env = add_aux env otys in
      add_aux env (List.map ty_lval lvs)
    | Ccall(lvs, _, _) ->
      if lvs = [] then env 
      else add_aux env (List.map ty_lval lvs)
    | Cif(_, c1, c2) | Cwhile(_, c1, _, c2) -> init_aux pd asmOp (init_aux pd asmOp env c1) c2
    | Cfor(_,_,c) -> 
      if for_safety env then
        init_aux pd asmOp (add_aux env [tint; tint]) c
      else
        init_aux pd asmOp (add_aux env [tint]) c

  and init_aux pd asmOp env c = List.fold_left (init_aux_i pd asmOp) env c

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
            Format.fprintf fmt "(%a.map Some %a)" (pp_Array env) n pp e
          else Format.fprintf fmt "(Some %a)" pp e 
        else pp fmt e 
      | Lmem _ -> pp fmt e
      | Laset _ -> pp fmt e
      | Lasub _ -> assert false (* NOT IMPLEMENTED *) 
    else pp fmt e

  let pp_assgn_i pd env fmt lv ((etyo, etyi), aux) =
    Format.fprintf fmt "@ "; pp_leaks_lv pd env fmt lv;
    let pp_e fmt aux =
      pp_wzeroext pp_string fmt etyo etyi aux in
    let pp_e = pp_some env (pp_cast env pp_e) lv in
    pp_lval1 pd env pp_e fmt (lv, (etyo,aux))

  let pp_call pd env fmt lvs etyso etysi pp a =
    let auxs = get_aux env etysi in
    Format.fprintf fmt "@[%a %a;@]" pp_aux_lvs auxs pp a;
    let tyauxs = List.combine (List.combine etyso etysi) auxs in
    List.iter2 (pp_assgn_i pd env fmt) lvs tyauxs
        
  let rec pp_cmd pd asmOp env fmt c =
    Format.fprintf fmt "@[<v>%a@]" (pp_list "@ " (pp_instr pd asmOp env)) c

  and pp_instr pd asmOp env fmt i =
    match i.i_desc with 
    | Cassgn(v, _, _, (Parr_init _ as e)) ->
      pp_leaks_e pd env fmt e;
      let pp_e fmt _ = Format.fprintf fmt "witness" in
      pp_lval1 pd env pp_e fmt (v, ((), ()))

    | Cassgn (lv, _, _, e) ->
      pp_leaks_e pd env fmt e;
      let pp fmt e = Format.fprintf fmt "<- %a" (pp_expr pd env) e in
      let tys = [ty_expr e] in
      pp_call pd env fmt [lv] tys tys pp e

    | Copn([], _, op, es) ->
       (* Erase opn without return values but keep their leakage *)
       let op' = base_op op in
       pp_leaks_opn pd asmOp env fmt op' es;
       Format.fprintf fmt "(* Erased call to %a *)" (pp_opn pd asmOp) op

    | Copn(lvs, _, op, es) ->
      let op' = base_op op in
      (* Since we do not have merge for the moment only the output type can change *)
      let otys,itys = ty_sopn pd asmOp op es in
      let otys', _ = ty_sopn pd asmOp op' es in
      let pp fmt (op, es) = 
        Format.fprintf fmt "<- %a %a" (pp_opn pd asmOp) op
          (pp_list "@ " (pp_wcast pd env)) (List.combine itys es) in
      pp_leaks_opn pd asmOp env fmt op' es;
      pp_call pd env fmt lvs otys otys' pp (op, es)
      
    | Ccall(lvs, f, es) ->
      let otys, itys = get_funtype env f in
      let pp_args fmt es = 
        pp_list ",@ " (pp_wcast pd env) fmt (List.combine itys es) in
      pp_leaks_es pd env fmt es;
      if lvs = [] then 
        Format.fprintf fmt "@[%a (%a);@]" (pp_fname env) f pp_args es
      else
        let pp fmt es = 
          Format.fprintf fmt "<%@ %a (%a)" (pp_fname env) f pp_args es in
        pp_call pd env fmt lvs otys otys pp es

    | Csyscall(lvs, o, es) ->
      let s = Syscall.syscall_sig_u o in
      let otys = List.map Conv.ty_of_cty s.scs_tout in
      let itys =  List.map Conv.ty_of_cty s.scs_tin in

      let pp_args fmt es =
        pp_list ",@ " (pp_wcast pd env) fmt (List.combine itys es) in
      pp_leaks_es pd env fmt es;
      if lvs = [] then
        Format.fprintf fmt "@[%a (%a);@]" (pp_syscall env) o pp_args es
      else
        let pp fmt es =
          Format.fprintf fmt "<%@ %a (%a)" (pp_syscall env) o pp_args es in
        pp_call pd env fmt lvs otys otys pp es

    | Cif(e,c1,c2) ->
      pp_leaks_if pd env fmt e;
      Format.fprintf fmt "@[<v>if (%a) {@   %a@ } else {@   %a@ }@]"
        (pp_expr pd env) e (pp_cmd pd asmOp env) c1 (pp_cmd pd asmOp env) c2
      
    | Cwhile(_, c1, e,c2) ->
      let pp_leak fmt e = 
        Format.fprintf fmt "@ %a" (pp_leaks_if pd env) e in
      Format.fprintf fmt "@[<v>%a%a@ while (%a) {@   %a%a@ }@]"
        (pp_cmd pd asmOp env) c1 pp_leak e (pp_expr pd env) e
        (pp_cmd pd asmOp env) (c2@c1) pp_leak e

    | Cfor(i, (d,e1,e2), c) ->
      pp_leaks_for pd env fmt e1 e2;
      let aux, env1 = 
        if for_safety env then 
          let auxs = get_aux env [tint;tint] in
          List.hd auxs, set_var env (L.unloc i) false (List.nth auxs 1) 
        else List.hd (get_aux env [tint]), env in
      let pp_init, pp_e2 = 
        match e2 with
        (* Can be generalized to the case where e2 is not modified by c and i *)
        | Pconst _ -> (fun _fmt () -> ()), (fun fmt () -> pp_expr pd env fmt e2)
        | _ -> 
          let pp_init fmt () = 
            Format.fprintf fmt "@[%s <-@ %a@];@ " aux (pp_expr pd env) e2 in
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
        pp_i () (pp_expr pd env) e1 
        pp_i1 () pp_i2 ()
        (pp_cmd pd asmOp env1) c
        pp_i () pp_i () (if d = UpTo then "+" else "-")
        pp_restore ()

end 

let pp_aux fmt env = 
  let pp ty aux = 
    Format.fprintf fmt "@[var %s:@ %a@];@ " aux (pp_ty env) ty in
  Mty.iter (fun ty -> List.iter (pp ty)) env.auxv

let pp_safe_ret pd env fmt xs =
  if for_safety env then
    let es = List.map (fun x -> Pvar (gkvar x)) xs in
    Leak.pp_safe_cond pd env fmt (Leak.safe_es pd env es)

let pp_fun pd asmOp env fmt f =
  let f = { f with f_body = remove_for f.f_body } in
  let locals = Sv.elements (locals f) in
  (* initialize the env *)
  let env = List.fold_left (add_var false) env f.f_args in
  let env = List.fold_left (add_var (for_safety env)) env locals in  
  (* init auxiliary variables *) 
  let env = 
    if env.model = Normal then Normal.init_aux pd asmOp env f.f_body
    else Leak.init_aux pd asmOp env f.f_body in

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
    (pp_rty env) f.f_tyout
    pp_aux env
    (pp_locals env) locals
    (pp_cmd pd asmOp env) f.f_body
    (pp_safe_ret pd env) f.f_ret
    (pp_ret env) f.f_ret

let pp_glob_decl env fmt (x,d) =
  match d with
  | Global.Gword(ws, w) -> 
    Format.fprintf fmt "@[abbrev %a = %a.of_int %a.@]@ "
      (pp_var env) x pp_Tsz ws pp_print_i (Conv.z_of_word ws w)
  | Global.Garr(p,t) ->
    let wz, t = Conv.to_array x.v_ty p t in
    let pp_elem fmt z = 
      Format.fprintf fmt "%a.of_int %a" pp_Tsz wz pp_print_i z in
    Format.fprintf fmt "@[abbrev %a = %a.of_list witness [%a].@]@ "
       (pp_var env) x (pp_Array env) (Array.length t) 
       (pp_list ";@ " pp_elem) (Array.to_list t)

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

let jmodel () =
  let open Glob_options in
  match !target_arch with
  | X86_64 -> "JModel_x86"
  | ARM_M4 -> "JModel_m4"

let require_lib_slh () =
  let s =
    match !Glob_options.target_arch with
    | X86_64 -> "SLH64"
    | ARM_M4 -> "SLH32"
  in
  Format.sprintf "import %s." s

let pp_prog pd asmOp fmt model globs funcs arrsz warrsz randombytes =

  let env = empty_env model funcs arrsz warrsz randombytes in
  
  let env = 
    List.fold_left (fun env (x, d) -> let env = add_glob_arrsz env (x,d) in add_glob env x)
      env globs in
  let env = List.fold_left add_arrsz env funcs in

  let prefix = !Glob_options.ec_array_path in
  Sint.iter (pp_array_decl ~prefix) !(env.arrsz);
  Sint.iter (pp_warray_decl ~prefix) !(env.warrsz);

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

  let pp_mod_arg fmt env =
    if not (Sint.is_empty !(env.randombytes)) then
      Format.fprintf fmt "(%s:%s)" syscall_mod_arg  syscall_mod_sig in

  let pp_mod_arg_sig fmt env =
    if not (Sint.is_empty !(env.randombytes)) then
      let pp_randombytes_decl fmt n =
        Format.fprintf fmt "proc randombytes_%i(_:W8.t %a.t) : W8.t %a.t" n (pp_Array env) n (pp_Array env) n in
      Format.fprintf fmt "module type %s = {@   @[<v>%a@]@ }.@ @ "
        syscall_mod_sig
        (pp_list "@ " pp_randombytes_decl) (Sint.elements !(env.randombytes));
      let pp_randombytes_proc fmt n =
        Format.fprintf fmt "proc randombytes_%i(a:W8.t %a.t) : W8.t %a.t = {@   a <$ @[dmap %a.darray@ (fun a => %a.init (fun i => %a.get8 a i))@];@   return a;@ }"
          n (pp_Array env) n (pp_Array env) n (pp_WArray env) n 
          (pp_Array env) n (pp_WArray env) n
      in
      Format.fprintf fmt
       "module %s : %s = {@   @[<v>%a@]@ }.@ @ "
       syscall_mod syscall_mod_sig
       (pp_list "@ @ " pp_randombytes_proc) (Sint.elements !(env.randombytes))
  in

  Format.fprintf fmt 
    "@[<v>%s.@ %s %s.@ %s@ @ %s@ %a%a@ %a@ @ %amodule M%a = {@   @[<v>%a%a@]@ }.@ @]@."
    "require import AllCore IntDiv CoreMap List Distr"
    "from Jasmin require import"
    (jmodel ())
    (require_lib_slh ())
    (if env.model = ConstantTime then "from Jasmin require import JLeakage." else "")
    (pp_arrays "Array") !(env.arrsz)
    (pp_arrays "WArray") !(env.warrsz)
    (pp_list "@ @ " (pp_glob_decl env)) globs 
    pp_mod_arg_sig env
    pp_mod_arg env
    pp_leakages env 
    (pp_list "@ @ " (pp_fun pd asmOp env)) funcs
    
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
  (* Do first a dummy printing to collect the Arrayi WArrayi RandomBytes ... *)
  let dummy_fmt = Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ()) in 
  pp_prog pd asmOp dummy_fmt model globs funcs arrsz warrsz randombytes;
  pp_prog pd asmOp       fmt model globs funcs arrsz warrsz randombytes

