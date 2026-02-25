(* ------------------------------------------------------------------------ *)
open Utils
open Wsize
open Operators

(* ------------------------------------------------------------------------ *)

include CoreIdent

(* ------------------------------------------------------------------------ *)

module E = Expr

type 'len gvar_i = 'len gvar L.located

type 'len ggvar = {
  gv : 'len gvar_i;
  gs : E.v_scope;
}

type 'len gexpr =
  | Pconst of Z.t
  | Pbool  of bool
  | Parr_init of wsize * 'len
  | Pvar   of 'len ggvar
  | Pget   of Memory_model.aligned * Warray_.arr_access * wsize * 'len ggvar * 'len gexpr
  | Psub   of Warray_.arr_access * wsize * 'len * 'len ggvar * 'len gexpr
  | Pload  of Memory_model.aligned * wsize * 'len gexpr
  | Papp1  of sop1 * 'len gexpr
  | Papp2  of sop2 * 'len gexpr * 'len gexpr
  | PappN of opN * 'len gexpr list
  | Pif    of 'len gty * 'len gexpr * 'len gexpr * 'len gexpr

type 'len gexprs = 'len gexpr list

let kind_i v = (L.unloc v).v_kind
let ty_i v = (L.unloc v).v_ty

let is_stack_kind k =
  match k with
  | Stack _ -> true
  | _       -> false

let is_reg_kind k =
  match k with
  | Reg _ -> true
  | _     -> false

let reg_kind k =
  match k with
  | Reg (k, _) -> k
  | _     -> assert false

let is_reg_direct_kind k =
  match k with
  | Reg (_, Direct) -> true
  | _ -> false

let is_reg_ptr_kind k =
  match k with
  | Reg (_, Pointer _) -> true
  | _ -> false

let is_stk_ptr_kind k =
  match k with
  | Stack (Pointer _) -> true
  | _ -> false

let is_ptr k =
  match k with
  | Stack k | Reg(_, k) -> k <> Direct
  | _ -> false

let is_regx x =
  match x.v_kind with
  | Reg (Extra, _) -> true
  | _ -> false

(* ------------------------------------------------------------------------ *)

type 'len glval =
 | Lnone of L.t * 'len gty
 | Lvar  of 'len gvar_i
 | Lmem  of Memory_model.aligned * wsize * L.t * 'len gexpr
 | Laset of Memory_model.aligned * Warray_.arr_access * wsize * 'len gvar_i * 'len gexpr
 | Lasub of Warray_.arr_access * wsize * 'len * 'len gvar_i * 'len gexpr
 (* Lasub(acc,sz,len,v,e) is the sub-array of v:
    - [ws/8 * e; ws/8 * e + ws/8 * len[   if acc = Scale
    - [       e;        e + ws/8 * len[   if acc = Direct *)

type 'len glvals = 'len glval list

type 'len grange = E.dir * 'len gexpr * 'len gexpr

type 'len assertion = string * 'len gexpr

type ('len, 'info, 'asm) ginstr_r =
  | Cassgn of 'len glval * E.assgn_tag * 'len gty * 'len gexpr
  (* turn 'asm Sopn.sopn into 'sopn? could be useful to ensure that we remove things statically *)
  | Copn   of 'len glvals * E.assgn_tag * 'asm Sopn.sopn * 'len gexprs
  | Csyscall of 'len glvals * Wsize.wsize Syscall_t.syscall_t * 'len list * 'len gexprs
  | Cassert of 'len assertion
  | Cif    of 'len gexpr * ('len, 'info, 'asm) gstmt * ('len, 'info, 'asm) gstmt
  | Cfor   of 'len gvar_i * 'len grange * ('len, 'info, 'asm) gstmt
  | Cwhile of E.align * ('len, 'info, 'asm) gstmt * 'len gexpr * (IInfo.t * 'info) * ('len, 'info, 'asm) gstmt
  | Ccall  of 'len glvals * funname * 'len list * 'len gexprs

and ('len,'info,'asm) ginstr = {
    i_desc : ('len, 'info, 'asm) ginstr_r;
    i_loc  : L.i_loc;
    i_info : 'info;
    i_annot : Annotations.annotations;
  }

and ('len, 'info, 'asm) gstmt = ('len, 'info, 'asm) ginstr list

(* ------------------------------------------------------------------------ *)
type ('len, 'info, 'asm) gfunc = {
    f_loc  : L.t;
    f_annot: FInfo.f_annot;
    f_info : 'info;
    f_cc   : FInfo.call_conv;
    f_name : funname;
    f_al   : 'len gvar list;
    f_tyin : 'len gty list;
    f_args : 'len gvar list;
    f_body : ('len, 'info, 'asm) gstmt;
    f_tyout : 'len gty list;
    f_ret_info : FInfo.return_info;
    f_ret  : 'len gvar_i list
  }

type 'len ggexpr =
  | GEword of 'len gexpr
  | GEarray of 'len gexprs

type ('len, 'info, 'asm) gmod_item =
  | MIfun   of ('len, 'info, 'asm) gfunc
  | MIparam of ('len gvar * 'len gexpr)
  | MIglobal of ('len gvar * 'len ggexpr)

type ('len, 'info, 'asm) gprog = ('len, 'info, 'asm) gmod_item list
   (* first declaration occur at the end (i.e reverse order) *)

(* ------------------------------------------------------------------------ *)

let gkglob x = { gv = x; gs = E.Sglob}
let gkvar x = { gv = x; gs = E.Slocal}

let is_gkvar x = x.gs = E.Slocal

(* ------------------------------------------------------------------------ *)
(* Parametrized expression *)

type  pty    = pexpr_ gty
and   pvar   = pexpr_ gvar
and   pvar_i = pexpr_ gvar_i
and   plval  = pexpr_ glval
and   plvals = pexpr_ glvals
and   pexpr  = pexpr_ gexpr
and   pexpr_ = PE of pexpr [@@unboxed]


type range = length grange

type epty   = pexpr_ gety

type ('info, 'asm) pinstr_r = (pexpr_, 'info, 'asm) ginstr_r
type ('info, 'asm) pinstr   = (pexpr_, 'info, 'asm) ginstr
type ('info, 'asm) pstmt    = (pexpr_, 'info, 'asm) gstmt

type ('info, 'asm) pfunc     = (pexpr_, 'info, 'asm) gfunc
type ('info, 'asm) pmod_item = (pexpr_, 'info, 'asm) gmod_item
type ('info, 'asm) pprog     = (pexpr_, 'info, 'asm) gprog

(* ------------------------------------------------------------------------ *)
module PV = struct
  type t = pvar
  include GV

  let gequal x1 x2 = equal (L.unloc x1.gv) (L.unloc x2.gv) && (x1.gs = x2.gs)
end

module Mpv : Map.S with type key = pvar = Map.Make (PV)
module Spv = Set.Make  (PV)

(* ------------------------------------------------------------------------ *)

let rec pty_equal t1 t2 =
  match t1, t2 with
  | Bty b1, Bty b2 -> b1 = b2
  | Arr(b1, e1), Arr(b2, e2) ->
    (b1 = b2) && pexpr__equal e1 e2
  | _, _ -> false

and pexpr_equal e1 e2 =
 match e1, e2 with
 | Pconst n1, Pconst n2 -> Z.equal n1 n2
 | Pbool b1, Pbool b2 -> b1 = b2
 | Pvar v1, Pvar v2 -> PV.gequal v1 v2
 | Pget(al1, a1,b1,v1,e1), Pget(al2, a2, b2,v2,e2) -> al1 = al2 && a1 = a2 && b1 = b2 && PV.gequal v1 v2 && pexpr_equal e1 e2
 | Psub(a1,b1,l1,v1,e1), Psub(a2,b2,l2,v2,e2) ->
   a1 = a2 && b1 = b2 && pexpr__equal l1 l2 && PV.gequal v1 v2 && pexpr_equal e1 e2
 | Pload(al1,b1,e1), Pload(al2,b2,e2) -> al1 = al2 && b1 = b2 && pexpr_equal e1 e2
 | Papp1(o1,e1), Papp1(o2,e2) -> o1 = o2 && pexpr_equal e1 e2
 | Papp2(o1,e11,e12), Papp2(o2,e21,e22) -> o1 = o2 &&  pexpr_equal e11 e21 && pexpr_equal e12 e22
 | Pif(_,e11,e12,e13), Pif(_,e21,e22,e23) -> pexpr_equal e11 e21 && pexpr_equal e12 e22 && pexpr_equal e13 e23
 | _, _ -> false

and pexpr__equal (PE e1) (PE e2) = pexpr_equal e1 e2

let epty_equal t1 t2 =
  match t1, t2 with
  | ETbool, ETbool | ETint, ETint -> true
  | ETword(s1,sz1), ETword(s2, sz2) -> s1 = s2 && sz1 = sz2
  | ETarr(b1, e1) , ETarr(b2,e2)    -> b1 = b2 && pexpr__equal e1 e2
  | _, _ -> false

let ws_of_ety = function
  | ETword(_, ws) -> ws
  | _ -> assert false

let rec insert_mono x mono =
  match mono with
  | [] -> [x]
  | y :: mono' ->
      if x <= y then x :: mono
      else y :: insert_mono x mono'

let add_term ((coeff, _) as cm) terms =
  if coeff = 0 then terms else cm :: terms

let rec insert_term ((coeff, mono) as cm) terms =
  match terms with
  | [] -> [cm]
  | ((coeff', mono') as cm') :: terms' ->
    if mono < mono' then cm :: terms
    else if mono = mono' then add_term (coeff + coeff', mono) terms'
    else cm' :: insert_term cm terms'
let insert_term ((coeff, _) as cm) terms =
  if coeff = 0 then terms else insert_term cm terms

let expanded_form len =
  let rec expanded_form terms coeff mono poly =
    match poly with
    | Const n -> let coeff = n * coeff in insert_term (coeff, mono) terms
    | Var x -> let mono = insert_mono x mono in insert_term (coeff, mono) terms
    | Neg e -> expanded_form terms (-coeff) mono e
    | Add (e1, e2) -> expanded_form (expanded_form terms coeff mono e1) coeff mono e2
    | Sub (e1, e2) -> expanded_form (expanded_form terms coeff mono e1) (-coeff) mono e2
    | Mul (Const n, e) -> let coeff = n * coeff in expanded_form terms coeff mono e
    | Mul (Var x, e) -> let mono = insert_mono x mono in expanded_form terms coeff mono e
    | Mul (Neg e1, e2) -> expanded_form terms (-coeff) mono (Mul (e1, e2))
    | Mul (Add (e11, e12), e2) -> expanded_form terms coeff mono (Add (Mul (e11, e2), Mul (e12, e2)))
    | Mul (Sub (e11, e12), e2) -> expanded_form terms coeff mono (Sub (Mul (e11, e2), Mul (e12, e2)))
    | Mul (Mul (e11, e12), e2) -> expanded_form terms coeff mono (Mul (e11, Mul (e12, e2)))
    | Mul ((Div _ | Mod _ | Shl _ | Shr _), _) -> []
    | Div _ | Mod _ | Shl _ | Shr _ -> []
  in
  expanded_form [] 1 [] len

let rec is_poly al =
  match al with
  | Const _ | Var _ -> true
  | Neg al -> is_poly al
  | Add (al1, al2) | Sub (al1, al2) | Mul (al1, al2) -> is_poly al1 && is_poly al2
  | Div _ | Mod _ | Shl _ | Shr _ -> false

let size_of_ws = function
  | U8   -> 1
  | U16  -> 2
  | U32  -> 4
  | U64  -> 8
  | U128 -> 16
  | U256 -> 32

(* FIXME: [=] might be too strict *)
let compare_array_length (ws, al) (ws', al') =
  if is_poly al && is_poly al' then
    let ef = expanded_form (Mul (Const (size_of_ws ws), al)) in
    let ef' = expanded_form (Mul (Const (size_of_ws ws'), al')) in
    ef = ef'
  else
    (ws = ws') && (al = al')

let ety_equal t1 t2 =
  match t1, t2 with
  | ETbool, ETbool | ETint, ETint -> true
  | ETword(s1,sz1), ETword(s2, sz2) -> s1 = s2 && sz1 = sz2
  | ETarr(ws1, len1) , ETarr(ws2, len2)    -> compare_array_length (ws1, len1) (ws2, len2)
  | _, _ -> false

let rec al_of_expr e =
  match e with
  | Pconst n ->
    (* FIXME: change Const to Z and remove this error *)
      begin try Const (Z.to_int n)
      with Z.Overflow ->
        hierror ~loc:Lnone ~kind:"compilation error" ~sub_kind:"param expansion" "number too big"
      end
  | Pvar x -> assert (is_gkvar x); Var (L.unloc x.gv)
  | Papp1 (Oneg Op_int, e) ->
      Neg (al_of_expr e)
  | Papp2 (Oadd Op_int, e1, e2) ->
      Add (al_of_expr e1, al_of_expr e2)
  | Papp2 (Osub Op_int, e1, e2) ->
      Sub (al_of_expr e1, al_of_expr e2)
  | Papp2 (Omul Op_int, e1, e2) ->
      Mul (al_of_expr e1, al_of_expr e2)
  | Papp2 (Odiv (sg, Op_int), e1, e2) ->
      Div (sg, al_of_expr e1, al_of_expr e2)
  | Papp2 (Omod (sg, Op_int), e1, e2) ->
      Mod (sg, al_of_expr e1, al_of_expr e2)
  | Papp2 (Olsl Op_int, e1, e2) ->
      Shl (al_of_expr e1, al_of_expr e2)
  | Papp2 (Oasr Op_int, e1, e2) ->
      Shr (al_of_expr e1, al_of_expr e2)
  | _ ->
    (* FIXME: better error message *)
    hierror ~loc:Lnone ~kind:"compilation error" ~sub_kind:"param expansion" "operations too complex"

let rec expr_of_al al =
  match al with
  | Const n -> Pconst (Z.of_int n)
  | Var x -> Pvar (gkvar (L.mk_loc L._dummy x))
  | Neg al -> Papp1 (Oneg Op_int, expr_of_al al)
  | Add (al1, al2) -> Papp2 (Oadd Op_int, expr_of_al al1, expr_of_al al2)
  | Sub (al1, al2) -> Papp2 (Osub Op_int, expr_of_al al1, expr_of_al al2)
  | Mul (al1, al2) -> Papp2 (Omul Op_int, expr_of_al al1, expr_of_al al2)
  | Div (sg, al1, al2) -> Papp2 (Odiv (sg, Op_int), expr_of_al al1, expr_of_al al2)
  | Mod (sg, al1, al2) -> Papp2 (Omod (sg, Op_int), expr_of_al al1, expr_of_al al2)
  | Shl (al1, al2) -> Papp2 (Olsl Op_int, expr_of_al al1, expr_of_al al2)
  | Shr (al1, al2) -> Papp2 (Oasr Op_int, expr_of_al al1, expr_of_al al2)

(* ------------------------------------------------------------------------ *)
(* Non parametrized expression                                              *)

type ty    = length gty
type var   = length gvar
type var_i = length gvar_i
type lval  = length glval
type lvals = length glval list
type expr  = length gexpr
type exprs = length gexpr list

type ety   = length gety

type ('info, 'asm) instr = (length, 'info, 'asm) ginstr
type ('info, 'asm) instr_r = (length,'info,'asm) ginstr_r
type ('info, 'asm) stmt  = (length, 'info, 'asm) gstmt

type ('info, 'asm) func     = (length, 'info, 'asm) gfunc
type ('info, 'asm) mod_item = (length, 'info, 'asm) gmod_item
type global_decl           = var * Global.glob_value
type ('info,'asm) prog     = global_decl list * ('info, 'asm) func list

module Sv = Set.Make  (V)
module Mv = Map.Make  (V)
module Hv = Hash.Make (V)

let var_of_ident (x: CoreIdent.var) : var = x
let ident_of_var (x:var) : CoreIdent.var = x

(* -------------------------------------------------------------------- *)
(* used variables                                                       *)

let rec rvars_al f s al =
  match al with
  | Const _ -> s
  | Var x -> f x s
  | Neg al -> rvars_al f s al
  | Add (al1, al2) | Sub (al1, al2) | Mul (al1, al2) | Div (_, al1, al2) | Mod (_, al1, al2) | Shl (al1, al2) | Shr (al1, al2)  -> rvars_al f (rvars_al f s al1) al2

let rvars_v f x s =
  if is_gkvar x then f (L.unloc x.gv) s
  else s

let rec rvars_e f s = function
  | Pconst _ | Pbool _ | Parr_init _ -> s
  | Pvar x         -> rvars_v f x s
  | Pget(_,_,_,x,e) | Psub (_, _, _, x, e) -> rvars_e f (rvars_v f x s) e
  | Pload(_,_,e)
  | Papp1(_, e)    -> rvars_e f s e
  | Papp2(_,e1,e2) -> rvars_e f (rvars_e f s e1) e2
  | PappN (_, es) -> rvars_es f s es
  | Pif(_,e,e1,e2)   -> rvars_e f (rvars_e f (rvars_e f s e) e1) e2

and rvars_es f s es = List.fold_left (rvars_e f) s es

let rvars_lv f s = function
 | Lnone _       -> s
 | Lvar x        -> f (L.unloc x) s
 | Lmem (_,_,_ ,e) -> rvars_e f s e
 | Laset (_,_,_,x,e)
 | Lasub (_,_,_,x,e) -> rvars_e f (f (L.unloc x) s) e

let rvars_lvs f s lvs = List.fold_left (rvars_lv f) s lvs

let rec rvars_i f s i =
  match i.i_desc with
  | Cassgn(x, _, _, e)  -> rvars_e f (rvars_lv f s x) e
  | Copn(x,_,_,e)  | Csyscall (x, _, _, e) -> rvars_es f (rvars_lvs f s x) e
  | Cassert(_, e) -> rvars_e f s e
  | Cif(e,c1,c2)   -> rvars_c f (rvars_c f (rvars_e f s e) c1) c2
  | Cfor(x,(_,e1,e2), c) ->
    rvars_c f (rvars_e f (rvars_e f (f (L.unloc x) s) e1) e2) c
  | Cwhile(_, c, e, _, c') -> rvars_c f (rvars_e f (rvars_c f s c') e) c
  | Ccall(x,_,_,e) -> rvars_es f (rvars_lvs f s x) e

and rvars_c f s c =  List.fold_left (rvars_i f) s c

let fold_vars_ret f init fd =
  List.fold_left (fun a x -> f (L.unloc x) a) init fd.f_ret

let fold_vars_fc f z fc =
  let a = fold_vars_ret f z fc in
  rvars_c f a fc.f_body

let vars_al al = rvars_al Sv.add Sv.empty al
let vars_ret fd = fold_vars_ret Sv.add Sv.empty fd
let vars_lv z x = rvars_lv Sv.add z x
let vars_e e = rvars_e Sv.add Sv.empty e
let pvars_e e = rvars_e Spv.add Spv.empty e
let vars_es es = rvars_es Sv.add Sv.empty es
let vars_i i = rvars_i Sv.add Sv.empty i
let vars_c c = rvars_c Sv.add Sv.empty c
let pvars_c c = rvars_c Spv.add Spv.empty c

let params fc =
  List.fold_left (fun s v -> Sv.add v s) Sv.empty fc.f_args

let vars_fc fc =
  let s = params fc in
  let s = List.fold_left (fun s v -> Sv.add (L.unloc v) s) s fc.f_ret in
  rvars_c Sv.add s fc.f_body

let locals fc =
  let s1 = params fc in
  Sv.diff (vars_fc fc) s1

let written_lv s =
  function
  | Lvar x
  | Laset (_, _, _, x, _)
  | Lasub (_, _, _, x, _)
    -> Sv.add (L.unloc x) s
  | _ -> s

let rec written_vars_i ((v, f) as acc) i =
  match i.i_desc with
  | Cassgn(x, _, _, _) -> written_lv v x, f
  | Copn(xs, _, _, _) | Csyscall(xs, _, _, _)
    -> List.fold_left written_lv v xs, f
  | Ccall(xs, fn, _, _) ->
     List.fold_left written_lv v xs, Mf.modify_def [] fn (fun old -> i.i_loc :: old) f
  | Cassert (_, _) -> v, f
  | Cif(_, s1, s2)
  | Cwhile(_, s1, _, _, s2)
    -> written_vars_stmt (written_vars_stmt acc s1) s2
  | Cfor(_, _, s) -> written_vars_stmt acc s
and written_vars_stmt acc s =
  List.fold_left written_vars_i acc s

let written_vars_fc fc =
  written_vars_stmt (Sv.empty, Mf.empty) fc.f_body

(* -------------------------------------------------------------------- *)
(* Refresh i_loc, ensure that locations are uniq                        *)

let rec refresh_i_loc_i (i:('info, 'asm) instr) : ('info, 'asm) instr =
  let i_desc =
    match i.i_desc with
    | Cassgn _ | Copn _ | Csyscall _ | Ccall _ | Cassert _ -> i.i_desc
    | Cif(e, c1, c2) ->
        Cif(e, refresh_i_loc_c c1, refresh_i_loc_c c2)
    | Cfor(x, r, c) ->
        Cfor(x, r, refresh_i_loc_c c)
    | Cwhile(a, c1, e, ((loc, annot), info), c2) ->
        Cwhile(a, refresh_i_loc_c c1, e, ((L.refresh_i_loc loc, annot), info), refresh_i_loc_c c2)
  in
  { i with i_desc; i_loc = L.refresh_i_loc i.i_loc }

and refresh_i_loc_c (c:('info, 'asm) stmt) : ('info, 'asm) stmt =
  List.map refresh_i_loc_i c

let refresh_i_loc_f (f:('info, 'asm) func) : ('info, 'asm) func =
  { f with f_body = refresh_i_loc_c f.f_body }

let refresh_i_loc_p (p:('info, 'asm) prog) : ('info, 'asm) prog =
  fst p, List.map refresh_i_loc_f (snd p)


(* -------------------------------------------------------------------- *)
(* Functions on types                                                   *)

let int_of_ws = Annotations.int_of_ws

let string_of_ws = Annotations.string_of_ws

let wsize_lt ws1 ws2 = Wsize.wsize_cmp ws1 ws2 = Datatypes.Lt
let wsize_le ws1 ws2 = Wsize.wsize_cmp ws1 ws2 <> Datatypes.Gt

let int_of_pe =
  function
  | PE1   -> 1
  | PE2   -> 2
  | PE4   -> 4
  | PE8   -> 8
  | PE16  -> 16
  | PE32  -> 32
  | PE64  -> 64
  | PE128 -> 128


let int_of_velem ve = int_of_ws (wsize_of_velem ve)

let is_ty_arr = function
  | Arr _ -> true
  | _     -> false

let array_kind = function
  | Arr(ws, n) -> ws, n
  | _ -> assert false

let array_kind_const = function
  | Arr (ws, Const n) -> ws, n
  | _ -> assert false

let ws_of_ty = function
  | Bty (U ws) -> ws
  | _ -> assert false

let arr_size ws i = size_of_ws ws * i

let size_of t =
  match t with
  | Bty (U ws) -> Const (size_of_ws ws)
  | Arr (ws, len) ->
      begin match len with
      | Const n -> Const (arr_size ws n)
      | _ -> Mul (Const (size_of_ws ws), len)
      end
  | _ -> assert false

let size_of_const t =
  match t with
  | Bty (U ws) -> size_of_ws ws
  | Arr (ws', Const n) -> arr_size ws' n
  | _ -> assert false

(* -------------------------------------------------------------------- *)
(* Functions over variables                                             *)

let is_stack_var v =
  is_stack_kind v.v_kind

let is_reg_arr v =
  is_reg_direct_kind v.v_kind && is_ty_arr v.v_ty

let is_stack_array x =
  let x = L.unloc x in
  is_ty_arr x.v_ty && x.v_kind = Stack Direct

(* -------------------------------------------------------------------- *)
(* Functions over expressions                                           *)

let ( ++ ) e1 e2 =
  match e1, e2 with
  | Pconst n1, Pconst n2 -> Pconst (Z.add n1 n2)
  | _, _                 -> Papp2(Oadd Op_int, e1, e2)

let ( ** ) e1 e2 =
  match e1, e2 with
  | Pconst n1, Pconst n2 -> Pconst (Z.mul n1 n2)
  | _, _                 -> Papp2(Omul Op_int, e1, e2)

let cnst i = Pconst i
let icnst i = cnst (Z.of_int i)

let is_var = function
  | Pvar _ -> true
  | _ -> false

let access_offset aa ws i =
  match aa with
  | Warray_.AAscale -> size_of_ws ws * i
  | Warray_.AAdirect -> i

let get_ofs aa ws e =
  match e with
  | Pconst i -> Some (access_offset aa ws (Z.to_int i))
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Functions over lvalue                                                *)

let expr_of_lval = function
  | Lnone _         -> None
  | Lvar x          -> Some (Pvar (gkvar x))
  | Lmem (al, ws, _, e) -> Some (Pload(al,ws,e))
  | Laset(al, a, ws, x, e) -> Some (Pget(al, a,ws,gkvar x,e))
  | Lasub(a, ws, l, x, e) -> Some (Psub(a,ws,l,gkvar x, e))

(* -------------------------------------------------------------------- *)
(* Functions over instruction                                           *)

let rec has_syscall_i i =
  match i.i_desc with
  | Csyscall _ -> true
  | Cassgn _ | Copn _ | Ccall _ | Cassert _ -> false
  | Cif (_, c1, c2) | Cwhile(_, c1, _, _, c2) -> has_syscall c1 || has_syscall c2
  | Cfor (_, _, c) -> has_syscall c

and has_syscall c = List.exists has_syscall_i c

let rec has_call_or_syscall_i i =
  match i.i_desc with
  | Csyscall _ | Ccall _ -> true
  | Cassgn _ | Copn _ | Cassert _ -> false
  | Cif (_, c1, c2) | Cwhile(_, c1, _, _, c2) -> has_call_or_syscall c1 || has_call_or_syscall c2
  | Cfor (_, _, c) -> has_call_or_syscall c

and has_call_or_syscall c = List.exists has_call_or_syscall_i c

let has_annot a { i_annot; _ } = Annotations.has_symbol a i_annot

let is_inline annot cc =
  Annotations.has_symbol "inline" annot || cc = FInfo.Internal

let rec spilled_i s i =
  match i.i_desc with
  | Copn(_, _, Sopn.Opseudo_op (Pseudo_operator.Ospill _), es) -> rvars_es Sv.add s es
  | Cassgn _ | Csyscall _ | Ccall _ | Copn _ | Cassert _ -> s
  | Cif(_e, c1, c2)  -> spilled_c (spilled_c s c1) c2
  | Cfor(_, _, c)    -> spilled_c s c
  | Cwhile(_, c, _, _, c') -> spilled_c (spilled_c s c) c'

and spilled_c s c =  List.fold_left spilled_i s c

let spilled fc = spilled_c Sv.empty fc.f_body

let assigns = function
  | Cassgn (x, _, _, _) -> written_lv Sv.empty x
  | Copn (xs, _, _, _) | Csyscall (xs, _, _, _) | Ccall (xs, _, _, _) ->
      List.fold_left written_lv Sv.empty xs
  | Cif _ | Cwhile _ | Cassert _ | Cfor _ -> Sv.empty

let is_lmem = function
  | Lmem _ -> true
  | _ -> false

let has_effect = function
  | Csyscall _ | Ccall _ -> true
  | Cassgn (x, _, _, _) -> is_lmem x
  | Copn (xs, _, _, _) -> List.exists is_lmem xs
  | Cassert _ | Cif _ | Cwhile _ | Cfor _ -> false

(* -------------------------------------------------------------------- *)
let rec iter_instr f stmt = List.iter (iter_instr_i f) stmt

and iter_instr_i f gi =
  f gi;
  iter_instr_ir f gi.i_desc

and iter_instr_ir f = function
  | Cassgn _ | Copn _ | Csyscall _ | Ccall _ | Cassert _ -> ()
  | Cfor (_, _, c) -> iter_instr f c
  | Cif (_, c1, c2) | Cwhile (_, c1, _, _, c2) ->
     iter_instr f c1;
     iter_instr f c2

(* -------------------------------------------------------------------- *)
let clamp (sz : wsize) (z : Z.t) =
  Z.erem z (Z.shift_left Z.one (int_of_ws sz))

(* --------------------------------------------------------------------- *)
type ('info,'asm) sfundef = Expr.stk_fun_extra * ('info, 'asm) func
type ('info,'asm) sprog   = ('info, 'asm) sfundef list * Expr.sprog_extra
