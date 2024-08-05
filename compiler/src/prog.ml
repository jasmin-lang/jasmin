(* ------------------------------------------------------------------------ *)
open Utils
open Wsize

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
  | Parr_init of 'len
  | Pvar   of 'len ggvar
  | Pget   of Memory_model.aligned * Warray_.arr_access * wsize * 'len ggvar * 'len gexpr
  | Psub   of Warray_.arr_access * wsize * 'len * 'len ggvar * 'len gexpr
  | Pload  of Memory_model.aligned * wsize * 'len gvar_i * 'len gexpr
  | Papp1  of E.sop1 * 'len gexpr
  | Papp2  of E.sop2 * 'len gexpr * 'len gexpr
  | PappN of E.opN * 'len gexpr list
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
 | Lmem  of Memory_model.aligned * wsize * 'len gvar_i * 'len gexpr
 | Laset of Memory_model.aligned * Warray_.arr_access * wsize * 'len gvar_i * 'len gexpr
 | Lasub of Warray_.arr_access * wsize * 'len * 'len gvar_i * 'len gexpr
 (* Lasub(acc,sz,len,v,e) is the sub-array of v:
    - [ws/8 * e; ws/8 * e + ws/8 * len[   if acc = Scale
    - [       e;        e + ws/8 * len[   if acc = Direct *)

type 'len glvals = 'len glval list

type 'len grange = E.dir * 'len gexpr * 'len gexpr

type ('len,'info,'asm) ginstr_r =
  | Cassgn of 'len glval * E.assgn_tag * 'len gty * 'len gexpr
  (* turn 'asm Sopn.sopn into 'sopn? could be useful to ensure that we remove things statically *)
  | Copn   of 'len glvals * E.assgn_tag * 'asm Sopn.sopn * 'len gexprs
  | Csyscall of 'len glvals * BinNums.positive Syscall_t.syscall_t * 'len gexprs
  | Cif    of 'len gexpr * ('len,'info,'asm) gstmt * ('len,'info,'asm) gstmt
  | Cfor   of 'len gvar_i * 'len grange * ('len,'info,'asm) gstmt
  | Cwhile of E.align * ('len,'info,'asm) gstmt * 'len gexpr * ('len,'info,'asm) gstmt
  | Ccall  of 'len glvals * funname * 'len gexprs

and ('len,'info,'asm) ginstr = {
    i_desc : ('len,'info,'asm) ginstr_r;
    i_loc  : L.i_loc;
    i_info : 'info;
    i_annot : Annotations.annotations;
  }

and ('len,'info,'asm) gstmt = ('len,'info,'asm) ginstr list

(* ------------------------------------------------------------------------ *)
type ('len,'info,'asm) gfunc = {
    f_loc  : L.t;
    f_annot: FInfo.f_annot;
    f_cc   : FInfo.call_conv;
    f_name : funname;
    f_tyin : 'len gty list;
    f_args : 'len gvar list;
    f_body : ('len,'info,'asm) gstmt;
    f_tyout : 'len gty list;
    f_outannot : Annotations.annotations list; (* annotation attach to return type *)
    f_ret  : 'len gvar_i list
  }

type 'len ggexpr =
  | GEword of 'len gexpr
  | GEarray of 'len gexprs

type ('len,'info,'asm) gmod_item =
  | MIfun   of ('len,'info,'asm) gfunc
  | MIparam of ('len gvar * 'len gexpr)
  | MIglobal of ('len gvar * 'len ggexpr)

type ('len,'info,'asm) gprog = ('len,'info,'asm) gmod_item list
   (* first declaration occur at the end (i.e reverse order) *)

(* ------------------------------------------------------------------------ *)

let gkglob x = { gv = x; gs = E.Sglob}
let gkvar x = { gv = x; gs = E.Slocal}

let is_gkvar x = x.gs = E.Slocal

(* ------------------------------------------------------------------------ *)
(* Parametrized expression *)

type pty    = pexpr gty
and  pvar   = pexpr gvar
and  pvar_i = pexpr gvar_i
and  plval  = pexpr glval
and  plvals = pexpr glvals
and  pexpr  = pexpr gexpr

type ('info,'asm) pinstr = (pexpr,'info,'asm) ginstr
type ('info,'asm) pstmt  = (pexpr,'info,'asm) gstmt

type ('info,'asm) pfunc     = (pexpr,'info,'asm) gfunc
type ('info,'asm) pmod_item = (pexpr,'info,'asm) gmod_item
type ('info,'asm) pprog     = (pexpr,'info,'asm) gprog

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
    (b1 = b2) && pexpr_equal e1 e2
  | _, _ -> false

and pexpr_equal e1 e2 =
 match e1, e2 with
 | Pconst n1, Pconst n2 -> Z.equal n1 n2
 | Pbool b1, Pbool b2 -> b1 = b2
 | Pvar v1, Pvar v2 -> PV.gequal v1 v2
 | Pget(al1, a1,b1,v1,e1), Pget(al2, a2, b2,v2,e2) -> al1 = al2 && a1 = a2 && b1 = b2 && PV.gequal v1 v2 && pexpr_equal e1 e2
 | Psub(a1,b1,l1,v1,e1), Psub(a2,b2,l2,v2,e2) ->
   a1 = a2 && b1 = b2 && pexpr_equal l1 l2 && PV.gequal v1 v2 && pexpr_equal e1 e2
 | Pload(al1, b1,v1,e1), Pload(al2, b2,v2,e2) -> al1 = al2 &&b1 = b2 && PV.equal (L.unloc v1) (L.unloc v2) && pexpr_equal e1 e2
 | Papp1(o1,e1), Papp1(o2,e2) -> o1 = o2 && pexpr_equal e1 e2
 | Papp2(o1,e11,e12), Papp2(o2,e21,e22) -> o1 = o2 &&  pexpr_equal e11 e21 && pexpr_equal e12 e22
 | Pif(_,e11,e12,e13), Pif(_,e21,e22,e23) -> pexpr_equal e11 e21 && pexpr_equal e12 e22 && pexpr_equal e13 e23
 | _, _ -> false

(* ------------------------------------------------------------------------ *)
(* Non parametrized expression                                              *)

type ty    = int gty
type var   = int gvar
type var_i = int gvar_i
type lval  = int glval
type lvals = int glval list
type expr  = int gexpr
type exprs = int gexpr list

type ('info,'asm) instr = (int,'info,'asm) ginstr
type ('info,'asm) stmt  = (int,'info,'asm) gstmt

type ('info,'asm) func     = (int,'info,'asm) gfunc
type ('info,'asm) mod_item = (int,'info,'asm) gmod_item
type global_decl           = var * Global.glob_value
type ('info,'asm) prog     = global_decl list * ('info,'asm) func list

module Sv = Set.Make  (V)
module Mv = Map.Make  (V)
module Hv = Hash.Make (V)

let var_of_ident (x: CoreIdent.var) : var = x
let ident_of_var (x:var) : CoreIdent.var = x

(* -------------------------------------------------------------------- *)
(* used variables                                                       *)

let rvars_v f x s =
  if is_gkvar x then f (L.unloc x.gv) s
  else s

let rec rvars_e f s = function
  | Pconst _ | Pbool _ | Parr_init _ -> s
  | Pvar x         -> rvars_v f x s
  | Pget(_,_,_,x,e) | Psub (_, _, _, x, e) -> rvars_e f (rvars_v f x s) e
  | Pload(_,_,x,e)   -> rvars_e f (f (L.unloc x) s) e
  | Papp1(_, e)    -> rvars_e f s e
  | Papp2(_,e1,e2) -> rvars_e f (rvars_e f s e1) e2
  | PappN (_, es) -> rvars_es f s es
  | Pif(_,e,e1,e2)   -> rvars_e f (rvars_e f (rvars_e f s e) e1) e2

and rvars_es f s es = List.fold_left (rvars_e f) s es

let rvars_lv f s = function
 | Lnone _       -> s
 | Lvar x        -> f (L.unloc x) s
 | Lmem (_,_,x,e)
 | Laset (_,_,_,x,e)
 | Lasub (_,_,_,x,e) -> rvars_e f (f (L.unloc x) s) e

let rvars_lvs f s lvs = List.fold_left (rvars_lv f) s lvs

let rec rvars_i f s i =
  match i.i_desc with
  | Cassgn(x, _, _, e)  -> rvars_e f (rvars_lv f s x) e
  | Copn(x,_,_,e)  | Csyscall (x, _, e) -> rvars_es f (rvars_lvs f s x) e
  | Cif(e,c1,c2)   -> rvars_c f (rvars_c f (rvars_e f s e) c1) c2
  | Cfor(x,(_,e1,e2), c) ->
    rvars_c f (rvars_e f (rvars_e f (f (L.unloc x) s) e1) e2) c
  | Cwhile(_,c,e,c')    -> rvars_c f (rvars_e f (rvars_c f s c') e) c
  | Ccall(x,_,e) -> rvars_es f (rvars_lvs f s x) e

and rvars_c f s c =  List.fold_left (rvars_i f) s c

let fold_vars_fc f z fc =
  let a  = List.fold_left (fun a x -> f (L.unloc x) a) z fc.f_ret in
  rvars_c f a fc.f_body

let vars_lv z x = rvars_lv Sv.add z x
let vars_e e = rvars_e Sv.add Sv.empty e
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
  let s2 = Sv.diff (vars_fc fc) s1 in
  Sv.filter V.is_local s2

let written_lv s =
  function
  | Lvar x -> Sv.add (L.unloc x) s
  | _ -> s

let rec written_vars_i ((v, f) as acc) i =
  match i.i_desc with
  | Cassgn(x, _, _, _) -> written_lv v x, f
  | Copn(xs, _, _, _) | Csyscall(xs, _, _)
    -> List.fold_left written_lv v xs, f
  | Ccall(xs, fn, _) ->
     List.fold_left written_lv v xs, Mf.modify_def [] fn (fun old -> i.i_loc :: old) f
  | Cif(_, s1, s2)
  | Cwhile(_, s1, _, s2)
    -> written_vars_stmt (written_vars_stmt acc s1) s2
  | Cfor(_, _, s) -> written_vars_stmt acc s
and written_vars_stmt acc s =
  List.fold_left written_vars_i acc s

let written_vars_fc fc =
  written_vars_stmt (Sv.empty, Mf.empty) fc.f_body

(* -------------------------------------------------------------------- *)
(* Refresh i_loc, ensure that locations are uniq                        *)

let rec refresh_i_loc_i (i:('info,'asm) instr) : ('info,'asm) instr =
  let i_desc =
    match i.i_desc with
    | Cassgn _ | Copn _ | Csyscall _ | Ccall _ -> i.i_desc
    | Cif(e, c1, c2) ->
        Cif(e, refresh_i_loc_c c1, refresh_i_loc_c c2)
    | Cfor(x, r, c) ->
        Cfor(x, r, refresh_i_loc_c c)
    | Cwhile(a, c1, e, c2) ->
        Cwhile(a, refresh_i_loc_c c1, e, refresh_i_loc_c c2)
  in
  { i with i_desc; i_loc = L.refresh_i_loc i.i_loc }

and refresh_i_loc_c (c:('info,'asm) stmt) : ('info,'asm) stmt =
  List.map refresh_i_loc_i c

let refresh_i_loc_f (f:('info,'asm) func) : ('info,'asm) func =
  { f with f_body = refresh_i_loc_c f.f_body }

let refresh_i_loc_p (p:('info,'asm) prog) : ('info,'asm) prog =
  fst p, List.map refresh_i_loc_f (snd p)


(* -------------------------------------------------------------------- *)
(* Functions on types                                                   *)

let int_of_ws = Annotations.int_of_ws

let size_of_ws = function
  | U8   -> 1
  | U16  -> 2
  | U32  -> 4
  | U64  -> 8
  | U128 -> 16
  | U256 -> 32

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

let ws_of_ty = function
  | Bty (U ws) -> ws
  | _ -> assert false

let arr_size ws i = size_of_ws ws * i

let size_of t =
  match t with
  | Bty (U ws) -> size_of_ws ws
  | Arr (ws', n) -> arr_size ws' n
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
  | Lmem (al, ws, x, e) -> Some (Pload(al,ws,x,e))
  | Laset(al, a, ws, x, e) -> Some (Pget(al, a,ws,gkvar x,e))
  | Lasub(a, ws, l, x, e) -> Some (Psub(a,ws,l,gkvar x, e))

(* -------------------------------------------------------------------- *)
(* Functions over instruction                                           *)

let rec has_syscall_i i =
  match i.i_desc with
  | Csyscall _ -> true
  | Cassgn _ | Copn _ | Ccall _ -> false
  | Cif (_, c1, c2) | Cwhile(_, c1, _, c2) -> has_syscall c1 || has_syscall c2
  | Cfor (_, _, c) -> has_syscall c

and has_syscall c = List.exists has_syscall_i c

let rec has_call_or_syscall_i i =
  match i.i_desc with
  | Csyscall _ | Ccall _ -> true
  | Cassgn _ | Copn _ -> false
  | Cif (_, c1, c2) | Cwhile(_, c1, _, c2) -> has_call_or_syscall c1 || has_call_or_syscall c2
  | Cfor (_, _, c) -> has_call_or_syscall c

and has_call_or_syscall c = List.exists has_call_or_syscall_i c

let has_annot a { i_annot; _ } = Annotations.has_symbol a i_annot

let is_inline annot cc =
  Annotations.has_symbol "inline" annot || cc = FInfo.Internal

let rec spilled_i s i =
  match i.i_desc with
  | Copn(_, _, Sopn.Opseudo_op (Pseudo_operator.Ospill _), es) -> rvars_es Sv.add s es
  | Cassgn _ | Csyscall _ | Ccall _ | Copn _-> s
  | Cif(e,c1,c2)     -> spilled_c (spilled_c s c1) c2
  | Cfor(_, _, c)    -> spilled_c s c
  | Cwhile(_,c,_,c') -> spilled_c (spilled_c s c) c'

and spilled_c s c =  List.fold_left spilled_i s c

let spilled fc = spilled_c Sv.empty fc.f_body

(* -------------------------------------------------------------------- *)
let clamp (sz : wsize) (z : Z.t) =
  Z.erem z (Z.shift_left Z.one (int_of_ws sz))

let clamp_pe (sz : pelem) (z : Z.t) =
  Z.erem z (Z.shift_left Z.one (int_of_pe sz))


(* --------------------------------------------------------------------- *)
type ('info,'asm) sfundef = Expr.stk_fun_extra * ('info,'asm) func
type ('info,'asm) sprog   = ('info,'asm) sfundef list * Expr.sprog_extra
