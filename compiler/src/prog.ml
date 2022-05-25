(* ------------------------------------------------------------------------ *)
open Utils
open Wsize
module E = Expr
module L = Location

module Name = struct
  type t = string
  let equal (n1:t) (n2:t) = n1 = n2
end

type uid = int

let int_of_uid i = i

(* ------------------------------------------------------------------------ *)
type base_ty =
  | Bool
  | Int              (* Unbounded integer for pexpr *)
  | U   of wsize (* U(n): unsigned n-bit integer *)
  [@@deriving compare,sexp]

type writable = Constant | Writable
type pointer = Direct | Pointer of writable

type reg_kind = Normal | Extra

type v_kind =
  | Const            (* global parameter  *)
  | Stack of pointer (* stack variable    *)
  | Reg   of reg_kind * pointer (* register variable *)
  | Inline           (* inline variable   *)
  | Global           (* global (in memory) constant *)

type 'len gty =
  | Bty of base_ty
  | Arr of wsize * 'len (* Arr(n,de): array of n-bit integers with dim. *)
           (* invariant only Const variable can be used in expression *)
           (* the type of the expression is [Int] *)

type 'len gvar = {
  v_name : Name.t;
  v_id   : uid;
  v_kind : v_kind;
  v_ty   : 'len gty;
  v_dloc : L.t;   (* location where declared *)
  v_annot : Syntax.annotations;
}

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
  | Pget   of Warray_.arr_access * wsize * 'len ggvar * 'len gexpr
  | Psub   of Warray_.arr_access * wsize * 'len * 'len ggvar * 'len gexpr
  | Pload  of wsize * 'len gvar_i * 'len gexpr
  | Papp1  of E.sop1 * 'len gexpr
  | Papp2  of E.sop2 * 'len gexpr * 'len gexpr
  | PappN of E.opN * 'len gexpr list
  | Pif    of 'len gty * 'len gexpr * 'len gexpr * 'len gexpr

type 'len gexprs = 'len gexpr list

let u8   = Bty (U U8)
let u16  = Bty (U U16)
let u32  = Bty (U U32)
let u64  = Bty (U U64)
let u128 = Bty (U U128)
let u256 = Bty (U U256)
let tu ws = Bty (U ws)
let tbool = Bty Bool
let tint  = Bty Int

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
 | Lmem  of wsize * 'len gvar_i * 'len gexpr
 | Laset of Warray_.arr_access * wsize * 'len gvar_i * 'len gexpr
 | Lasub of Warray_.arr_access * wsize * 'len * 'len gvar_i * 'len gexpr
 (* Lasub(acc,sz,len,v,e) is the sub-array of v:
    - [ws/8 * e; ws/8 * e + ws/8 * len[   if acc = Scale
    - [       e;        e + ws/8 * len[   if acc = Direct *)

type 'len glvals = 'len glval list

type funname = {
    fn_name : Name.t;
    fn_id   : uid;
  }

type 'len grange = E.dir * 'len gexpr * 'len gexpr

type ('len,'info) ginstr_r =
  | Cassgn of 'len glval * E.assgn_tag * 'len gty * 'len gexpr
  | Copn   of 'len glvals * E.assgn_tag * X86_extra.x86_extended_op Sopn.sopn * 'len gexprs
  | Csyscall of 'len glvals * Syscall.syscall_t * 'len gexprs
  | Cif    of 'len gexpr * ('len,'info) gstmt * ('len,'info) gstmt
  | Cfor   of 'len gvar_i * 'len grange * ('len,'info) gstmt
  | Cwhile of E.align * ('len,'info) gstmt * 'len gexpr * ('len,'info) gstmt
  | Ccall  of E.inline_info * 'len glvals * funname * 'len gexprs

and ('len,'info) ginstr = {
    i_desc : ('len,'info) ginstr_r;
    i_loc  : L.i_loc;
    i_info : 'info;
    i_annot : Syntax.annotations;
  }

and ('len,'info) gstmt = ('len,'info) ginstr list

(* ------------------------------------------------------------------------ *)
type subroutine_info = {
    returned_params : int option list;
  }

type call_conv =
  | Export                 (* The function should be exported to the outside word *)
  | Subroutine of subroutine_info (* internal function that should not be inlined *)
  | Internal                   (* internal function that should be inlined *)

type returnaddress_kind =
  | OnStack
  | OnReg

type f_annot = {
    retaddr_kind  : returnaddress_kind option;
    stack_allocation_size : Z.t option;
    stack_size    : Z.t option;
    stack_align   : wsize option;
  }

let f_annot_empty = {
    retaddr_kind  = None;
    stack_allocation_size = None;
    stack_size    = None;
    stack_align   = None;
  }

type ('len,'info) gfunc = {
    f_loc  : L.t;
    f_annot : f_annot;
    f_user_annot : Syntax.annotations;
    f_cc   : call_conv;
    f_name : funname;
    f_tyin : 'len gty list;
    f_args : 'len gvar list;
    f_body : ('len,'info) gstmt;
    f_tyout : 'len gty list;
    f_outannot : Syntax.annotations list; (* annotation attach to return type *)
    f_ret  : 'len gvar_i list
  }

type 'len ggexpr =
  | GEword of 'len gexpr
  | GEarray of 'len gexprs

type ('len,'info) gmod_item =
  | MIfun   of ('len,'info) gfunc
  | MIparam of ('len gvar * 'len gexpr)
  | MIglobal of ('len gvar * 'len ggexpr)

type ('len,'info) gprog = ('len,'info) gmod_item list
   (* first declaration occur at the end (i.e reverse order) *)

(* ------------------------------------------------------------------------ *)
module GV = struct
  let mk v_name v_kind v_ty v_dloc v_annot =
    let v_id = Uniq.gen () in
    { v_name; v_id; v_kind; v_ty; v_dloc; v_annot }

  let clone v = mk v.v_name v.v_kind v.v_ty v.v_dloc v.v_annot

  let compare v1 v2 = v1.v_id - v2.v_id

  let equal v1 v2 = v1.v_id = v2.v_id

  let hash v = v.v_id

  let is_glob v = v.v_kind = Const

  let is_local v = not (is_glob v)
end

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

type 'info pinstr = (pexpr,'info) ginstr
type 'info pstmt  = (pexpr,'info) gstmt

type 'info pfunc     = (pexpr,'info) gfunc
type 'info pmod_item = (pexpr,'info) gmod_item
type 'info pprog     = (pexpr,'info) gprog

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
 | Pget(a1,b1,v1,e1), Pget(a2, b2,v2,e2) -> a1 = a2 && b1 = b2 && PV.gequal v1 v2 && pexpr_equal e1 e2
 | Psub(a1,b1,l1,v1,e1), Psub(a2,b2,l2,v2,e2) ->
   a1 = a2 && b1 = b2 && pexpr_equal l1 l2 && PV.gequal v1 v2 && pexpr_equal e1 e2
 | Pload(b1,v1,e1), Pload(b2,v2,e2) -> b1 = b2 && PV.equal (L.unloc v1) (L.unloc v2) && pexpr_equal e1 e2
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

type 'info instr = (int,'info) ginstr
type 'info stmt  = (int,'info) gstmt

type 'info func     = (int,'info) gfunc
type 'info mod_item = (int,'info) gmod_item
type global_decl    = var * Global.glob_value
type 'info prog     = global_decl list * 'info func list

module V = struct
  type t = var
  include GV

  let gequal x1 x2 = equal (L.unloc x1.gv) (L.unloc x2.gv) && (x1.gs = x2.gs)
end

module Sv = Set.Make  (V)
module Mv = Map.Make  (V)
module Hv = Hash.Make (V)

let rip = V.mk "RIP" (Reg(Normal, Direct)) u64 L._dummy []
let rsp = V.mk "RSP" (Reg(Normal, Direct)) u64 L._dummy []

let rec expr_equal (e1 :expr) (e2 : expr) : bool =
 match e1, e2 with
 | Pconst n1, Pconst n2 -> Z.equal n1 n2
 | Pbool b1, Pbool b2 -> b1 = b2
 | Pvar v1, Pvar v2 -> V.gequal v1 v2
 | Pget(a1,b1,v1,e1), Pget(a2, b2,v2,e2) -> a1 = a2 && b1 = b2 && V.gequal v1 v2 && expr_equal e1 e2
 | Psub(a1,b1,l1,v1,e1), Psub(a2,b2,l2,v2,e2) ->
   a1 = a2 && b1 = b2 && l1 = l2 && V.gequal v1 v2 && expr_equal e1 e2
 | Pload(b1,v1,e1), Pload(b2,v2,e2) -> b1 = b2 && V.equal (L.unloc v1) (L.unloc v2) && expr_equal e1 e2
 | Papp1(o1,e1), Papp1(o2,e2) -> o1 = o2 && expr_equal e1 e2
 | Papp2(o1,e11,e12), Papp2(o2,e21,e22) -> o1 = o2 && expr_equal e11 e21 && expr_equal e12 e22
 | Pif(_,e11,e12,e13), Pif(_,e21,e22,e23) -> expr_equal e11 e21 && expr_equal e12 e22 && expr_equal e13 e23
 | _, _ -> false

(* ------------------------------------------------------------------------ *)
(* Function name                                                            *)

module F = struct
  let mk fn_name =
    { fn_name; fn_id = Uniq.gen (); }

  type t = funname

  let compare f1 f2 = f1.fn_id - f2.fn_id

  let equal f1 f2 = f1.fn_id = f2.fn_id

  let hash f = f.fn_id
end

module Sf = Set.Make (F)
module Mf = Map.Make (F)
module Hf = Hash.Make(F)


(* -------------------------------------------------------------------- *)
(* used variables                                                       *)

let rvars_v f x s =
  if is_gkvar x then f (L.unloc x.gv) s
  else s 

let rec rvars_e f s = function
  | Pconst _ | Pbool _ | Parr_init _ -> s
  | Pvar x         -> rvars_v f x s
  | Pget(_,_,x,e) | Psub (_, _, _, x, e) -> rvars_e f (rvars_v f x s) e
  | Pload(_,x,e)   -> rvars_e f (f (L.unloc x) s) e
  | Papp1(_, e)    -> rvars_e f s e
  | Papp2(_,e1,e2) -> rvars_e f (rvars_e f s e1) e2
  | PappN (_, es) -> rvars_es f s es
  | Pif(_,e,e1,e2)   -> rvars_e f (rvars_e f (rvars_e f s e) e1) e2

and rvars_es f s es = List.fold_left (rvars_e f) s es

let rvars_lv f s = function
 | Lnone _       -> s
 | Lvar x        -> f (L.unloc x) s
 | Lmem (_,x,e)
 | Laset (_,_,x,e)
 | Lasub (_,_,_,x,e) -> rvars_e f (f (L.unloc x) s) e

let rvars_lvs f s lvs = List.fold_left (rvars_lv f) s lvs

let rec rvars_i f s i =
  match i.i_desc with
  | Cassgn(x, _, _, e)  -> rvars_e f (rvars_lv f s x) e
  | Copn(x,_,_,e) | Csyscall (x, _, e) -> rvars_es f (rvars_lvs f s x) e
  | Cif(e,c1,c2)   -> rvars_c f (rvars_c f (rvars_e f s e) c1) c2
  | Cfor(x,(_,e1,e2), c) ->
    rvars_c f (rvars_e f (rvars_e f (f (L.unloc x) s) e1) e2) c
  | Cwhile(_,c,e,c')    -> rvars_c f (rvars_e f (rvars_c f s c') e) c
  | Ccall(_,x,_,e) -> rvars_es f (rvars_lvs f s x) e

and rvars_c f s c =  List.fold_left (rvars_i f) s c

let fold_vars_fc f z fc =
  let a  = List.fold_left (fun a x -> f (L.unloc x) a) z fc.f_ret in
  rvars_c f a fc.f_body

let vars_lv z x = rvars_lv Sv.add z x
let vars_e e = rvars_e Sv.add Sv.empty e
let vars_es es = rvars_es Sv.add Sv.empty es
let vars_i i = rvars_i Sv.add Sv.empty i
let vars_c c = rvars_c Sv.add Sv.empty c

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
  | Ccall(_, xs, fn, _) ->
     List.fold_left written_lv v xs, Mf.modify_def [] fn (fun old -> i.i_loc :: old) f
  | Cif(_, s1, s2)
  | Cwhile(_, s1, _, s2)
    -> written_vars_stmt (written_vars_stmt acc s1) s2
  | Cfor(_, _, s) -> written_vars_stmt acc s
and written_vars_stmt acc s =
  List.fold_left written_vars_i acc s

let written_vars_fc fc =
  written_vars_stmt (Sv.empty, Mf.empty) fc.f_body

let written_vars s = 
  written_vars_stmt (Sv.empty, Mf.empty) s

(* -------------------------------------------------------------------- *)
(* Refresh i_loc, ensure that locations are uniq                        *)

let rec refresh_i_loc_i (i:'info instr) : 'info instr =
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

and refresh_i_loc_c (c:'info stmt) : 'info stmt =
  List.map refresh_i_loc_i c

let refresh_i_loc_f (f:'info func) : 'info func =
  { f with f_body = refresh_i_loc_c f.f_body }

let refresh_i_loc_p (p:'info prog) : 'info prog =
  fst p, List.map refresh_i_loc_f (snd p)


(* -------------------------------------------------------------------- *)
(* Functions on types                                                   *)

let int_of_ws = function
  | U8   -> 8
  | U16  -> 16
  | U32  -> 32
  | U64  -> 64
  | U128 -> 128
  | U256 -> 256

let size_of_ws = function
  | U8   -> 1
  | U16  -> 2
  | U32  -> 4
  | U64  -> 8
  | U128 -> 16
  | U256 -> 32

let string_of_ws ws = Format.sprintf "u%i" (int_of_ws ws)

let wsize_lt ws1 ws2 = Wsize.wsize_cmp ws1 ws2 = Datatypes.Lt
let wsize_le ws1 ws2 = Wsize.wsize_cmp ws1 ws2 <> Datatypes.Gt

let uptr = U64 (* Warning this should be arch dependent *)

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

let cast64 e = Papp1 (Oword_of_int U64, e)

let is_var = function
  | Pvar _ -> true
  | _ -> false

let get_ofs aa ws e =
  match e with
  | Pconst i ->
     Some
       (match aa with
        | Warray_.AAdirect -> Z.to_int i
        | Warray_.AAscale -> size_of_ws ws * Z.to_int i
       )
  | _ -> None

(* -------------------------------------------------------------------- *)
(* Functions over lvalues                                               *)

let expr_of_lval = function
  | Lnone _         -> None
  | Lvar x          -> Some (Pvar (gkvar x))
  | Lmem (ws, x, e) -> Some (Pload(ws,x,e))
  | Laset(a, ws, x, e) -> Some (Pget(a,ws,gkvar x,e))
  | Lasub(a, ws, l, x, e) -> Some (Psub(a,ws,l,gkvar x, e))

(* -------------------------------------------------------------------- *)
(* Functions over instructions                                          *)

let destruct_move i =
  match i.i_desc with
  | Cassgn(x, tag, ty, e) -> x, tag, ty, e
  | _                 -> assert false

let rec has_syscall_i i = 
  match i.i_desc with
  | Csyscall _ -> true
  | Cassgn _ | Copn _ | Ccall _ -> false 
  | Cif (_, c1, c2) | Cwhile(_, c1, _, c2) -> has_syscall c1 || has_syscall c2 
  | Cfor (_, _, c) -> has_syscall c

and has_syscall c = List.exists has_syscall_i c

(* -------------------------------------------------------------------- *)
let clamp (sz : wsize) (z : Z.t) =
  Z.erem z (Z.shift_left Z.one (int_of_ws sz))

let clamp_pe (sz : pelem) (z : Z.t) =
  Z.erem z (Z.shift_left Z.one (int_of_pe sz))


(* --------------------------------------------------------------------- *)
type 'info sfundef = Expr.stk_fun_extra * 'info func
type 'info sprog   = 'info sfundef list * Expr.sprog_extra
