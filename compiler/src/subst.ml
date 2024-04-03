open Utils
open Prog
module L = Location

(* When there is no location, we report an internal error. *)
let hierror ?loc fmt =
  let h = hierror ~kind:"compilation error" ~sub_kind:"param expansion" in
  match loc with
  | None -> h ~loc:Lnone ~internal:true fmt
  | Some loc -> h ~loc:(Lone loc) fmt

let gsubst_ty (flen: 'len1 -> 'len2) ty = 
  match ty with
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, flen e)

let rec gsubst_e (flen: ?loc:L.t -> 'len1 -> 'len2) (f: 'len1 ggvar -> 'len2 gexpr) e =
  match e with
  | Pconst c -> Pconst c
  | Pbool b  -> Pbool b
  | Parr_init n -> Parr_init (flen n)
  | Pvar v -> f v
  | Pget (al, aa, ws, v, e) -> Pget(al, aa, ws, gsubst_gvar f v, gsubst_e flen f e)
  | Psub (aa, ws, len, v, e) -> Psub(aa,ws,flen ~loc:(L.loc v.gv) len, gsubst_gvar f v, gsubst_e flen f e)
  | Pload (al, ws, v, e) -> Pload (al, ws, gsubst_vdest f v, gsubst_e flen f e)
  | Papp1 (o, e)     -> Papp1 (o, gsubst_e flen f e)
  | Papp2 (o, e1, e2)-> Papp2 (o, gsubst_e flen f e1, gsubst_e flen f e2)
  | PappN (o, es) -> PappN (o, List.map (gsubst_e flen f) es)
  | Pif   (ty, e, e1, e2)-> Pif(gsubst_ty (flen ?loc:None) ty, gsubst_e flen f e, gsubst_e flen f e1, gsubst_e flen f e2)

and gsubst_gvar f v = 
  match f v with
  | Pvar v -> v
  | _      -> assert false

and gsubst_vdest f v =
  let v = gsubst_gvar f (gkvar v) in
  assert (is_gkvar v);
  v.gv

let gsubst_lval (flen: ?loc:L.t -> 'len1 -> 'len2) f lv =
  match lv with
  | Lnone(i,ty)  -> Lnone(i, gsubst_ty (flen ~loc:i) ty)
  | Lvar v       -> Lvar (gsubst_vdest f v)
  | Lmem (al, w,v,e) -> Lmem(al, w, gsubst_vdest f v, gsubst_e flen f e)
  | Laset(al, aa,w,v,e) -> Laset(al, aa, w, gsubst_vdest f v, gsubst_e flen f e)
  | Lasub(aa,w,len,v,e) -> Lasub(aa, w, flen ~loc:(L.loc v) len, gsubst_vdest f v, gsubst_e flen f e)

let gsubst_lvals flen f  = List.map (gsubst_lval flen f)
let gsubst_es flen f = List.map (gsubst_e flen f)

let rec gsubst_i (flen: ?loc:L.t -> 'len1 -> 'len2) f i =
  let i_desc =
    match i.i_desc with
    | Cassgn(x, tg, ty, e) ->
      let e = gsubst_e flen f e in
      let x = gsubst_lval flen f x in
      let ty = gsubst_ty (flen ?loc:None) ty in
      Cassgn(x, tg, ty, e)
    | Copn(x,t,o,e)   -> Copn(gsubst_lvals flen f x, t, o, gsubst_es flen f e)
    | Csyscall(x,o,e)   -> Csyscall(gsubst_lvals flen f x, o, gsubst_es flen f e)
    | Cif(e,c1,c2)  -> Cif(gsubst_e flen f e, gsubst_c flen f c1, gsubst_c flen f c2)
    | Cfor(x,(d,e1,e2),c) ->
        Cfor(gsubst_vdest f x, (d, gsubst_e flen f e1, gsubst_e flen f e2), gsubst_c flen f c)
    | Cwhile(a, c, e, c') -> 
      Cwhile(a, gsubst_c flen f c, gsubst_e flen f e, gsubst_c flen f c')
    | Ccall(x,fn,e) -> Ccall(gsubst_lvals flen f x, fn, gsubst_es flen f e) in
  { i with i_desc }

and gsubst_c flen f c = List.map (gsubst_i flen f) c

let gsubst_func (flen: ?loc:L.t -> 'len1 -> 'len2) f fc =
  let dov v = L.unloc (gsubst_vdest f (L.mk_loc L._dummy v)) in
  { fc with
    f_tyin = List.map (gsubst_ty (flen ?loc:None)) fc.f_tyin;
    f_args = List.map dov fc.f_args;
    f_body = gsubst_c flen f fc.f_body;
    f_tyout = List.map (gsubst_ty (flen ?loc:None)) fc.f_tyout;
    f_ret  = List.map (gsubst_vdest f) fc.f_ret
  }

let subst_func f fc =
  gsubst_func (fun ?loc:_ ty -> ty)
     (fun v -> if is_gkvar v then f v.gv else Pvar v) fc

(* ---------------------------------------------------------------- *)

type psubst = pexpr ggvar -> pexpr

let rec psubst_e (f: psubst) e =
  gsubst_e (fun ?loc:_ -> psubst_e f) f e
  

let psubst_ty f (ty:pty) : pty = 
  match ty with
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, psubst_e f e)

let psubst_v subst =
  let subst = ref subst in
  let rec aux v : pexpr =
    let k = v.gs in
    let v = v.gv in
    let v_ = v.L.pl_desc in
    let e = 
      try Mpv.find v_ !subst
      with Not_found ->
        assert (not (PV.is_glob v_));
        let ty = psubst_ty aux v_.v_ty in
        let v' = PV.mk v_.v_name v_.v_kind ty v_.v_dloc v_.v_annot in
        let v = {v with L.pl_desc = v'} in
        let v = { gv = v; gs = k } in
        let e = Pvar v in
        subst := Mpv.add v_ e !subst;
        e in
    match e with
    | Pvar x -> 
      let k = x.gs in
      let x = {x.gv with L.pl_loc = L.loc v} in
      let x = {gv = x; gs = k} in
      Pvar x
    | _      -> e in
  aux

let psubst_ge f = function
  | GEword e -> GEword (psubst_e f e)
  | GEarray es -> GEarray (List.map (psubst_e f) es)

let psubst_prog (prog:('info, 'asm) pprog) =
  let subst = ref (Mpv.empty : pexpr Mpv.t) in
  let rec aux = function
    | [] -> [], []
    | MIparam(v,e) :: items ->
        let g, p = aux items in
        let f = psubst_v !subst in 
        subst := Mpv.add v (psubst_e f e) !subst;
        g, p
    | MIglobal (v, e) :: items ->
      let g, p = aux items in
      let f = psubst_v !subst in
      let v' =
        let v =
          gsubst_gvar f {gv = L.mk_loc L._dummy v; gs = Expr.Sglob} in
        assert (not (is_gkvar v)); L.unloc v.gv in
      let e = psubst_ge f e in
      subst := Mpv.add v (Pvar (gkglob (L.mk_loc L._dummy v'))) !subst;
      (v', e) :: g, p
    | MIfun fc :: items ->
        let g, p = aux items in
        let subst_v = psubst_v !subst in
        let subst_ty = psubst_ty subst_v in
        let dov v =
          L.unloc (gsubst_vdest subst_v (L.mk_loc L._dummy v)) in
        let fc = {
            fc with
            f_tyin = List.map subst_ty fc.f_tyin;
            f_args = List.map dov fc.f_args;
            f_body = gsubst_c (fun ?loc:_ -> psubst_e subst_v) subst_v fc.f_body;
            f_tyout = List.map subst_ty fc.f_tyout;
            f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret
          } in
        g, fc::p in
    aux prog

(* ---------------------------------------------------------------- *)
(* Simplify type                                                    *)

let int_of_op2 ?loc o =
  match o with
  | Expr.Oadd Op_int -> Z.add
  | Expr.Omul Op_int -> Z.mul
  | Expr.Osub Op_int -> Z.sub
  | Expr.Odiv Cmp_int -> Z.div
  | Expr.Omod Cmp_int -> Z.erem
  | _     -> hierror ?loc "operator %s not allowed in array size (only standard arithmetic operators and modulo are allowed)" (PrintCommon.string_of_op2 o)

let rec int_of_expr ?loc e =
  match e with
  | Pconst i -> i
  | Papp2 (o, e1, e2) ->
      let op = int_of_op2 ?loc o in
      op (int_of_expr ?loc e1) (int_of_expr ?loc e2)
  | Pbool _ | Parr_init _ | Pvar _ 
  | Pget _ | Psub _ | Pload _ | Papp1 _ | PappN _ | Pif _ ->
      hierror ?loc "expression %a not allowed in array size (only constant arithmetic expressions are allowed)" Printer.pp_pexpr e


let isubst_len ?loc e =
  let z = int_of_expr ?loc e in
  try Z.to_int z
  with Z.Overflow ->
    hierror ?loc "cannot define a (sub-)array of size %a, this number is too big" Z.pp_print z

let isubst_ty ?loc = function
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, isubst_len ?loc e)


let isubst_prog glob prog =

  let isubst_v subst =
    let aux v0 =
      let k = v0.gs in
      let v = v0.gv in
      let v_ = v.L.pl_desc in
      let e =
        try Mpv.find v_ !subst
        with Not_found ->
          let ty = isubst_ty ~loc:v_.v_dloc v_.v_ty in
          let v1 = V.mk v_.v_name v_.v_kind ty v_.v_dloc v_.v_annot in
          let v  = { v with L.pl_desc = v1 } in
          let v0 = { gv = v; gs = k } in
          let e = Pvar v0 in
          subst := Mpv.add v_ e !subst;
          e in
      match e with
      | Pvar x -> 
        let k = x.gs in
        let x = {x.gv with L.pl_loc = L.loc v} in
        let x = {gv = x; gs = k} in
        Pvar x
      | _      -> e in
    aux in 

  let subst = ref Mpv.empty in
  
  let isubst_glob (x, gd) = 
    let subst_v = isubst_v subst in
    let x = 
      let x = 
        gsubst_gvar subst_v {gv = L.mk_loc L._dummy x; gs = Expr.Sglob} in
      assert (not (is_gkvar x)); L.unloc x.gv in

    let gd = 
      match gd with
      | GEword e -> GEword (gsubst_e isubst_len subst_v e)
      | GEarray es -> GEarray (List.map (gsubst_e isubst_len subst_v) es) in
    x, gd in
  let glob = List.map isubst_glob glob in

  let subst = !subst in

  let isubst_item fc = 
    let subst = ref subst in
    let subst_v = isubst_v subst in
    let dov v =
      L.unloc (gsubst_vdest subst_v (L.mk_loc L._dummy v)) in
    (* Order matters so that the clearest error is triggered first.
       We use let-in to enforce the right order *)
    let f_args = List.map dov fc.f_args in
    let f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret in
    let fc = {
        fc with
        f_tyin = List.map isubst_ty fc.f_tyin;
        f_args;
        f_body = gsubst_c isubst_len subst_v fc.f_body;
        f_tyout = List.map isubst_ty fc.f_tyout;
        f_ret;
      } in
    fc
  in
  let isubst_item fc =
    try isubst_item fc
    with HiError e -> raise (HiError { e with err_funname = Some fc.f_name.fn_name })
  in

  let prog = List.map isubst_item prog in
  glob, prog 



(* ---------------------------------------------------------------- *)
(* Remove parameter from program definition                         *)

exception NotAConstantExpr

let clamp_k k e = 
  match k with 
  | E.Op_w ws -> clamp ws e
  | E.Op_int  -> e

let rec constant_of_expr (e: Prog.expr) : Z.t =
  let open Prog in

  match e with
  | Papp1 (Oword_of_int sz, e) ->
      clamp sz (constant_of_expr e)

  | Papp1(Oint_of_word sz, e) ->
      clamp sz (constant_of_expr e)

  | Pconst z ->
      z

  | _ -> raise NotAConstantExpr


let remove_params (prog : ('info, 'asm) pprog) =
  let globals, prog = psubst_prog prog in
  let globals, prog = isubst_prog globals prog in

  let global_tbl = Hv.create 101 in
  let add_glob x gv = Hv.add global_tbl x gv in
  let get_glob x = Hv.find_option global_tbl (Conv.var_of_cvar x) in

  let mk_word ws e =
    let open Constant_prop in
    let e = Conv.cexpr_of_expr e in
    let c = const_prop_e (fun _ -> assert false) (Some get_glob) Var0.Mvar.empty e in
    let z = constant_of_expr (Conv.expr_of_cexpr c) in
    Word0.wrepr ws (Conv.cz_of_z (clamp ws z)) in


  let doglob (x, e) =
    let gv =
      match x.v_ty, e with
      | Bty (U ws), GEword e ->
        begin try Global.Gword (ws, mk_word ws e)
        with NotAConstantExpr ->
          hierror ~loc:x.v_dloc "the expression assigned to global variable %a must evaluate to a constant"
            (Printer.pp_var ~debug:false) x
        end
      | Arr (_ws, n), GEarray es when List.length es <> n ->
         let m = List.length es in
         hierror ~loc:x.v_dloc "array size mismatch for global variable %a: %d %s given (%d expected)"
           (Printer.pp_var ~debug:false) x
           (List.length es)
           (if m > 1 then "values" else "value")
           n
      | Arr (ws, n), GEarray es ->
        let p = Conv.pos_of_int (n * size_of_ws ws) in
        let mk_word_i i e =
          try mk_word ws e
          with NotAConstantExpr ->
            hierror ~loc:x.v_dloc "in the list assigned to global variable %a, the expression at position %d must evaluate to a constant"
              (Printer.pp_var ~debug:false) x
              i
        in
        let t = Warray_.WArray.of_list ws (List.mapi mk_word_i es) in
        Global.Garr(p, t)
      | _, _ -> assert false in
    add_glob x gv;
    x, gv
  in
  let globals = List.rev_map doglob (List.rev globals) in
  globals, prog


(* ---------------------------------------------------------------- *)
(* Rename all variable using fresh variable                         *)

let csubst_v () =
  let tbl = Hv.create 101 in
  let aux v =
    if not (is_gkvar v) then Pvar v
    else
      let v_ = v.gv.L.pl_desc in
      let v' = 
        try Hv.find tbl v_
        with Not_found ->
          let v' = V.clone v_ in
          Hv.add tbl v_ v'; v' in
    Pvar (gkvar { v.gv with L.pl_desc = v' }) in
  aux

let clone_func fc =
  let subst_v = csubst_v () in
  gsubst_func (fun ?loc:_ ty -> ty) subst_v fc

(* ---------------------------------------------------------------- *)
(* extend instruction info                                          *)

let rec extend_iinfo_i pre i =
  let i_desc = 
    match i.i_desc with
    | Cassgn _ | Copn _ | Csyscall _ | Ccall _ -> i.i_desc
    | Cif(e,c1,c2) -> 
      Cif(e, extend_iinfo_c pre c1, extend_iinfo_c pre c2)
    | Cfor(x,r,c) -> 
      Cfor(x,r, extend_iinfo_c pre c)
    | Cwhile (a, c1, e, c2) -> 
      Cwhile(a, extend_iinfo_c pre c1, e, extend_iinfo_c pre c2) in
  let {L.base_loc = ii; L.stack_loc = l} = i.i_loc in
  let i_loc = L.i_loc ii (l @ pre) in
  { i with i_desc; i_loc }

and extend_iinfo_c pre c = List.map (extend_iinfo_i pre) c

let extend_iinfo {L.base_loc = i; L.stack_loc = l} fd = 
  { fd with f_body = extend_iinfo_c (i::l) fd.f_body }

(* ---------------------------------------------------------------- *)
(* Perform a substitution of variable by variable                   *) 

type vsubst = var Mv.t 

let vsubst_v s v = try Mv.find v s with Not_found -> v

let vsubst_vi s v = {v with L.pl_desc = vsubst_v s (L.unloc v) }

let vsubst_gv s v = { v with gv = vsubst_vi s v.gv }

let vsubst_ve s v = Pvar (vsubst_gv s v) 
  
let vsubst_e  s = gsubst_e  (fun ?loc:_ ty -> ty) (vsubst_ve s)
let vsubst_es s = gsubst_es (fun ?loc:_ ty -> ty) (vsubst_ve s)

let vsubst_lval  s = gsubst_lval  (fun ?loc:_ ty -> ty) (vsubst_ve s)
let vsubst_lvals s = gsubst_lvals (fun ?loc:_ ty -> ty) (vsubst_ve s)

let vsubst_i s = gsubst_i (fun ?loc:_ ty -> ty) (vsubst_ve s)
let vsubst_c s = gsubst_c (fun ?loc:_ ty -> ty) (vsubst_ve s)

let vsubst_func s = gsubst_func (fun ?loc:_ ty -> ty) (vsubst_ve s)

