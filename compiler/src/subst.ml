open Prog
module L = Location

let gsubst_ty (flen: 'len1 -> 'len2) ty = 
  match ty with
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, flen e)

let rec gsubst_e (flen: 'len1 -> 'len2) (f: 'len1 ggvar -> 'len2 gexpr) e =
  match e with
  | Pconst c -> Pconst c
  | Pbool b  -> Pbool b
  | Parr_init n -> Parr_init (flen n)
  | Pvar v -> f v
  | Pget (aa, ws, v, e) -> Pget(aa, ws, gsubst_gvar f v, gsubst_e flen f e)
  | Psub (aa, ws, len, v, e) -> Psub(aa,ws,flen len, gsubst_gvar f v, gsubst_e flen f e)
  | Pload (ws, v, e) -> Pload (ws, gsubst_vdest f v, gsubst_e flen f e)
  | Papp1 (o, e)     -> Papp1 (o, gsubst_e flen f e)
  | Papp2 (o, e1, e2)-> Papp2 (o, gsubst_e flen f e1, gsubst_e flen f e2)
  | PappN (o, es) -> PappN (o, List.map (gsubst_e flen f) es)
  | Pif   (ty, e, e1, e2)-> Pif(gsubst_ty flen ty, gsubst_e flen f e, gsubst_e flen f e1, gsubst_e flen f e2)

and gsubst_gvar f v = 
  match f v with
  | Pvar v -> v
  | _      -> assert false

and gsubst_vdest f v =
  let v = gsubst_gvar f (gkvar v) in
  assert (is_gkvar v);
  v.gv

let gsubst_lval flen f lv =
  match lv with
  | Lnone(i,ty)  -> Lnone(i, gsubst_ty flen ty)
  | Lvar v       -> Lvar (gsubst_vdest f v)
  | Lmem (w,v,e) -> Lmem(w, gsubst_vdest f v, gsubst_e flen f e)
  | Laset(aa,w,v,e) -> Laset(aa, w, gsubst_vdest f v, gsubst_e flen f e)
  | Lasub(aa,w,len,v,e) -> Lasub(aa, w, flen len, gsubst_vdest f v, gsubst_e flen f e)

let gsubst_lvals flen f  = List.map (gsubst_lval flen f)
let gsubst_es flen f = List.map (gsubst_e flen f)

let rec gsubst_i flen f i =
  let i_desc =
    match i.i_desc with
    | Cassgn(x, tg, ty, e) -> Cassgn(gsubst_lval flen f x, tg, gsubst_ty flen ty, gsubst_e flen f e)
    | Copn(x,t,o,e)   -> Copn(gsubst_lvals flen f x, t, o, gsubst_es flen f e)
    | Cif(e,c1,c2)  -> Cif(gsubst_e flen f e, gsubst_c flen f c1, gsubst_c flen f c2)
    | Cfor(x,(d,e1,e2),c) ->
        Cfor(gsubst_vdest f x, (d, gsubst_e flen f e1, gsubst_e flen f e2), gsubst_c flen f c)
    | Cwhile(a, c, e, c') -> 
      Cwhile(a, gsubst_c flen f c, gsubst_e flen f e, gsubst_c flen f c')
    | Ccall(ii,x,fn,e) -> Ccall(ii, gsubst_lvals flen f x, fn, gsubst_es flen f e) in
  { i with i_desc }

and gsubst_c flen f c = List.map (gsubst_i flen f) c

let gsubst_func flen f fc =
  let dov v = L.unloc (gsubst_vdest f (L.mk_loc L._dummy v)) in
  { fc with
    f_tyin = List.map (gsubst_ty flen) fc.f_tyin;
    f_args = List.map dov fc.f_args;
    f_body = gsubst_c flen f fc.f_body;
    f_tyout = List.map (gsubst_ty flen) fc.f_tyout;
    f_ret  = List.map (gsubst_vdest f) fc.f_ret
  }

let subst_func f fc =
  gsubst_func (fun ty -> ty)
     (fun v -> if is_gkvar v then f v.gv else Pvar v) fc

(* ---------------------------------------------------------------- *)

type psubst = pexpr Mv.t

let rec psubst_e (f: pexpr ggvar -> pexpr) e = 
  gsubst_e (psubst_e f) f e
  

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
        let v' = PV.mk v_.v_name v_.v_kind ty v_.v_dloc in
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

let psubst_prog (prog:'info pprog) =
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
      let e = psubst_ge f e in
      subst := Mpv.add v (Pvar (gkglob (L.mk_loc L._dummy v))) !subst;
      (v, e) :: g, p
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
            f_body = gsubst_c (psubst_e subst_v) subst_v fc.f_body;
            f_tyout = List.map subst_ty fc.f_tyout;
            f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret
          } in
        g, fc::p in
    aux prog

(* ---------------------------------------------------------------- *)
(* Simplify type                                                    *)

let int_of_op2 o i1 i2 =
  match o with
  | Expr.Oadd Op_int -> B.add i1 i2
  | Expr.Omul Op_int -> B.mul i1 i2
  | Expr.Osub Op_int -> B.sub i1 i2
  | Expr.Odiv Cmp_int -> B.div i1 i2
  | Expr.Omod Cmp_int -> B.erem i1 i2
  | _     -> Utils.hierror "operator %s not allowed in array size" (Printer.string_of_op2 o)

let rec int_of_expr e =
  match e with
  | Pconst i -> i
  | Papp2 (o, e1, e2) ->
      int_of_op2 o (int_of_expr e1) (int_of_expr e2)
  | Pbool _ | Parr_init _ | Pvar _ 
  | Pget _ | Psub _ | Pload _ | Papp1 _ | PappN _ | Pif _ -> assert false


let isubst_len e = B.to_int (int_of_expr e)

let isubst_ty = function
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, isubst_len e)


let isubst_prog glob prog =

  let isubst_v subst =
    let aux v0 =
      let k = v0.gs in
      let v = v0.gv in
      let v_ = v.L.pl_desc in
      try Mpv.find v_ !subst
      with Not_found ->
        let ty = isubst_ty v_.v_ty in
        let v1 = V.mk v_.v_name v_.v_kind ty v_.v_dloc in
        let v  = { v with L.pl_desc = v1 } in
        let v0 = { gv = v; gs = k } in
        let e = Pvar v0 in
        subst := Mpv.add v_ e !subst;
        e in
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
    let fc = {
        fc with
        f_tyin = List.map isubst_ty fc.f_tyin;
        f_args = List.map dov fc.f_args;
        f_body = gsubst_c isubst_len subst_v fc.f_body;
        f_tyout = List.map isubst_ty fc.f_tyout;
        f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret
      } in
    fc in

  let prog = List.map isubst_item prog in
  glob, prog 



(* ---------------------------------------------------------------- *)
(* Remove parameter from program definition                         *)

exception NotAConstantExpr

let clamp_k k e = 
  match k with 
  | E.Op_w ws -> clamp ws e
  | E.Op_int  -> e

let rec constant_of_expr (e: Prog.expr) : Bigint.zint =
  let open Prog in

  match e with
  | Papp1 (Oword_of_int sz, e) ->
      clamp sz (constant_of_expr e)

  | Papp1(Oint_of_word sz, e) ->
      clamp sz (constant_of_expr e)

  | Pconst z ->
      z

  | Papp1 (Oneg k, e) ->
      clamp_k k (Bigint.neg (clamp_k k (constant_of_expr e)))

  | Papp2 (Oadd k, e1, e2) ->
      let e1 = clamp_k k (constant_of_expr e1) in
      let e2 = clamp_k k (constant_of_expr e2) in
      clamp_k k (Bigint.add e1 e2)

  | Papp2 (Osub k, e1, e2) ->
      let e1 = clamp_k k (constant_of_expr e1) in
      let e2 = clamp_k k (constant_of_expr e2) in
      clamp_k k (Bigint.sub e1 e2)

  | Papp2 (Omul k, e1, e2) ->
      let e1 = clamp_k k (constant_of_expr e1) in
      let e2 = clamp_k k (constant_of_expr e2) in
      clamp_k k (Bigint.mul e1 e2)

  | PappN(Opack(ws,pe), es) ->
      let es = List.map constant_of_expr es in
      let k = int_of_pe pe in
      let e = 
        List.fold_left (fun n e -> 
            Bigint.add (Bigint.lshift n k) (clamp_pe pe e)) Bigint.zero es in
      clamp ws e

  | _ -> raise NotAConstantExpr


let remove_params (prog : 'info pprog) =
  let globals, prog = psubst_prog prog in
  let globals, prog = isubst_prog globals prog in
  let mk_word ws e =
    Word0.wrepr ws (Conv.z_of_bi (clamp ws (constant_of_expr e))) in
  let doglob (x, e) =
    match x.v_ty, e with
    | Bty (U ws), GEword e ->
      x, Global.Gword (ws, mk_word ws e)
    | Arr (_ws, n), GEarray es when List.length es <> n ->
       let m = List.length es in
       Utils.hierror "%s: array size mismatch for global variable %a: %d %s given (%d expected)"
         (Location.tostring x.v_dloc)
         (Printer.pp_var ~debug:false) x
         (List.length es)
         (if m > 1 then "values" else "value")
         n
    | Arr (ws, n), GEarray es ->
      let p = Conv.pos_of_int (n * size_of_ws ws) in
      let t = ref (Warray_.WArray.empty p) in
      let doit i e =
        match Warray_.WArray.set p ws !t Warray_.AAscale (Conv.z_of_int i) (mk_word ws e) with
        | Ok t1 -> t := t1
        | _ -> assert false in
      List.iteri doit es;
      x, Global.Garr(p, !t)
    | _, _ -> assert false
  in
  let globals = List.map doglob globals in
  globals, prog


(* ---------------------------------------------------------------- *)
(* Rename all variable using fresh variable                         *)

let csubst_v () =
  let tbl = Hv.create 101 in
  let rec aux v =
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
  gsubst_func (fun ty -> ty) subst_v fc

(* ---------------------------------------------------------------- *)
(* extend instruction info                                          *)

let rec extend_iinfo_i pre i =
  let i_desc = 
    match i.i_desc with
    | Cassgn _ | Copn _ | Ccall _ -> i.i_desc
    | Cif(e,c1,c2) -> 
      Cif(e, extend_iinfo_c pre c1, extend_iinfo_c pre c2)
    | Cfor(x,r,c) -> 
      Cfor(x,r, extend_iinfo_c pre c)
    | Cwhile (a, c1, e, c2) -> 
      Cwhile(a, extend_iinfo_c pre c1, e, extend_iinfo_c pre c2) in
  let ii, l = i.i_loc in
  let i_loc = ii, (l @ pre) in
  { i with i_desc; i_loc }

and extend_iinfo_c pre c = List.map (extend_iinfo_i pre) c

let extend_iinfo (i,l) fd = 
  { fd with f_body = extend_iinfo_c (i::l) fd.f_body }

(* ---------------------------------------------------------------- *)
(* Perform a substitution of variable by variable                   *) 

type vsubst = var Mv.t 

let vsubst_v s v = try Mv.find v s with Not_found -> v

let vsubst_vi s v = {v with L.pl_desc = vsubst_v s (L.unloc v) }

let vsubst_gv s v = { v with gv = vsubst_vi s v.gv }

let vsubst_ve s v = Pvar (vsubst_gv s v) 
  
let vsubst_e  s = gsubst_e  (fun ty -> ty) (vsubst_ve s)
let vsubst_es s = gsubst_es (fun ty -> ty) (vsubst_ve s) 

let vsubst_lval  s = gsubst_lval  (fun ty -> ty) (vsubst_ve s)
let vsubst_lvals s = gsubst_lvals (fun ty -> ty) (vsubst_ve s)

let vsubst_i s = gsubst_i (fun ty -> ty) (vsubst_ve s)
let vsubst_c s = gsubst_c (fun ty -> ty) (vsubst_ve s)

let vsubst_func s = gsubst_func (fun ty -> ty) (vsubst_ve s)

