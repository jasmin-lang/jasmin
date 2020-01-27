open Prog
module L = Location

let rec gsubst_e (fty: 'ty1 -> 'ty2) (f: 'ty1 gvar_i -> 'ty2 gexpr) e =
  match e with
  | Pconst c -> Pconst c
  | Pbool b  -> Pbool b
  | Parr_init n -> Parr_init n
  | Pvar v -> f v
  | Pglobal (ws, g)  -> Pglobal (ws, g)
  | Pget  (ws, v, e) -> Pget(ws, gsubst_vdest f v, gsubst_e fty f e)
  | Pload (ws, v, e) -> Pload (ws, gsubst_vdest f v, gsubst_e fty f e)
  | Papp1 (o, e)     -> Papp1 (o, gsubst_e fty f e)
  | Papp2 (o, e1, e2)-> Papp2 (o, gsubst_e fty f e1, gsubst_e fty f e2)
  | PappN (o, es) -> PappN (o, List.map (gsubst_e fty f) es)
  | Pif   (ty, e, e1, e2)-> Pif(fty ty, gsubst_e fty f e, gsubst_e fty f e1, gsubst_e fty f e2)

and gsubst_vdest f v =
  match f v with
  | Pvar v -> v
  | _      -> assert false

let gsubst_lval fty f lv =
  match lv with
  | Lnone(i,ty)  -> Lnone(i, fty ty)
  | Lvar v       -> Lvar (gsubst_vdest f v)
  | Lmem (w,v,e) -> Lmem(w, gsubst_vdest f v, gsubst_e fty f e)
  | Laset(w,v,e) -> Laset(w, gsubst_vdest f v, gsubst_e fty f e)

let gsubst_lvals fty f  = List.map (gsubst_lval fty f)
let gsubst_es fty f = List.map (gsubst_e fty f)

let rec gsubst_i fty f i =
  let i_desc =
    match i.i_desc with
    | Cassgn(x, tg, ty, e) -> Cassgn(gsubst_lval fty f x, tg, fty ty, gsubst_e fty f e)
    | Copn(x,t,o,e)   -> Copn(gsubst_lvals fty f x, t, o, gsubst_es fty f e)
    | Cif(e,c1,c2)  -> Cif(gsubst_e fty f e, gsubst_c fty f c1, gsubst_c fty f c2)
    | Cfor(x,(d,e1,e2),c) ->
        Cfor(gsubst_vdest f x, (d, gsubst_e fty f e1, gsubst_e fty f e2), gsubst_c fty f c)
    | Cwhile(a, c, e, c') -> 
      Cwhile(a, gsubst_c fty f c, gsubst_e fty f e, gsubst_c fty f c')
    | Ccall(ii,x,fn,e) -> Ccall(ii, gsubst_lvals fty f x, fn, gsubst_es fty f e) in
  { i with i_desc }

and gsubst_c fty f c = List.map (gsubst_i fty f) c

let gsubst_func fty f fc =
  let dov v = L.unloc (gsubst_vdest f (L.mk_loc L._dummy v)) in
  { fc with
    f_tyin = List.map fty fc.f_tyin;
    f_args = List.map dov fc.f_args;
    f_body = gsubst_c fty f fc.f_body;
    f_tyout = List.map fty fc.f_tyout;
    f_ret  = List.map (gsubst_vdest f) fc.f_ret
  }

(* ---------------------------------------------------------------- *)

type psubst = pexpr Mv.t

let psubst_ty fty f ty = 
  match ty with
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, gsubst_e fty f e)

let psubst_v subst =
  let subst = ref subst in
  let rec aux v : pexpr =
    let v_ = v.L.pl_desc in
    let e = 
      try Mpv.find v_ !subst
      with Not_found ->
        assert (not (PV.is_glob v_));
        let ty = auxty v_.v_ty in
        let v' = PV.mk v_.v_name v_.v_kind ty v_.v_dloc in
        let e = Pvar {v with L.pl_desc = v'} in
        subst := Mpv.add v_ e !subst;
        e in
    match e with
    | Pvar x -> Pvar {x with L.pl_loc = L.loc v}
    | _      -> e 
  and auxty (ty:pty) : pty = psubst_ty auxty aux ty in
  auxty, aux

let psubst_prog (prog:'info pprog) : ((Name.t * pty) * pexpr) list * 'info pprog =
  let subst = ref (Mpv.empty : pexpr Mpv.t) in
  let rec aux = function
    | [] -> [], []
    | MIparam(v,e) :: items ->
        let g, p = aux items in
        let fty, f = psubst_v !subst in 
        subst := Mpv.add v (gsubst_e fty f e) !subst;
        g, p
    | MIglobal (v, e) :: items ->
      let g, p = aux items in
      let fty, f = psubst_v !subst in 
      let e = gsubst_e fty f e in
      (v, e) :: g, p
    | MIfun fc :: items ->
        let g, p = aux items in
        let subst_ty, subst_v = psubst_v !subst in
        let dov v =
          L.unloc (gsubst_vdest subst_v (L.mk_loc L._dummy v)) in
        let fc = {
            fc with
            f_tyin = List.map subst_ty fc.f_tyin;
            f_args = List.map dov fc.f_args;
            f_body = gsubst_c subst_ty subst_v fc.f_body;
            f_tyout = List.map subst_ty fc.f_tyout;
            f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret
          } in
        g, MIfun(fc)::p in
    aux prog

(* ---------------------------------------------------------------- *)
(* Simplify type                                                    *)

let int_of_op2 o i1 i2 =
  match o with
  | Expr.Oadd Op_int -> B.add i1 i2
  | Expr.Omul Op_int -> B.mul i1 i2
  | Expr.Osub Op_int -> B.sub i1 i2
  | _     -> assert false

let rec int_of_expr e =
  match e with
  | Pconst i -> i
  | Papp2 (o, e1, e2) ->
      int_of_op2 o (int_of_expr e1) (int_of_expr e2)
  | Pbool _ | Parr_init _ | Pvar _ | Pglobal _
  | Pget _ | Pload _ | Papp1 _ | PappN _ | Pif _ -> assert false


let isubst_ty = function
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, B.to_int (int_of_expr e))


let isubst_prog (glob: ((Name.t * pty) * _) list) (prog:'info pprog) =

  let isubst_v () =
    let subst = ref Mpv.empty in
    let aux v =
      let v_ = v.L.pl_desc in
      try Mpv.find v_ !subst
      with Not_found ->
        assert (not (PV.is_glob v_));
        let ty = isubst_ty v_.v_ty in
        let e =
          Pvar {v with
                 L.pl_desc = V.mk v_.v_name v_.v_kind ty v_.v_dloc } in
        subst := Mpv.add v_ e !subst;
        e in
    aux in

  let isubst_item = function
    | MIglobal _
    | MIparam _ -> assert false
    | MIfun fc  ->
      let subst_v = isubst_v () in
      let dov v =
        L.unloc (gsubst_vdest subst_v (L.mk_loc L._dummy v)) in
      let fc = {
          fc with
          f_tyin = List.map isubst_ty fc.f_tyin;
          f_args = List.map dov fc.f_args;
          f_body = gsubst_c isubst_ty subst_v fc.f_body;
          f_tyout = List.map isubst_ty fc.f_tyout;
          f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret
        } in
      fc in

  let isubst_glob ((x,ty),e) = 
    let subst_v = isubst_v () in
    let ty = isubst_ty ty in
    let e = gsubst_e isubst_ty subst_v e in
    ((x,ty),e) in

  let prog = List.map isubst_item prog in
  let glob = List.map isubst_glob glob in
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
  let doglob ((x,ty),e) = 
    let ws = 
      match ty with
      | Bty (U ws) -> ws 
      | _ -> raise NotAConstantExpr in
    ws, x, clamp ws (constant_of_expr e) in
  let globals = List.map doglob globals in 
  globals, prog

(* ---------------------------------------------------------------- *)
(* Rename all variable using fresh variable                         *)

let csubst_v () =
  let tbl = Hv.create 101 in
  let rec aux v =
    let v_ = v.L.pl_desc in
    let v' = 
      try Hv.find tbl v_
      with Not_found ->
        let v' = V.clone v_ in
        Hv.add tbl v_ v'; v' in
    Pvar { v with L.pl_desc = v' } in 
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

let vsubst_ve s v = Pvar (vsubst_vi s v) 
  
let vsubst_e  s = gsubst_e  (fun ty -> ty) (vsubst_ve s)
let vsubst_es s = gsubst_es (fun ty -> ty) (vsubst_ve s) 

let vsubst_lval  s = gsubst_lval  (fun ty -> ty) (vsubst_ve s)
let vsubst_lvals s = gsubst_lvals (fun ty -> ty) (vsubst_ve s)

let vsubst_i s = gsubst_i (fun ty -> ty) (vsubst_ve s)
let vsubst_c s = gsubst_c (fun ty -> ty) (vsubst_ve s)

let vsubst_func s = gsubst_func (fun ty -> ty) (vsubst_ve s)

