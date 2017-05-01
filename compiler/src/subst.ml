open Prog
module L = Location

let rec gsubst_e (f: 'ty1 gvar_i -> 'ty2 gexpr) e =
  match e with
  | Pconst c -> Pconst c
  | Pbool b  -> Pbool b
  | Pcast(ws,e) -> Pcast(ws, gsubst_e f e)
  | Pvar v -> f v
  | Pget (v,e) -> Pget(gsubst_vdest f v, gsubst_e f e)
  | Pload (ws, v, e) -> Pload(ws, gsubst_vdest f v, gsubst_e f e)
  | Pnot e -> Pnot(gsubst_e f e)
  | Papp2(o,e1,e2) -> Papp2 (o, gsubst_e f e1, gsubst_e f e2)

and gsubst_vdest f v =
  match f v with
  | Pvar v -> v
  | _      -> assert false

let gsubst_lval f lv =
  match lv with
  | Lnone i     -> Lnone i
  | Lvar v      -> Lvar (gsubst_vdest f v)
  | Lmem(w,v,e) -> Lmem(w, gsubst_vdest f v, gsubst_e f e)
  | Laset(v,e)  -> Laset(gsubst_vdest f v, gsubst_e f e)

let gsubst_lvals f = List.map (gsubst_lval f)
let gsubst_es f = List.map (gsubst_e f)

let rec gsubst_i f i =
  let i_desc =
    match i.i_desc with
    | Cblock c      -> Cblock (gsubst_c f c)
    | Cassgn(x,t,e) -> Cassgn(gsubst_lval f x, t, gsubst_e f e)
    | Copn(x,o,e)   -> Copn(gsubst_lvals f x, o, gsubst_es f e)
    | Cif(e,c1,c2)  -> Cif(gsubst_e f e, gsubst_c f c1, gsubst_c f c2)
    | Cfor(x,(d,e1,e2),c) ->
        Cfor(gsubst_vdest f x, (d, gsubst_e f e1, gsubst_e f e2), gsubst_c f c)
    | Cwhile(c, e, c') -> 
      Cwhile(gsubst_c f c, gsubst_e f e, gsubst_c f c')
    | Ccall(ii,x,fn,e) -> Ccall(ii, gsubst_lvals f x, fn, gsubst_es f e) in
  { i with i_desc }

and gsubst_c f c = List.map (gsubst_i f) c

let gsubst_func f fc =
  let dov v = L.unloc (gsubst_vdest f (L.mk_loc L._dummy v)) in
  { fc with
    f_args = List.map dov fc.f_args;
    f_body = gsubst_c f fc.f_body;
    f_ret  = List.map (gsubst_vdest f) fc.f_ret
  }

(* ---------------------------------------------------------------- *)

let psubst_ty f ty =
  match ty with
  | Bty _ -> ty
  | Arr(ty, e) -> Arr(ty, gsubst_e f e)

type psubst = pexpr Mv.t

let psubst_v subst =
  let subst = ref subst in
  let rec aux v =
    let v_ = v.L.pl_desc in
    let e = 
      try Mpv.find v_ !subst
      with Not_found ->
        assert (not (PV.is_glob v_));
        let ty = psubst_ty (aux) v_.v_ty in
        let v' = PV.mk v_.v_name v_.v_kind ty v_.v_dloc in
        let e = Pvar {v with L.pl_desc = v'} in
        subst := Mpv.add v_ e !subst;
        e in
    match e with
    | Pvar x -> Pvar {x with L.pl_loc = L.loc v}
    | _      -> e in

  aux

let psubst_prog (prog:'info pprog) =
  let subst = ref (Mpv.empty : pexpr Mpv.t) in
  let rec aux = function
    | [] -> []
    | MIparam(v,e) :: items ->
        let p = aux items in
        subst := Mpv.add v (gsubst_e (psubst_v !subst) e) !subst;
        p
    | MIfun fc :: items ->
        let p = aux items in
        let subst_v = psubst_v !subst in
        let dov v =
          L.unloc (gsubst_vdest subst_v (L.mk_loc L._dummy v)) in
        let fc = {
            fc with
            f_args = List.map dov fc.f_args;
            f_body = gsubst_c subst_v fc.f_body;
            f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret
          } in
        MIfun(fc)::p in
    aux prog

(* ---------------------------------------------------------------- *)
(* Simplify type                                                    *)

let int_of_op2 o i1 i2 =
  match o with
  | Oadd  -> B.add i1 i2
  | Omul  -> B.mul i1 i2
  | Osub  -> B.sub i1 i2
  | _     -> assert false

let rec int_of_expr e =
  match e with
  | Pconst i -> i
  | Papp2 (o, e1, e2) ->
      int_of_op2 o (int_of_expr e1) (int_of_expr e2)
  | Pbool _ | Pcast _ | Pvar _
  | Pget _ | Pload _ | Pnot _ -> assert false


let isubst_ty = function
  | Bty ty -> Bty ty
  | Arr(ty, e) -> Arr(ty, B.to_int (int_of_expr e))


let isubst_prog (prog:'info pprog) =

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
    | MIparam _ -> assert false
    | MIfun fc  ->
      let subst_v = isubst_v () in
      let dov v =
        L.unloc (gsubst_vdest subst_v (L.mk_loc L._dummy v)) in
      let fc = {
          fc with
          f_args = List.map dov fc.f_args;
          f_body = gsubst_c subst_v fc.f_body;
          f_ret  = List.map (gsubst_vdest subst_v) fc.f_ret
        } in
      fc in

  List.map isubst_item prog


(* ---------------------------------------------------------------- *)
(* Remove parameter from program definition                         *)

let remove_params (prog : 'info pprog) : 'info prog =
  isubst_prog (psubst_prog prog)



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
  gsubst_func subst_v fc


(* ---------------------------------------------------------------- *)
(* Perform a substitution of variable by variable                   *) 

type vsubst = var Mv.t 

let vsubst_v s v = try Mv.find v s with Not_found -> v

let vsubst_vi s v = {v with L.pl_desc = vsubst_v s (L.unloc v) }

let vsubst_ve s v = Pvar (vsubst_vi s v) 
  
let vsubst_e  s = gsubst_e  (vsubst_ve s)
let vsubst_es s = gsubst_es (vsubst_ve s) 

let vsubst_lval  s = gsubst_lval  (vsubst_ve s)
let vsubst_lvals s = gsubst_lvals (vsubst_ve s)

let vsubst_i s = gsubst_i (vsubst_ve s)
let vsubst_c s = gsubst_c (vsubst_ve s)

let vsubst_func s = gsubst_func (vsubst_ve s)

