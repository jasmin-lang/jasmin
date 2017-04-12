open Prog
module L = Location

let rec subst_e (f: pvar_i -> 'ty gexpr) e =
  match e with
  | Pconst c -> Pconst c
  | Pbool b  -> Pbool b
  | Pcast(ws,e) -> Pcast(ws, subst_e f e)
  | Pvar v -> f v
  | Pget (v,e) -> Pget(subst_vdest f v, subst_e f e)
  | Pload (ws, v, e) -> Pload(ws, subst_vdest f v, subst_e f e)
  | Pnot e -> Pnot(subst_e f e)
  | Papp2(o,e1,e2) -> Papp2 (o, subst_e f e1, subst_e f e2)

and subst_vdest f v = 
  match f v with
  | Pvar v -> v
  | _      -> assert false

let subst_lval f lv = 
  match lv with
  | Lnone i     -> Lnone i
  | Lvar v      -> Lvar (subst_vdest f v)
  | Lmem(w,v,e) -> Lmem(w, subst_vdest f v, subst_e f e)
  | Laset(v,e)  -> Laset(subst_vdest f v, subst_e f e)

let subst_lvals f = List.map (subst_lval f)
let subst_es f = List.map (subst_e f) 

let rec subst_i f i =
  let i_desc = 
    match i.i_desc with
    | Cblock c      -> Cblock (subst_c f c)
    | Cassgn(x,t,e) -> Cassgn(subst_lval f x, t, subst_e f e)
    | Copn(x,o,e)   -> Copn(subst_lvals f x, o, subst_es f e)
    | Cif(e,c1,c2)  -> Cif(subst_e f e, subst_c f c1, subst_c f c2)
    | Cfor(x,(d,e1,e2),c) -> 
        Cfor(subst_vdest f x, (d, subst_e f e1, subst_e f e2), subst_c f c)
    | Cwhile(e, c)  -> Cwhile(subst_e f e, subst_c f c)
    | Ccall(ii,x,fn,e) -> Ccall(ii,subst_lvals f x, fn, subst_es f e) in
  { i with i_desc }

and subst_c f c = List.map (subst_i f) c

(* ---------------------------------------------------------------- *)

let psubst_ty f ty =
  match ty with
  | Bty _ -> ty
  | Arr(ty, e) -> Arr(ty, subst_e f e)
    
type psubst = pexpr Mv.t

let psubst_v subst =
  let subst = ref subst in
  let rec aux v =
    let v_ = v.L.pl_desc in
      try Mpv.find v_ !subst 
      with Not_found -> 
        assert (not (PV.is_glob v_));
        let ty = psubst_ty (aux) v_.v_ty in
        let e = 
          Pvar {v with L.pl_desc = PV.mk v_.v_name v_.v_kind ty v_.v_dloc } in
        subst := Mpv.add v_ e !subst;
        e in
    aux 

let psubst_prog (prog:'info pprog) = 
  let subst = ref (Mpv.empty : pexpr Mpv.t) in  
  let rec aux = function
    | [] -> []
    | MIparam(v,e) :: items -> 
        let p = aux items in
        subst := Mpv.add v (subst_e (psubst_v !subst) e) !subst;
        p
    | MIfun fc :: items ->
        let p = aux items in
        let subst_v = psubst_v !subst in
        let dov v =
          L.unloc (subst_vdest subst_v (L.mk_loc L._dummy v)) in
        let fc = { 
            fc with
            f_args = List.map dov fc.f_args;
            f_body = subst_c subst_v fc.f_body;
            f_ret  = List.map (subst_vdest subst_v) fc.f_ret 
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
        L.unloc (subst_vdest subst_v (L.mk_loc L._dummy v)) in
      let fc = { 
          fc with
          f_args = List.map dov fc.f_args;
          f_body = subst_c subst_v fc.f_body;
          f_ret  = List.map (subst_vdest subst_v) fc.f_ret 
        } in
      fc in

  List.map isubst_item prog

 
(* ---------------------------------------------------------------- *)
(* Remove parameter from program definition                         *)

let remove_params (prog : 'info pprog) : 'info prog = 
  isubst_prog (psubst_prog prog)


  
