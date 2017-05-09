(* Replace register array by register *)
open Prog



let check_not_reg_arr v =
   assert (not (is_reg_arr (L.unloc v)))
   (* FIXME: raise an error message, v contain the location *)

let get_reg_arr tbl v e =
  let v_ = L.unloc v in
  match e with
  | Pconst i ->
    begin
      let i = B.to_int i in
      try (Hv.find tbl v_).(i)
      with Not_found -> assert false
    end
  | _        -> assert false
    (* FIXME: raise an error message, v contain the location *)

let init_tbl fc =
  let tbl = Hv.create 107 in
  let init_var v =
    let ws, sz = array_kind v.v_ty in
    let ty = Bty (U ws) in
    let vi i =
      V.mk (v.v_name ^ "#" ^ string_of_int i) Reg ty v.v_dloc in
    let t = Array.init sz vi in
    Hv.add tbl v t in
  let vars = Sv.filter is_reg_arr (vars_fc fc) in
  Sv.iter init_var vars;
  tbl

let rec arrexp_e tbl e =
  match e with
  | Pconst _ | Pbool _ -> e
  | Pvar x -> check_not_reg_arr x; e

  | Pget (x,e) ->
    if is_reg_arr (L.unloc x) then
      let v = get_reg_arr tbl x e in
      Pvar (L.mk_loc (L.loc x) v)
    else Pget(x, arrexp_e tbl e)

  | Pcast(ws,e)    -> Pcast(ws, arrexp_e tbl e)
  | Pload(ws,x,e)  -> Pload(ws,x,arrexp_e tbl e)
  | Papp1 (o, e)   -> Papp1(o, arrexp_e tbl e)
  | Papp2(o,e1,e2) -> Papp2(o,arrexp_e tbl e1, arrexp_e tbl e2)
  | Pif(e,e1,e2)   -> Pif(arrexp_e tbl e, arrexp_e tbl e1, arrexp_e tbl e2)

let arrexp_lv tbl lv =
  match lv with
  | Laset(x,e) ->
    if is_reg_arr (L.unloc x) then
      let v = get_reg_arr tbl x e in
      Lvar (L.mk_loc (L.loc x) v)
    else Laset(x, arrexp_e tbl e)
  | Lvar x       -> check_not_reg_arr x; lv
  | Lnone _      -> lv
  | Lmem(ws,x,e) -> Lmem(ws,x,arrexp_e tbl e)

let arrexp_es  tbl = List.map (arrexp_e tbl)
let arrexp_lvs tbl = List.map (arrexp_lv tbl)

let rec arrexp_i tbl i =
  let i_desc =
    match i.i_desc with
    | Cblock c -> Cblock (arrexp_c tbl c)
    | Cassgn(x,t,e) -> Cassgn(arrexp_lv tbl x, t, arrexp_e tbl e)
    | Copn(x,o,e)   -> Copn(arrexp_lvs tbl x, o, arrexp_es tbl e)
    | Cif(e,c1,c2)  -> Cif(arrexp_e tbl e, arrexp_c tbl c1, arrexp_c tbl c2)
    | Cfor(i,(d,e1,e2),c) ->
      Cfor(i, (d, arrexp_e tbl e1, arrexp_e tbl e2), arrexp_c tbl c)
    | Cwhile(c, e, c') -> 
      Cwhile(arrexp_c tbl c, arrexp_e tbl e, arrexp_c tbl c')
    | Ccall(ii,x,f,e) -> Ccall(ii, arrexp_lvs tbl x, f, arrexp_es tbl e)
  in
  { i with i_desc }

and arrexp_c tbl c = List.map (arrexp_i tbl) c

let arrexp_func fc =
  List.iter (fun v -> check_not_reg_arr (L.mk_loc L._dummy v)) fc.f_args;
  List.iter check_not_reg_arr fc.f_ret;
  let tbl = init_tbl fc in
  { fc with f_body = arrexp_c tbl fc.f_body }

let arrexp_prog prog = List.map arrexp_func prog

(* -------------------------------------------------------------- *)
(* Perform stack allocation                                       *)

let init_stk fc =
  let vars = Sv.elements (Sv.filter is_stack_var (vars_fc fc)) in
  (* FIXME: For the moment we assume that all variable are 64 bits *)
  let size = ref 0 in
  let tbl = Hv.create 107 in
  let init_var v =
    let n =
      match v.v_ty with
      | Bty (U W64)  -> size_of_ws W64
      | Arr (W64, n) -> n * size_of_ws W64
      | _            -> assert false in
    let pos = !size in
    let bpos = B.of_int pos in
    Hv.add tbl v bpos;
    size := pos + n;
    (v,pos) in
  let alloc = List.map init_var vars in
  alloc, !size, tbl

let load_stack ws loc e =
   Pload (ws, L.mk_loc loc vstack, cast64 e)

let store_stack ws loc e =
   Lmem (ws, L.mk_loc loc vstack, cast64 e)

let rec astk_e tbl e =
  match e with
  | Pconst _ | Pbool _ -> e

  | Pvar x ->
    let x_ = L.unloc x in
    let loc = L.loc x in
    if is_stack_var x_ then
      let _ = assert (not (is_ty_arr x_.v_ty)) in (* FIXME: ERROR MSG *)
      let ws = ws_of_ty x_.v_ty in
      load_stack ws loc (cnst (Hv.find tbl x_))
    else e

  | Pget (x, e) when is_stack_var (L.unloc x) ->
    let x_ = L.unloc x in
    let loc = L.loc x in
    let ws, _n = array_kind x_.v_ty in
    let ipos = cnst (Hv.find tbl x_) in
    load_stack ws loc (ipos ++ (icnst (size_of_ws ws) ** e))

  | Pget _ -> assert false (* FIXME: ERROR MSG *)

  | Pcast(ws,e)    -> Pcast(ws, astk_e tbl e)
  | Pload(ws,x,e)  -> Pload(ws,x, astk_e tbl e)
  | Papp1(o,e)     -> Papp1(o, astk_e tbl e)
  | Papp2(o,e1,e2) -> Papp2(o, astk_e tbl e1, astk_e tbl e2)
  | Pif(e,e1,e2)   -> Pif(astk_e tbl e, astk_e tbl e1, astk_e tbl e2)

let astk_lv tbl lv =
  match lv with
  | Laset(x,e) when is_stack_var (L.unloc x) ->
    let x_ = L.unloc x in
    let loc = L.loc x in
    let ws, _n = array_kind x_.v_ty in
    let ipos = cnst (Hv.find tbl x_) in
    store_stack ws loc (ipos ++ (icnst (size_of_ws ws) ** e))

  | Laset _ ->  assert false (* FIXME: ERROR MSG *)

  | Lvar x       ->
    let x_ = L.unloc x in
    let loc = L.loc x in
    if is_stack_var x_ then
      let _ = assert (not (is_ty_arr x_.v_ty)) in (* FIXME: ERROR MSG *)
      let ws = ws_of_ty x_.v_ty in
      store_stack ws loc (cnst (Hv.find tbl x_))
    else lv

  | Lnone _      -> lv

  | Lmem(ws,x,e) -> Lmem(ws,x,astk_e tbl e)


let astk_es  tbl = List.map (astk_e tbl)
let astk_lvs tbl = List.map (astk_lv tbl)

let rec astk_i tbl i =
  let i_desc =
    match i.i_desc with
    | Cblock c        -> Cblock (astk_c tbl c)
    | Cassgn(x,t,e)   -> Cassgn(astk_lv tbl x, t, astk_e tbl e)
    | Copn(x,o,e)     -> Copn(astk_lvs tbl x, o, astk_es tbl e)
    | Cif(e,c1,c2)    -> Cif(astk_e tbl e, astk_c tbl c1, astk_c tbl c2)
    | Cfor(i,(d,e1,e2),c) ->
      Cfor(i, (d, astk_e tbl e1, astk_e tbl e2), astk_c tbl c)
    | Cwhile(c, e, c') -> Cwhile(astk_c tbl c, astk_e tbl e, astk_c tbl c')
    | Ccall(ii,x,f,e) -> Ccall(ii, astk_lvs tbl x, f, astk_es tbl e)
  in
  { i with i_desc }

and astk_c tbl c = List.map (astk_i tbl) c

let check_stack_var v =
  assert (not (is_stack_var (L.unloc v)))

let stk_alloc_func fc =
  List.iter (fun v -> check_stack_var (L.mk_loc L._dummy v)) fc.f_args;
  List.iter check_stack_var fc.f_ret;
  let alloc, sz, tbl = init_stk fc in
  alloc, sz, { fc with f_body = astk_c tbl fc.f_body }

let stk_alloc_prog prog = List.map stk_alloc_func prog
