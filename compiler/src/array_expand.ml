(* Replace register array by register *)
open Utils
open Prog

let check_not_pred pmsg pred msg v =
  if pred (L.unloc v)
  then hierror "%a: variable %a is %s (%s)"
      L.pp_loc (L.loc v)
      (Printer.pp_var ~debug:true) (L.unloc v)
      pmsg msg

let check_not_reg_arr = check_not_pred "an array" is_reg_arr

let get_reg tbl x i =
  match Hv.find tbl x with
  | r ->
     if i < Array.length r then r.(i)
     else hierror "get_reg: %a[%d] out of bounds" (Printer.pp_var ~debug:true) x i
  | exception Not_found ->
     hierror "get_reg: %a[%d] not found" (Printer.pp_var ~debug:true) x i

let get_reg_arr tbl v e =
  let v_ = L.unloc v in
  match e with
  | Pconst i ->
    begin
      let i = B.to_int i in
      try get_reg tbl v_ i
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
      V.mk (v.v_name ^ "#" ^ string_of_int i) (Reg Direct) ty v.v_dloc in
    let t = Array.init sz vi in
    Hv.add tbl v t in
  let vars = Sv.filter is_reg_arr (vars_fc fc) in
  Sv.iter init_var vars;
  tbl

let rec arrexp_e tbl e =
  match e with
  | Pconst _ | Pbool _ | Parr_init _ -> e
  | Pvar x -> check_not_reg_arr "Pvar" x.gv; e

  | Pget (aa, ws, x,e) ->
    if is_reg_arr (L.unloc x.gv) then
      let v = get_reg_arr tbl x.gv e in
      Pvar (gkvar (L.mk_loc (L.loc x.gv) v))
    else Pget(aa, ws, x, arrexp_e tbl e)
  | Psub(aa, ws, len, x, e) ->
    assert (not (is_reg_arr (L.unloc x.gv)));
    Psub(aa, ws, len, x, arrexp_e tbl e)
  | Pload(ws,x,e)  -> Pload(ws,x,arrexp_e tbl e)
  | Papp1 (o, e)   -> Papp1(o, arrexp_e tbl e)
  | Papp2(o,e1,e2) -> Papp2(o,arrexp_e tbl e1, arrexp_e tbl e2)
  | PappN (o, es) -> PappN (o, List.map (arrexp_e tbl) es)
  | Pif(ty, e,e1,e2)   -> Pif(ty, arrexp_e tbl e, arrexp_e tbl e1, arrexp_e tbl e2)

let arrexp_lv tbl lv =
  match lv with
  | Laset(aa, ws, x, e) ->
    if is_reg_arr (L.unloc x) then
      let v = get_reg_arr tbl x e in
      Lvar (L.mk_loc (L.loc x) v)
    else Laset(aa, ws, x, arrexp_e tbl e)
  | Lasub(aa, ws, len, x, e) ->
    assert (not (is_reg_arr (L.unloc x)));
    Lasub(aa, ws, len, x, arrexp_e tbl e)
  | Lvar x       -> check_not_reg_arr "Lvar" x; lv
  | Lnone _      -> lv
  | Lmem(ws,x,e) -> Lmem(ws,x,arrexp_e tbl e)

let arrexp_es  tbl = List.map (arrexp_e tbl)
let arrexp_lvs tbl = List.map (arrexp_lv tbl)

let arrexp_args tbl es =
  let es = List.fold_left (fun es e ->
               match e with
               | Pvar x when is_reg_arr (L.unloc x.gv) ->
                  begin match (L.unloc x.gv).v_ty with
                  | Arr (_ws, n) ->
                     let es = ref es in
                     for i = 0 to n - 1 do
                       let r = get_reg tbl (L.unloc x.gv) i in
                       es := Pvar (gkvar (L.mk_loc (L.loc x.gv) r)) :: !es
                     done;
                     !es
                  | _ -> assert false
                  end
               | _ -> e :: es
             ) [] es in
  List.rev es

let rec arrexp_i tbl i =
  let i_desc =
    match i.i_desc with
    | Cassgn(x, tg, ty, e) -> Cassgn(arrexp_lv tbl x, tg, ty, arrexp_e tbl e)
    | Copn(x,t,o,e)   -> Copn(arrexp_lvs tbl x, t, o, arrexp_es tbl e)
    | Cif(e,c1,c2)  -> Cif(arrexp_e tbl e, arrexp_c tbl c1, arrexp_c tbl c2)
    | Cfor(i,(d,e1,e2),c) ->
      Cfor(i, (d, arrexp_e tbl e1, arrexp_e tbl e2), arrexp_c tbl c)
    | Cwhile(a, c, e, c') ->
      Cwhile(a, arrexp_c tbl c, arrexp_e tbl e, arrexp_c tbl c')
    | Ccall(ii,x,f,e) -> Ccall(ii, arrexp_lvs tbl x, f, arrexp_args tbl e)
  in
  { i with i_desc }

and arrexp_c tbl c = List.map (arrexp_i tbl) c

(** Expands function arguments (types & names) *)
let arrexp_sig_args tbl (tys: int gty list) (xs : int gvar list) : int gty list * int gvar list =
  let tys, xs =
    List.fold_left2 (fun (tys, xs) ty x ->
        match ty with
        | Arr _ when x.v_kind = Reg Direct ->
           begin match x.v_ty with
           | Arr (ws, n) ->
              let ty = Bty (U ws) in
              let tys, xs = ref tys, ref xs in
              for i = 0 to n - 1 do
                let x = get_reg tbl x i in
                tys := ty :: !tys;
                xs := x :: !xs
              done;
              !tys, !xs
           | _ -> hierror "arrexp_sig_args: type error"
           end
        | _ -> (ty :: tys, x :: xs)
      ) ([], []) tys xs
  in
  List.rev tys, List.rev xs

let arrexp_func fc =
  List.iter (check_not_reg_arr "function return") fc.f_ret;
  let tbl = init_tbl fc in
  let f_tyin, f_args = arrexp_sig_args tbl fc.f_tyin fc.f_args in
  let f_body = arrexp_c tbl fc.f_body in
  { fc with f_tyin ; f_args ; f_body }

(* -------------------------------------------------------------- *)
(* Perform stack allocation                                       *)

(* The variables are allocated in decreasing order of (base) size;
   this ensures that the alignment constraints are satisfied. *)
(*
let is_stack_k_var pkind x = x.v_kind = Stack pkind 

let add_var tbl ws x = 
  if is_stack_k_var Direct x then 
    let ws' = Mv.find_default Wsize.U8 x tbl in
    if size_of_ws ws' <= size_of_ws ws then Mv.add x ws tbl
    else tbl 
  else tbl

let rec array_access_e tbl e = 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ | Pvar _ -> tbl
  | Pget(_, ws, x, e) -> array_access_e (add_var tbl ws (L.unloc x.gv)) e
  | Pload (_,_,e) | Papp1 (_,e) -> array_access_e tbl e 
  | Papp2(_,e1,e2) -> array_access_e (array_access_e tbl e1) e2
  | PappN (_,es) -> array_access_es tbl es
  | Pif(_, e1,e2,e3) -> array_access_es tbl [e1;e2;e3]

and array_access_es tbl es = List.fold_left array_access_e tbl es 

let array_access_lv tbl = function
 | Lnone _ | Lvar _ -> tbl
 | Lmem  (_,_,e) -> array_access_e tbl e
 | Laset (_, ws, x, e) -> array_access_e (add_var tbl ws (L.unloc x)) e

let array_access_lvs =  List.fold_left array_access_lv

let rec array_acces_i tbl i = 
  match i.i_desc with
  | Cassgn (x, _, _, e) -> array_access_lv (array_access_e tbl e) x
  | Copn(xs,_,_,es) | Ccall(_,xs,_,es) -> 
    array_access_lvs (array_access_es tbl es) xs
  | Cif(e, c1, c2) | Cwhile(_, c1, e, c2)  -> 
    array_access_c (array_access_c (array_access_e tbl e) c1) c2
  | Cfor(_,(_,e1,e2), c) ->
    array_access_c (array_access_e (array_access_e tbl e1) e2) c

and array_access_c tbl c = 
  List.fold_left array_acces_i tbl c

type param_info = { 
  pp_ptr      : var;
  pp_writable : bool;
  pp_align    : Wsize.wsize;
}

type ptr_kind =
  | Pstack of int * Wsize.wsize
  | Pregptr of var 
  | Pstkptr of int

let init_stk fc extra_vars =
  let fv = vars_fc fc in
  let vars = Sv.filter is_stack_var fv in
  let extra = Sv.of_list (Array.to_list extra_vars) in
  let vars' = Sv.union vars extra in
  let tbl = array_access_c Mv.empty fc.f_body in
  let get_size v =
    if is_stack_k_var Pointer v then 
      let s = size_of_ws U64 in v, Wsize.U64, s, s
    else
      match v.v_ty with
      | Bty (U ws)   -> let s = size_of_ws ws in v, ws, s, s
      | Arr (ws', n) -> 
        let ws = try Mv.find v tbl with Not_found -> assert false in
        v, ws, size_of_ws ws, arr_size ws' n
      | t -> 
        Format.eprintf "%a@." Printer.pp_ty t;
        assert false in
  let vars' = List.rev_map get_size (Sv.elements vars') in
  let cmp (_, _, s1, _) (_, _, s2, _) = s2 - s1 in
  let size = ref 0 in  
  (* FIXME: optimize this 
     if pos mod s <> 0 then a hole appear in the stack,
     in this case we can try to fill the hole with a variable 
     of a smaller size allowing to align the next pos
   *)
  let mk_pos v pos ws = 
    if is_stack_k_var Pointer v then Pstkptr pos
    else Pstack (pos,ws) in
  let init_var (v, ws, s, n) =
    let pos = !size in
    let pos = 
      if pos mod s = 0 then pos
      else (pos/s + 1) * s in
    size := pos + n;
    (v, mk_pos v pos ws) in

  let vars' = List.sort cmp vars' in
  let alloc = List.map init_var vars' in
  let find v = snd (List.find (fun (v',_) -> V.equal v v') alloc) in
  let extra_vars = Array.map find extra_vars in
  let isnot_extra (v,_) = not (Sv.mem v extra) in
  let alloc = List.filter isnot_extra alloc in
  let regp = Sv.filter (fun v -> v.v_kind = Reg Pointer) fv in
  let regp = 
    let mk v = 
      (v, Pregptr (V.mk v.v_name (Reg Direct) u64 v.v_dloc)) in
    List.map mk (Sv.elements regp) in
  (* --------------------- *)
  let do_param v = 
    if is_ptr v.v_kind then 
      let (ws,_) = array_kind v.v_ty in (* FIXME *)
      assert (is_reg_kind v.v_kind); (* FIXME *)
      let info = {
          pp_ptr      = V.mk v.v_name (Reg Direct) u64 v.v_dloc;
          pp_writable = true; (* FIXME *)
          pp_align    = ws; 
        } in 
      Some info
    else 
      None in
  let params = List.map do_param fc.f_args in
  let do_res v = 
    let x = L.unloc v in
    if is_ptr x.v_kind then
      let rec aux i l = 
        match l with
        | []      -> assert false (* FIXME *)
        | x' :: l -> if V.equal x x' then i else aux (i+1) l in
      Some (aux 0 fc.f_args) 
    else None in
  let results = List.map do_res fc.f_ret in
  params, results, regp @ alloc, !size, extra_vars

let vstack = rsp

let check_stack_var =
  check_not_pred "in stack" is_stack_var

let stk_alloc_func fc =
  List.iter (fun v -> check_stack_var "function argument" (L.mk_loc L._dummy v)) fc.f_args;
  List.iter (check_stack_var "function return") fc.f_ret;
  init_stk fc 

(* -------------------------------------------------------------- *)
(* Perform global allocation                                       *)

(* The variables are allocated in decreasing order of (base) size;
   this ensures that the alignment constraints are satisfied. *)

let add_gvar tbl ws x = 
  let ws' = Mv.find_default Wsize.U8 x tbl in
  if size_of_ws ws' <= size_of_ws ws then Mv.add x ws tbl
  else tbl 

let rec garray_access_e tbl e = 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ | Pvar _ -> tbl
  | Pget(_, ws , x, e) -> 
    let tbl = if is_gkvar x then tbl else add_gvar tbl ws (L.unloc x.gv) in
    garray_access_e tbl e
  | Pload (_,_,e) | Papp1 (_,e) -> garray_access_e tbl e 
  | Papp2(_,e1,e2) -> garray_access_e (garray_access_e tbl e1) e2
  | PappN (_,es) -> garray_access_es tbl es
  | Pif(_, e1,e2,e3) -> garray_access_es tbl [e1;e2;e3]

and garray_access_es tbl es = List.fold_left garray_access_e tbl es 

let rec garray_acces_i tbl i = 
  match i.i_desc with
  | Cassgn (_, _, _, e) -> garray_access_e tbl e
  | Copn(_,_,_,es) | Ccall(_,_,_,es) -> garray_access_es tbl es
  | Cif(e, c1, c2) | Cwhile(_, c1, e, c2)  -> 
    garray_access_c (garray_access_c (garray_access_e tbl e) c1) c2
  | Cfor(_,(_,e1,e2), c) ->
    garray_access_c (garray_access_e (garray_access_e tbl e1) e2) c

and garray_access_c tbl c = 
  List.fold_left garray_acces_i tbl c

let garray_access_f tbl fc = garray_access_c tbl (fc.f_body)
  
let init_glob (globs, funcs) =

  let vars = List.map fst globs in

  let add tbl x =
    let ws = 
      match x.v_ty with
      | Bty (U ws) -> ws
      | Arr (ws,_) -> ws
      | _          -> assert false in
    add_gvar tbl ws x in

  let tbl = List.fold_left add Mv.empty vars in

  let tbl = List.fold_left garray_access_f tbl funcs in

  let size v =
     match v.v_ty with
     | Bty (U ws)  -> let s = size_of_ws ws in v, ws, s, s
     | Arr (ws', n) -> 
       let ws = try Mv.find v tbl with Not_found -> assert false in
       v, ws, size_of_ws ws, arr_size ws' n
     | _            -> assert false in

  let vars = List.rev_map size vars in
  let cmp (_, _, s1, _) (_, _, s2, _) = s2 - s1 in

  let vars = List.sort cmp vars in 
  let size = ref 0 in
  let data = ref [] in
  let get x = 
    try List.assoc x globs with Not_found -> assert false in

  let init_var (v, ws, s, n) =
    let pos = !size in
    let pos = 
      if pos mod s = 0 then pos
      else 
        let new_pos = (pos/s + 1) * s in
        (* fill data with 0 *)
        for i = 0 to new_pos - pos - 1 do
          data := Word0.wrepr U8 (Conv.z_of_int 0) :: !data
        done;
        new_pos in
    (* fill data with the corresponding values *)
    begin match get v with
    | Global.Gword(ws, w) ->
      let w = Memory_model.LE.encode ws w in
      data := List.rev_append w !data 
    | Global.Garr(p, t) ->
      let ip = Conv.int_of_pos p in
      for i = 0 to ip - 1 do
        let w = 
          match Warray_.WArray.get p Warray_.AAdirect U8 t (Conv.z_of_int i) with
          | Ok w -> w
          | _    -> assert false in
        data := w :: !data
      done 
    end;
    size := pos + n;
    (v,(pos,ws)) in
  let alloc = List.map init_var vars in
  let data = List.rev !data in
  data, alloc
 *)
