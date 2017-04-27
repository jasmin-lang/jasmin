open BinInt
open BinNums
open Datatypes
open Eqtype
open Expr
open Seq
open Utils0
open Var0

(** val snot : pexpr -> pexpr **)

let snot e = match e with
| Pbool b -> Pbool (negb b)
| Pnot e0 -> e0
| _ -> Pnot e

(** val sand : pexpr -> pexpr -> pexpr **)

let sand e1 e2 =
  match is_bool e1 with
  | Some b -> if b then e2 else Pbool false
  | None ->
    (match is_bool e2 with
     | Some b -> if b then e1 else Pbool false
     | None -> Papp2 (Oand, e1, e2))

(** val sor : pexpr -> pexpr -> pexpr **)

let sor e1 e2 =
  match is_bool e1 with
  | Some b -> if b then Pbool true else e2
  | None ->
    (match is_bool e2 with
     | Some b -> if b then Pbool true else e1
     | None -> Papp2 (Oor, e1, e2))

(** val sadd : pexpr -> pexpr -> pexpr **)

let sadd e1 e2 =
  match is_const e1 with
  | Some n ->
    (match is_const e2 with
     | Some n0 -> Pconst (Z.add n n0)
     | None ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic Z0)
       then e2
       else Papp2 (Oadd, e1, e2))
  | None ->
    (match is_const e2 with
     | Some n ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic Z0)
       then e1
       else Papp2 (Oadd, e1, e2)
     | None -> Papp2 (Oadd, e1, e2))

(** val ssub : pexpr -> pexpr -> pexpr **)

let ssub e1 e2 =
  match is_const e1 with
  | Some n1 ->
    (match is_const e2 with
     | Some n -> Pconst (Z.sub n1 n)
     | None -> Papp2 (Osub, e1, e2))
  | None ->
    (match is_const e2 with
     | Some n ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic Z0)
       then e1
       else Papp2 (Osub, e1, e2)
     | None -> Papp2 (Osub, e1, e2))

(** val smul : pexpr -> pexpr -> pexpr **)

let smul e1 e2 =
  match is_const e1 with
  | Some n ->
    (match is_const e2 with
     | Some n0 -> Pconst (Z.mul n n0)
     | None ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic Z0)
       then Pconst Z0
       else if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic (Zpos Coq_xH))
            then e2
            else Papp2 (Omul, e1, e2))
  | None ->
    (match is_const e2 with
     | Some n ->
       if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic Z0)
       then Pconst Z0
       else if eq_op coq_Z_eqType (Obj.magic n) (Obj.magic (Zpos Coq_xH))
            then e1
            else Papp2 (Omul, e1, e2)
     | None -> Papp2 (Omul, e1, e2))

(** val s_eq : pexpr -> pexpr -> pexpr **)

let s_eq e1 e2 =
  match is_const e1 with
  | Some n1 ->
    (match is_const e2 with
     | Some n2 -> Pbool (eq_op coq_Z_eqType (Obj.magic n1) (Obj.magic n2))
     | None ->
       if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
       then Pbool true
       else Papp2 (Oeq, e1, e2))
  | None ->
    if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
    then Pbool true
    else Papp2 (Oeq, e1, e2)

(** val sneq : pexpr -> pexpr -> pexpr **)

let sneq e1 e2 =
  match is_const e1 with
  | Some n1 ->
    (match is_const e2 with
     | Some n2 ->
       Pbool (negb (eq_op coq_Z_eqType (Obj.magic n1) (Obj.magic n2)))
     | None ->
       if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
       then Pbool false
       else Papp2 (Oneq, e1, e2))
  | None ->
    if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
    then Pbool false
    else Papp2 (Oneq, e1, e2)

(** val slt : pexpr -> pexpr -> pexpr **)

let slt e1 e2 =
  match is_const e1 with
  | Some n1 ->
    (match is_const e2 with
     | Some n2 -> Pbool (Z.ltb n1 n2)
     | None ->
       if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
       then Pbool false
       else Papp2 (Olt, e1, e2))
  | None ->
    if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
    then Pbool false
    else Papp2 (Olt, e1, e2)

(** val sle : pexpr -> pexpr -> pexpr **)

let sle e1 e2 =
  match is_const e1 with
  | Some n1 ->
    (match is_const e2 with
     | Some n2 -> Pbool (Z.leb n1 n2)
     | None ->
       if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
       then Pbool true
       else Papp2 (Ole, e1, e2))
  | None ->
    if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
    then Pbool true
    else Papp2 (Ole, e1, e2)

(** val sgt : pexpr -> pexpr -> pexpr **)

let sgt e1 e2 =
  match is_const e1 with
  | Some n1 ->
    (match is_const e2 with
     | Some n2 -> Pbool (Z.gtb n1 n2)
     | None ->
       if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
       then Pbool false
       else Papp2 (Ogt, e1, e2))
  | None ->
    if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
    then Pbool false
    else Papp2 (Ogt, e1, e2)

(** val sge : pexpr -> pexpr -> pexpr **)

let sge e1 e2 =
  match is_const e1 with
  | Some n1 ->
    (match is_const e2 with
     | Some n2 -> Pbool (Z.geb n1 n2)
     | None ->
       if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
       then Pbool true
       else Papp2 (Oge, e1, e2))
  | None ->
    if eq_op Eq_pexpr.Exports.eqType (Obj.magic e1) (Obj.magic e2)
    then Pbool true
    else Papp2 (Oge, e1, e2)

(** val s_op2 : sop2 -> pexpr -> pexpr -> pexpr **)

let s_op2 o e1 e2 =
  match o with
  | Oand -> sand e1 e2
  | Oor -> sor e1 e2
  | Oadd -> sadd e1 e2
  | Omul -> smul e1 e2
  | Osub -> ssub e1 e2
  | Oeq -> s_eq e1 e2
  | Oneq -> sneq e1 e2
  | Olt -> slt e1 e2
  | Ole -> sle e1 e2
  | Ogt -> sgt e1 e2
  | Oge -> sge e1 e2

(** val const_prop_e : coq_Z Mvar.t -> pexpr -> pexpr **)

let rec const_prop_e m e = match e with
| Pcast e0 -> Pcast (const_prop_e m e0)
| Pvar x ->
  (match Mvar.get m (Obj.magic v_var x) with
   | Some n -> Pconst n
   | None -> e)
| Pget (x, e0) -> Pget (x, (const_prop_e m e0))
| Pload (x, e0) -> Pload (x, (const_prop_e m e0))
| Pnot e0 -> snot e0
| Papp2 (o, e1, e2) -> s_op2 o (const_prop_e m e1) (const_prop_e m e2)
| _ -> e

(** val empty_cpm : coq_Z Mvar.t **)

let empty_cpm =
  Mvar.empty

(** val merge_cpm : coq_Z Mvar.t -> coq_Z Mvar.t -> coq_Z Mvar.t **)

let merge_cpm =
  Mvar.map2 (fun _ o1 o2 ->
    match o1 with
    | Some n1 ->
      (match o2 with
       | Some n2 ->
         if eq_op coq_Z_eqType (Obj.magic n1) (Obj.magic n2)
         then Some n1
         else None
       | None -> None)
    | None -> None)

(** val remove_cpm : coq_Z Mvar.t -> Sv.t -> coq_Z Mvar.t **)

let remove_cpm m s =
  Sv.fold (fun x m0 -> Mvar.remove m0 x) s m

(** val const_prop_rv : coq_Z Mvar.t -> lval -> coq_Z Mvar.t * lval **)

let const_prop_rv m rv = match rv with
| Lnone _ -> (m, rv)
| Lvar x -> ((Mvar.remove m (Obj.magic v_var x)), rv)
| Lmem (x, e) -> (m, (Lmem (x, (const_prop_e m e))))
| Laset (x, e) ->
  ((Mvar.remove m (Obj.magic v_var x)), (Laset (x, (const_prop_e m e))))

(** val const_prop_rvs :
    coq_Z Mvar.t -> lval list -> coq_Z Mvar.t * lval list **)

let rec const_prop_rvs m = function
| [] -> (m, [])
| rv :: rvs0 ->
  let (m0, rv0) = const_prop_rv m rv in
  let (m1, rvs1) = const_prop_rvs m0 rvs0 in (m1, (rv0 :: rvs1))

(** val add_cpm :
    coq_Z Mvar.t -> lval -> assgn_tag -> pexpr -> coq_Z Mvar.t **)

let add_cpm m rv tag e =
  match rv with
  | Lvar x ->
    (match tag with
     | AT_inline ->
       (match is_const e with
        | Some n -> Mvar.set m (Obj.magic v_var x) n
        | None -> m)
     | _ -> m)
  | _ -> m

(** val const_prop :
    (coq_Z Mvar.t -> instr -> coq_Z Mvar.t * instr list) -> coq_Z Mvar.t ->
    instr list -> coq_Z Mvar.t * instr list **)

let rec const_prop const_prop_i0 m = function
| [] -> (m, [])
| i :: c0 ->
  let (m0, ic) = const_prop_i0 m i in
  let (m1, c1) = const_prop const_prop_i0 m0 c0 in (m1, (cat ic c1))

(** val const_prop_ir :
    coq_Z Mvar.t -> instr_info -> instr_r -> coq_Z Mvar.t * instr list **)

let rec const_prop_ir m ii ir = match ir with
| Cassgn (x, tag, e) ->
  let e0 = const_prop_e m e in
  let (m0, x0) = const_prop_rv m x in
  let m1 = add_cpm m0 x0 tag e0 in
  (m1, ((MkI (ii, (Cassgn (x0, tag, e0)))) :: []))
| Copn (xs, o, es) ->
  let es0 = map (const_prop_e m) es in
  let (m0, xs0) = const_prop_rvs m xs in
  (m0, ((MkI (ii, (Copn (xs0, o, es0)))) :: []))
| Cif (b, c1, c2) ->
  let b0 = const_prop_e m b in
  (match is_bool b0 with
   | Some b1 -> let c = if b1 then c1 else c2 in const_prop const_prop_i m c
   | None ->
     let (m1, c3) = const_prop const_prop_i m c1 in
     let (m2, c4) = const_prop const_prop_i m c2 in
     ((merge_cpm m1 m2), ((MkI (ii, (Cif (b0, c3, c4)))) :: [])))
| Cfor (x, r, c) ->
  let (p, e2) = r in
  let (dir, e1) = p in
  let e3 = const_prop_e m e1 in
  let e4 = const_prop_e m e2 in
  let m0 = remove_cpm m (write_i ir) in
  let (_, c0) = const_prop const_prop_i m0 c in
  (m0, ((MkI (ii, (Cfor (x, ((dir, e3), e4), c0)))) :: []))
| Cwhile (e, c) ->
  let m0 = remove_cpm m (write_i ir) in
  let (_, c0) = const_prop const_prop_i m0 c in
  (m0, ((MkI (ii, (Cwhile ((const_prop_e m0 e), c0)))) :: []))
| Ccall (fi, xs, f, es) ->
  let es0 = map (const_prop_e m) es in
  let (m0, xs0) = const_prop_rvs m xs in
  (m0, ((MkI (ii, (Ccall (fi, xs0, f, es0)))) :: []))

(** val const_prop_i : coq_Z Mvar.t -> instr -> coq_Z Mvar.t * instr list **)

and const_prop_i m = function
| MkI (ii, ir) -> const_prop_ir m ii ir

(** val const_prop_fun : fundef -> fundef **)

let const_prop_fun f =
  let { f_iinfo = ii; f_params = p; f_body = c; f_res = r } = f in
  let (_, c0) = const_prop const_prop_i empty_cpm c in
  { f_iinfo = ii; f_params = p; f_body = c0; f_res = r }

(** val const_prop_prog : prog -> prog **)

let const_prop_prog p =
  map_prog const_prop_fun p
