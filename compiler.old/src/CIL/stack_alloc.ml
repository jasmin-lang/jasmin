open Ascii
open BinInt
open BinNums
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Seq
open Type
open Utils0
open Var0

module S =
 struct
  type sfundef = { sf_iinfo : instr_info; sf_stk_sz : coq_Z;
                   sf_stk_id : Equality.sort; sf_params : var_i list;
                   sf_body : instr list; sf_res : var_i list }

  (** val sf_stk_sz : sfundef -> coq_Z **)

  let sf_stk_sz x = x.sf_stk_sz

  (** val sf_stk_id : sfundef -> Equality.sort **)

  let sf_stk_id x = x.sf_stk_id

  (** val sf_params : sfundef -> var_i list **)

  let sf_params x = x.sf_params

  (** val sf_body : sfundef -> instr list **)

  let sf_body x = x.sf_body

  (** val sf_res : sfundef -> var_i list **)

  let sf_res x = x.sf_res

  type sprog = (funname * sfundef) list
 end

type map = coq_Z Mvar.t * Equality.sort

(** val size_of : stype -> coq_Z cexec **)

let size_of = function
| Coq_sarr n -> Ok (Zpos n)
| Coq_sword -> Ok (Zpos Coq_xH)
| _ ->
  cerror (Cerr_stk_alloc (String ((Ascii (true, true, false, false, true,
    true, true, false)), (String ((Ascii (true, false, false, true, false,
    true, true, false)), (String ((Ascii (false, true, false, true, true,
    true, true, false)), (String ((Ascii (true, false, true, false, false,
    true, true, false)), (String ((Ascii (true, true, true, true, true,
    false, true, false)), (String ((Ascii (true, true, true, true, false,
    true, true, false)), (String ((Ascii (false, true, true, false, false,
    true, true, false)), EmptyString)))))))))))))))

(** val init_map :
    coq_Z -> Equality.sort -> (Var.var * coq_Z) list -> (error_msg, coq_Z
    Mvar.t * Equality.sort) result **)

let init_map sz nstk l =
  let add0 = fun vp mp ->
    if Z.leb (snd mp) (snd vp)
    then Result.bind (fun s ->
           cok ((Mvar.set (fst mp) (fst (Obj.magic vp)) (snd vp)),
             (Z.add (snd vp) s))) (size_of (fst vp).Var.vtype)
    else cerror (Cerr_stk_alloc (String ((Ascii (true, true, true, true,
           false, true, true, false)), (String ((Ascii (false, true, true,
           false, true, true, true, false)), (String ((Ascii (true, false,
           true, false, false, true, true, false)), (String ((Ascii (false,
           true, false, false, true, true, true, false)), (String ((Ascii
           (false, false, true, true, false, true, true, false)), (String
           ((Ascii (true, false, false, false, false, true, true, false)),
           (String ((Ascii (false, false, false, false, true, true, true,
           false)), EmptyString)))))))))))))))
  in
  Result.bind (fun mp ->
    if Z.leb (snd mp) sz
    then cok ((fst mp), nstk)
    else cerror (Cerr_stk_alloc (String ((Ascii (true, true, false, false,
           true, true, true, false)), (String ((Ascii (false, false, true,
           false, true, true, true, false)), (String ((Ascii (true, false,
           false, false, false, true, true, false)), (String ((Ascii (true,
           true, false, false, false, true, true, false)), (String ((Ascii
           (true, true, false, true, false, true, true, false)), (String
           ((Ascii (false, false, false, false, false, true, false, false)),
           (String ((Ascii (true, true, false, false, true, true, true,
           false)), (String ((Ascii (true, false, false, true, false, true,
           true, false)), (String ((Ascii (false, true, false, true, true,
           true, true, false)), (String ((Ascii (true, false, true, false,
           false, true, true, false)), EmptyString))))))))))))))))))))))
    (foldM add0 (Mvar.empty, Z0) l)

(** val is_in_stk : map -> Var.var -> bool **)

let is_in_stk m x =
  match Mvar.get (fst m) (Obj.magic x) with
  | Some _ -> true
  | None -> false

(** val vstk : map -> Var.var **)

let vstk m =
  { Var.vtype = Coq_sword; Var.vname = (snd m) }

(** val is_vstk : map -> Var.var -> bool **)

let is_vstk m x =
  eq_op Var.var_eqType (Obj.magic x) (Obj.magic vstk m)

(** val check_var : map -> var_i -> var_i -> bool **)

let check_var m x1 x2 =
  (&&)
    ((&&) (negb (is_in_stk m x1.v_var))
      (eq_op Var.var_eqType (Obj.magic v_var x1) (Obj.magic v_var x2)))
    (negb (is_vstk m x1.v_var))

(** val check_var_stk : map -> var_i -> var_i -> pexpr -> bool **)

let check_var_stk m x1 x2 e2 =
  (&&)
    ((&&) (is_vstk m x2.v_var)
      (eq_op stype_eqType (Obj.magic Var.vtype x1.v_var)
        (Obj.magic Coq_sword)))
    (match Mvar.get (fst m) (Obj.magic v_var x1) with
     | Some ofs ->
       eq_op Eq_pexpr.Exports.eqType (Obj.magic e2)
         (Obj.magic (Pcast (Pconst ofs)))
     | None -> false)

(** val is_arr_type : stype -> bool **)

let is_arr_type = function
| Coq_sarr _ -> true
| _ -> false

(** val check_arr_stk' :
    (map -> pexpr -> pexpr -> bool) -> map -> var_i -> pexpr -> var_i ->
    pexpr -> bool **)

let check_arr_stk' check_e0 m x1 e1 x2 e2 =
  (&&) ((&&) (is_vstk m x2.v_var) (is_arr_type x1.v_var.Var.vtype))
    (match Mvar.get (fst m) (Obj.magic v_var x1) with
     | Some ofs ->
       (||)
         ((||)
           (match e2 with
            | Pcast p ->
              (match p with
               | Papp2 (s, p0, e2') ->
                 (match s with
                  | Oadd ->
                    (match p0 with
                     | Pconst ofs' ->
                       (&&)
                         (eq_op coq_Z_eqType (Obj.magic ofs)
                           (Obj.magic ofs')) (check_e0 m e1 e2')
                     | _ -> false)
                  | _ -> false)
               | _ -> false)
            | _ -> false)
           (match e2 with
            | Pcast p ->
              (match p with
               | Papp2 (s, e2', p0) ->
                 (match s with
                  | Oadd ->
                    (match p0 with
                     | Pconst ofs' ->
                       (&&)
                         (eq_op coq_Z_eqType (Obj.magic ofs)
                           (Obj.magic ofs')) (check_e0 m e1 e2')
                     | _ -> false)
                  | _ -> false)
               | _ -> false)
            | _ -> false))
         (match e1 with
          | Pconst n ->
            eq_op Eq_pexpr.Exports.eqType (Obj.magic e2)
              (Obj.magic (Pcast (Pconst (Z.add ofs n))))
          | _ -> false)
     | None -> false)

(** val check_e : map -> pexpr -> pexpr -> bool **)

let rec check_e m e1 e2 =
  match e1 with
  | Pconst n1 ->
    (match e2 with
     | Pconst n2 -> eq_op coq_Z_eqType (Obj.magic n1) (Obj.magic n2)
     | _ -> false)
  | Pbool b1 ->
    (match e2 with
     | Pbool b2 -> eq_op bool_eqType (Obj.magic b1) (Obj.magic b2)
     | _ -> false)
  | Pcast e3 ->
    (match e2 with
     | Pcast e4 -> check_e m e3 e4
     | _ -> false)
  | Pvar x1 ->
    (match e2 with
     | Pvar x2 -> check_var m x1 x2
     | Pload (x2, e3) -> check_var_stk m x1 x2 e3
     | _ -> false)
  | Pget (x1, e3) ->
    (match e2 with
     | Pget (x2, e4) -> (&&) (check_var m x1 x2) (check_e m e3 e4)
     | Pload (x2, e4) -> check_arr_stk' check_e m x1 e3 x2 e4
     | _ -> false)
  | Pload (x1, e3) ->
    (match e2 with
     | Pload (x2, e4) -> (&&) (check_var m x1 x2) (check_e m e3 e4)
     | _ -> false)
  | Pnot e3 ->
    (match e2 with
     | Pnot e4 -> check_e m e3 e4
     | _ -> false)
  | Papp2 (o1, e11, e12) ->
    (match e2 with
     | Papp2 (o2, e21, e22) ->
       (&&)
         ((&&) (eq_op sop2_eqType (Obj.magic o1) (Obj.magic o2))
           (check_e m e11 e21)) (check_e m e12 e22)
     | _ -> false)

(** val check_arr_stk : map -> var_i -> pexpr -> var_i -> pexpr -> bool **)

let check_arr_stk =
  check_arr_stk' check_e

(** val check_lval : map -> lval -> lval -> bool **)

let check_lval m r1 r2 =
  match r1 with
  | Lnone _ ->
    (match r2 with
     | Lnone _ -> true
     | _ -> false)
  | Lvar x1 ->
    (match r2 with
     | Lvar x2 -> check_var m x1 x2
     | Lmem (x2, e2) -> check_var_stk m x1 x2 e2
     | _ -> false)
  | Lmem (x1, e1) ->
    (match r2 with
     | Lmem (x2, e2) -> (&&) (check_var m x1 x2) (check_e m e1 e2)
     | _ -> false)
  | Laset (x1, e1) ->
    (match r2 with
     | Lmem (x2, e2) -> check_arr_stk m x1 e1 x2 e2
     | Laset (x2, e2) -> (&&) (check_var m x1 x2) (check_e m e1 e2)
     | _ -> false)

(** val check_i : map -> instr -> instr -> bool **)

let rec check_i m i1 i2 =
  let MkI (_, ir1) = i1 in
  let MkI (_, ir2) = i2 in
  (match ir1 with
   | Cassgn (r1, _, e1) ->
     (match ir2 with
      | Cassgn (r2, _, e2) -> (&&) (check_lval m r1 r2) (check_e m e1 e2)
      | _ -> false)
   | Copn (rs1, o1, e1) ->
     (match ir2 with
      | Copn (rs2, o2, e2) ->
        (&&)
          ((&&) (all2 (check_lval m) rs1 rs2)
            (eq_op sopn_eqType (Obj.magic o1) (Obj.magic o2)))
          (all2 (check_e m) e1 e2)
      | _ -> false)
   | Cif (e1, c1, c1') ->
     (match ir2 with
      | Cif (e2, c2, c2') ->
        (&&) ((&&) (check_e m e1 e2) (all2 (check_i m) c1 c2))
          (all2 (check_i m) c1' c2')
      | _ -> false)
   | Cwhile (e1, c1) ->
     (match ir2 with
      | Cwhile (e2, c2) -> (&&) (check_e m e1 e2) (all2 (check_i m) c1 c2)
      | _ -> false)
   | _ -> false)

(** val check_fd : (Var.var * coq_Z) list -> fundef -> S.sfundef -> bool **)

let check_fd l fd fd' =
  match init_map fd'.S.sf_stk_sz fd'.S.sf_stk_id l with
  | Ok m ->
    (&&)
      ((&&) (all2 (check_var m) fd.f_params fd'.S.sf_params)
        (all2 (check_var m) fd.f_res fd'.S.sf_res))
      (all2 (check_i m) fd.f_body fd'.S.sf_body)
  | Error _ -> false

(** val check_prog :
    prog -> S.sprog -> (Var.var * coq_Z) list list -> bool **)

let check_prog p sP ll =
  all2 (fun f s ->
    let (sf, l) = s in
    (&&) (eq_op pos_eqType (fst (Obj.magic f)) (fst (Obj.magic sf)))
      (check_fd l (snd f) (snd sf))) p (zip sP ll)
