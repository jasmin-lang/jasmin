open BinInt
open Datatypes
open Allocation
open Compiler_util
open Eqtype
open Expr
open Gen_map
open Ssrbool
open Strings
open Type
open Utils0
open Var0

type __ = Obj.t

module CmpIndex =
 struct
  (** val t : Equality.coq_type **)

  let t =
    Equality.clone (prod_eqType Var.var_eqType coq_Z_eqType)
      (Obj.magic prod_eqMixin Var.var_eqType coq_Z_eqType) (fun x -> x)

  (** val cmp : Equality.sort -> Equality.sort -> comparison **)

  let cmp =
    Obj.magic lex CmpVar.cmp Z.compare
 end

module Mi = Mmake(CmpIndex)

module Ma = MakeMalloc(Mi)

module CBEA =
 struct
  module M =
   struct
    type expansion = { alloc : Ma.t; allocated : Sv.t }

    (** val alloc : expansion -> Ma.t **)

    let alloc x = x.alloc

    (** val allocated : expansion -> Sv.t **)

    let allocated x = x.allocated

    type t = expansion

    (** val empty : expansion **)

    let empty =
      { alloc = Ma.empty; allocated = Sv.empty }

    (** val merge : expansion -> expansion -> expansion **)

    let merge r1 r2 =
      { alloc = (Ma.merge r1.alloc r2.alloc); allocated =
        (Sv.union r1.allocated r2.allocated) }

    (** val incl : expansion -> expansion -> bool **)

    let incl r1 r2 =
      (&&) (Ma.incl r1.alloc r2.alloc) (Sv.subset r2.allocated r1.allocated)

    (** val set_arr :
        Equality.sort -> Equality.sort -> Equality.sort -> expansion ->
        expansion **)

    let set_arr x n id r =
      { alloc = (Ma.set r.alloc (Obj.magic (x, n)) id); allocated =
        (Sv.add (Obj.magic { Var.vtype = Coq_sword; Var.vname = id })
          (Sv.add x r.allocated)) }
   end

  (** val check_var : M.expansion -> Var.var -> Var.var -> bool **)

  let check_var m x1 x2 =
    (&&) (eq_op Var.var_eqType (Obj.magic x1) (Obj.magic x2))
      (negb (Sv.mem (Obj.magic x1) m.M.allocated))

  (** val check_eb : M.expansion -> pexpr -> pexpr -> bool **)

  let rec check_eb m e1 e2 =
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
       | Pcast e4 -> check_eb m e3 e4
       | _ -> false)
    | Pvar x1 ->
      (match e2 with
       | Pvar x2 -> check_var m x1.v_var x2.v_var
       | _ -> false)
    | Pget (x1, e3) ->
      (match e2 with
       | Pvar x2 ->
         (match is_const e3 with
          | Some n1 ->
            (&&)
              (eq_op (option_eqType Ident.ident)
                (Obj.magic Ma.get m.M.alloc (x1.v_var, n1))
                (Obj.magic (Some x2.v_var.Var.vname)))
              (eq_op stype_eqType (Obj.magic Var.vtype x2.v_var)
                (Obj.magic Coq_sword))
          | None -> false)
       | Pget (x2, e4) ->
         (&&) (check_var m x1.v_var x2.v_var) (check_eb m e3 e4)
       | _ -> false)
    | Pload (x1, e3) ->
      (match e2 with
       | Pload (x2, e4) ->
         (&&) (check_var m x1.v_var x2.v_var) (check_eb m e3 e4)
       | _ -> false)
    | Pnot e3 ->
      (match e2 with
       | Pnot e4 -> check_eb m e3 e4
       | _ -> false)
    | Papp2 (o1, e11, e12) ->
      (match e2 with
       | Papp2 (o2, e21, e22) ->
         (&&)
           ((&&) (eq_op sop2_eqType (Obj.magic o1) (Obj.magic o2))
             (check_eb m e11 e21)) (check_eb m e12 e22)
       | _ -> false)

  (** val check_e : pexpr -> pexpr -> M.expansion -> M.expansion cexec **)

  let check_e e1 e2 m =
    if check_eb m e1 e2 then cok m else cerror (Cerr_arr_exp (e1, e2))

  (** val check_lval : lval -> lval -> M.expansion -> M.expansion cexec **)

  let check_lval r1 r2 m =
    match r1 with
    | Lnone _ ->
      (match r2 with
       | Lnone _ -> cok m
       | _ -> cerror (Cerr_arr_exp_v (r1, r2)))
    | Lvar x1 ->
      (match r2 with
       | Lvar x2 ->
         if check_var m x1.v_var x2.v_var
         then cok m
         else cerror (Cerr_arr_exp_v (r1, r2))
       | _ -> cerror (Cerr_arr_exp_v (r1, r2)))
    | Lmem (x1, e1) ->
      (match r2 with
       | Lmem (x2, e2) ->
         if (&&) (check_var m x1.v_var x2.v_var) (check_eb m e1 e2)
         then cok m
         else cerror (Cerr_arr_exp_v (r1, r2))
       | _ -> cerror (Cerr_arr_exp_v (r1, r2)))
    | Laset (x1, e1) ->
      (match r2 with
       | Lvar x2 ->
         if eq_op stype_eqType (Obj.magic Var.vtype x2.v_var)
              (Obj.magic Coq_sword)
         then (match is_const e1 with
               | Some n1 ->
                 cok
                   (M.set_arr (Obj.magic v_var x1) (Obj.magic n1)
                     x2.v_var.Var.vname m)
               | None -> cerror (Cerr_arr_exp_v (r1, r2)))
         else cerror (Cerr_arr_exp_v (r1, r2))
       | Laset (x2, e2) ->
         if (&&) (check_var m x1.v_var x2.v_var) (check_eb m e1 e2)
         then cok m
         else cerror (Cerr_arr_exp_v (r1, r2))
       | _ -> cerror (Cerr_arr_exp_v (r1, r2)))
 end

module CheckExpansion = MakeCheckAlloc(CBEA)
