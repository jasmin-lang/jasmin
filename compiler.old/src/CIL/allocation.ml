open Ascii
open Datatypes
open String0
open Compiler_util
open Eqtype
open Expr
open Gen_map
open Seq
open Ssrbool
open Ssreflect
open Strings
open Type
open Utils0
open Var0

let __ = let rec f _ = Obj.repr f in Obj.repr f

module type CheckB =
 sig
  module M :
   sig
    type t

    val empty : t

    val merge : t -> t -> t

    val incl : t -> t -> bool
   end

  val check_e : pexpr -> pexpr -> M.t -> M.t cexec

  val check_lval : lval -> lval -> M.t -> M.t cexec
 end

(** val salloc : string **)

let salloc =
  String ((Ascii (true, false, false, false, false, true, true, false)),
    (String ((Ascii (false, false, true, true, false, true, true, false)),
    (String ((Ascii (false, false, true, true, false, true, true, false)),
    (String ((Ascii (true, true, true, true, false, true, true, false)),
    (String ((Ascii (true, true, false, false, false, true, true, false)),
    (String ((Ascii (true, false, false, false, false, true, true, false)),
    (String ((Ascii (false, false, true, false, true, true, true, false)),
    (String ((Ascii (true, false, false, true, false, true, true, false)),
    (String ((Ascii (true, true, true, true, false, true, true, false)),
    (String ((Ascii (false, true, true, true, false, true, true, false)),
    EmptyString)))))))))))))))))))

module MakeCheckAlloc =
 functor (C:CheckB) ->
 struct
  (** val loop :
      instr_info -> (C.M.t -> C.M.t ciexec) -> nat -> C.M.t -> C.M.t ciexec **)

  let rec loop ii check_c n m =
    match n with
    | O ->
      cierror ii (Cerr_Loop (String ((Ascii (true, false, false, false,
        false, true, true, false)), (String ((Ascii (false, false, true,
        true, false, true, true, false)), (String ((Ascii (false, false,
        true, true, false, true, true, false)), (String ((Ascii (true, true,
        true, true, false, true, true, false)), (String ((Ascii (true, true,
        false, false, false, true, true, false)), (String ((Ascii (true,
        false, false, false, false, true, true, false)), (String ((Ascii
        (false, false, true, false, true, true, true, false)), (String
        ((Ascii (true, false, false, true, false, true, true, false)),
        (String ((Ascii (true, true, true, true, false, true, true, false)),
        (String ((Ascii (false, true, true, true, false, true, true, false)),
        EmptyString)))))))))))))))))))))
    | S n0 ->
      Result.bind (fun m' ->
        if C.M.incl m m' then Ok m else loop ii check_c n0 (C.M.merge m m'))
        (check_c m)

  (** val check_e_error : error_msg **)

  let check_e_error =
    Cerr_fold2 (String ((Ascii (true, false, false, false, false, true, true,
      false)), (String ((Ascii (false, false, true, true, false, true, true,
      false)), (String ((Ascii (false, false, true, true, false, true, true,
      false)), (String ((Ascii (true, true, true, true, false, true, true,
      false)), (String ((Ascii (true, true, false, false, false, true, true,
      false)), (String ((Ascii (true, false, false, false, false, true, true,
      false)), (String ((Ascii (false, false, true, false, true, true, true,
      false)), (String ((Ascii (true, false, false, true, false, true, true,
      false)), (String ((Ascii (true, true, true, true, false, true, true,
      false)), (String ((Ascii (false, true, true, true, false, true, true,
      false)), (String ((Ascii (false, true, false, true, true, true, false,
      false)), (String ((Ascii (true, true, false, false, false, true, true,
      false)), (String ((Ascii (false, false, false, true, false, true, true,
      false)), (String ((Ascii (true, false, true, false, false, true, true,
      false)), (String ((Ascii (true, true, false, false, false, true, true,
      false)), (String ((Ascii (true, true, false, true, false, true, true,
      false)), (String ((Ascii (true, true, true, true, true, false, true,
      false)), (String ((Ascii (true, false, true, false, false, true, true,
      false)), EmptyString))))))))))))))))))))))))))))))))))))

  (** val cmd2_error : error_msg **)

  let cmd2_error =
    Cerr_fold2 (String ((Ascii (true, false, false, false, false, true, true,
      false)), (String ((Ascii (false, false, true, true, false, true, true,
      false)), (String ((Ascii (false, false, true, true, false, true, true,
      false)), (String ((Ascii (true, true, true, true, false, true, true,
      false)), (String ((Ascii (true, true, false, false, false, true, true,
      false)), (String ((Ascii (true, false, false, false, false, true, true,
      false)), (String ((Ascii (false, false, true, false, true, true, true,
      false)), (String ((Ascii (true, false, false, true, false, true, true,
      false)), (String ((Ascii (true, true, true, true, false, true, true,
      false)), (String ((Ascii (false, true, true, true, false, true, true,
      false)), (String ((Ascii (false, true, false, true, true, true, false,
      false)), (String ((Ascii (true, true, false, false, false, true, true,
      false)), (String ((Ascii (false, false, false, true, false, true, true,
      false)), (String ((Ascii (true, false, true, false, false, true, true,
      false)), (String ((Ascii (true, true, false, false, false, true, true,
      false)), (String ((Ascii (true, true, false, true, false, true, true,
      false)), (String ((Ascii (true, true, true, true, true, false, true,
      false)), (String ((Ascii (true, true, false, false, false, true, true,
      false)), (String ((Ascii (true, false, true, true, false, true, true,
      false)), (String ((Ascii (false, false, true, false, false, true, true,
      false)), EmptyString))))))))))))))))))))))))))))))))))))))))

  (** val check_es :
      pexpr list -> pexpr list -> C.M.t -> (error_msg, C.M.t) result **)

  let check_es es1 es2 r =
    fold2 check_e_error C.check_e es1 es2 r

  (** val check_lvals :
      lval list -> lval list -> C.M.t -> (error_msg, C.M.t) result **)

  let check_lvals =
    fold2 (Cerr_fold2 (String ((Ascii (true, false, false, false, false,
      true, true, false)), (String ((Ascii (false, false, true, true, false,
      true, true, false)), (String ((Ascii (false, false, true, true, false,
      true, true, false)), (String ((Ascii (true, true, true, true, false,
      true, true, false)), (String ((Ascii (true, true, false, false, false,
      true, true, false)), (String ((Ascii (true, false, false, false, false,
      true, true, false)), (String ((Ascii (false, false, true, false, true,
      true, true, false)), (String ((Ascii (true, false, false, true, false,
      true, true, false)), (String ((Ascii (true, true, true, true, false,
      true, true, false)), (String ((Ascii (false, true, true, true, false,
      true, true, false)), (String ((Ascii (false, true, false, true, true,
      true, false, false)), (String ((Ascii (true, true, false, false, false,
      true, true, false)), (String ((Ascii (false, false, false, true, false,
      true, true, false)), (String ((Ascii (true, false, true, false, false,
      true, true, false)), (String ((Ascii (true, true, false, false, false,
      true, true, false)), (String ((Ascii (true, true, false, true, false,
      true, true, false)), (String ((Ascii (true, true, true, true, true,
      false, true, false)), (String ((Ascii (false, false, true, true, false,
      true, true, false)), (String ((Ascii (false, true, true, false, true,
      true, true, false)), (String ((Ascii (true, false, false, false, false,
      true, true, false)), (String ((Ascii (false, false, true, true, false,
      true, true, false)), (String ((Ascii (true, true, false, false, true,
      true, true, false)),
      EmptyString))))))))))))))))))))))))))))))))))))))))))))) C.check_lval

  (** val check_var : var_i -> var_i -> C.M.t -> C.M.t cexec **)

  let check_var x1 x2 r =
    C.check_lval (Lvar x1) (Lvar x2) r

  (** val check_vars :
      var_i list -> var_i list -> C.M.t -> (error_msg, C.M.t) result **)

  let check_vars xs1 xs2 r =
    check_lvals (map (fun x -> Lvar x) xs1) (map (fun x -> Lvar x) xs2) r

  (** val check_i :
      instr_info -> instr_r -> instr_r -> C.M.t -> C.M.t ciexec **)

  let rec check_i iinfo i1 i2 r =
    match i1 with
    | Cassgn (x1, _, e1) ->
      (match i2 with
       | Cassgn (x2, _, e2) ->
         add_iinfo iinfo
           (Result.bind (C.check_lval x1 x2) (C.check_e e1 e2 r))
       | _ -> cierror iinfo (Cerr_neqinstr (i1, i2, salloc)))
    | Copn (xs1, o1, es1) ->
      (match i2 with
       | Copn (xs2, o2, es2) ->
         if eq_op sopn_eqType (Obj.magic o1) (Obj.magic o2)
         then add_iinfo iinfo
                (Result.bind (check_lvals xs1 xs2) (check_es es1 es2 r))
         else cierror iinfo (Cerr_neqop (o1, o2, salloc))
       | _ -> cierror iinfo (Cerr_neqinstr (i1, i2, salloc)))
    | Cif (e1, c11, c12) ->
      (match i2 with
       | Cif (e2, c21, c22) ->
         Result.bind (fun re ->
           Result.bind (fun r1 ->
             Result.bind (fun r2 -> Ok (C.M.merge r1 r2))
               (fold2 (iinfo, cmd2_error) check_I c12 c22 re))
             (fold2 (iinfo, cmd2_error) check_I c11 c21 re))
           (add_iinfo iinfo (C.check_e e1 e2 r))
       | _ -> cierror iinfo (Cerr_neqinstr (i1, i2, salloc)))
    | Cfor (x1, r0, c1) ->
      let (p, hi1) = r0 in
      let (d1, lo1) = p in
      (match i2 with
       | Cfor (x2, r1, c2) ->
         let (p0, hi2) = r1 in
         let (d2, lo2) = p0 in
         if eq_op dir_eqType (Obj.magic d1) (Obj.magic d2)
         then Result.bind (fun rhi ->
                let check_c = fun r2 ->
                  Result.bind (fold2 (iinfo, cmd2_error) check_I c1 c2)
                    (add_iinfo iinfo (check_var x1 x2 r2))
                in
                loop iinfo check_c Loop.nb rhi)
                (add_iinfo iinfo
                  (Result.bind (C.check_e hi1 hi2) (C.check_e lo1 lo2 r)))
         else cierror iinfo (Cerr_neqdir salloc)
       | _ -> cierror iinfo (Cerr_neqinstr (i1, i2, salloc)))
    | Cwhile (e1, c1) ->
      (match i2 with
       | Cwhile (e2, c2) ->
         let check_c = fun r0 ->
           Result.bind (fold2 (iinfo, cmd2_error) check_I c1 c2)
             (add_iinfo iinfo (C.check_e e1 e2 r0))
         in
         loop iinfo check_c Loop.nb r
       | _ -> cierror iinfo (Cerr_neqinstr (i1, i2, salloc)))
    | Ccall (_, x1, f1, arg1) ->
      (match i2 with
       | Ccall (_, x2, f2, arg2) ->
         if eq_op pos_eqType (Obj.magic f1) (Obj.magic f2)
         then add_iinfo iinfo
                (Result.bind (check_lvals x1 x2) (check_es arg1 arg2 r))
         else cierror iinfo (Cerr_neqfun (f1, f2, salloc))
       | _ -> cierror iinfo (Cerr_neqinstr (i1, i2, salloc)))

  (** val check_I :
      instr -> instr -> C.M.t -> (instr_info * error_msg, C.M.t) result **)

  and check_I i1 i2 r =
    let MkI (ii, i3) = i1 in let MkI (_, i4) = i2 in check_i ii i3 i4 r

  (** val check_cmd :
      instr_info -> instr list -> instr list -> C.M.t ->
      (instr_info * error_msg, C.M.t) result **)

  let check_cmd iinfo =
    fold2 (iinfo, cmd2_error) check_I

  (** val check_fundef :
      (funname * fundef) -> (funname * fundef) -> unit -> unit cfexec **)

  let check_fundef f1 f2 _ =
    let (f3, fd1) = f1 in
    let (f4, fd2) = f2 in
    if eq_op pos_eqType (Obj.magic f3) (Obj.magic f4)
    then add_finfo f3 f4
           (Result.bind (fun r ->
             Result.bind (fun r0 ->
               let es1 = map (fun x -> Pvar x) fd1.f_res in
               let es2 = map (fun x -> Pvar x) fd2.f_res in
               Result.bind (fun _ -> Ok ())
                 (add_iinfo fd1.f_iinfo (check_es es1 es2 r0)))
               (check_cmd fd1.f_iinfo fd1.f_body fd2.f_body r))
             (add_iinfo fd1.f_iinfo
               (check_vars fd1.f_params fd2.f_params C.M.empty)))
    else cferror (Ferr_neqfun (f3, f4))

  (** val check_prog :
      (funname * fundef) list -> (funname * fundef) list -> (fun_error, unit)
      result **)

  let check_prog prog1 prog2 =
    fold2 Ferr_neqprog check_fundef prog1 prog2 ()
 end

module MakeMalloc =
 functor (M:MAP) ->
 struct
  type t_ = { mvar : Equality.sort M.t; mid : Equality.sort Ms.t }

  (** val mvar : t_ -> Equality.sort M.t **)

  let mvar t0 =
    t0.mvar

  (** val mid : t_ -> Equality.sort Ms.t **)

  let mid t0 =
    t0.mid

  type t = t_

  (** val get : t -> Equality.sort -> Equality.sort option **)

  let get m x =
    M.get (mvar m) x

  (** val rm_id : t -> Equality.sort -> Equality.sort M.t **)

  let rm_id m id =
    match Ms.get (mid m) id with
    | Some x -> M.remove (mvar m) x
    | None -> mvar m

  (** val rm_x : t -> Equality.sort -> Equality.sort Ms.Map.t **)

  let rm_x m x =
    match M.get (mvar m) x with
    | Some id -> Ms.remove (mid m) id
    | None -> mid m

  (** val set : t -> Equality.sort -> Equality.sort -> t_ **)

  let set m x id =
    { mvar = (M.set (rm_id m id) x id); mid = (Ms.set (rm_x m x) id x) }

  (** val empty : t_ **)

  let empty =
    { mvar = M.empty; mid = Ms.empty }

  (** val merge : t_ -> t -> t **)

  let merge m1 m2 =
    M.fold (fun x idx m ->
      match get m2 x with
      | Some idx' -> if eq_op Ident.ident idx idx' then set m x idx else m
      | None -> m) (mvar m1) empty

  (** val incl : t_ -> t -> bool **)

  let incl m1 m2 =
    M.fold (fun x id b ->
      (&&) b
        (eq_op (option_eqType Ident.ident) (Obj.magic get m2 x)
          (Obj.magic (Some id)))) (mvar m1) true

  (** val inclP : t -> t -> reflect **)

  let inclP m1 m2 =
    let f = fun a kv ->
      (&&) a
        (eq_op (option_eqType Ident.ident) (Obj.magic get m2 (fst kv))
          (Obj.magic (Some (snd kv))))
    in
    let l = M.elements (mvar m1) in
    let b = true in
    ssr_have __
      (ssr_have __
        (ssr_have ReflectT
          (let _evar_0_ = fun b0 hb -> equivP b0 hb in
           let _evar_0_0 = fun p _ hrec b0 hb ->
             hrec (f b0 p)
               (let _evar_0_0 = fun _ ->
                  let _evar_0_0 = fun _ -> ReflectT in
                  let _evar_0_1 = fun _ -> ReflectF in
                  (match eqP (option_eqType Ident.ident)
                           (Obj.magic get m2 (fst p))
                           (Obj.magic (Some (snd p))) with
                   | ReflectT -> _evar_0_0 __
                   | ReflectF -> _evar_0_1 __)
                in
                let _evar_0_1 = fun _ -> ReflectF in
                (match hb with
                 | ReflectT -> _evar_0_0 __
                 | ReflectF -> _evar_0_1 __)) __ __
           in
           (fun hb _ _ ->
           let rec f0 l0 b0 hb0 =
             match l0 with
             | [] -> _evar_0_ b0 hb0
             | y :: l1 ->
               _evar_0_0 y l1 (fun b1 hb1 _ _ -> f0 l1 b1 hb1) b0 hb0
           in f0 l b hb))))
 end

module CBAreg =
 struct
  module M =
   struct
    module Mv = MakeMalloc(Mvar)

    type t_ = { mv : Mv.t; mset : Sv.t }

    (** val mv : t_ -> Mv.t **)

    let mv x = x.mv

    (** val mset : t_ -> Sv.t **)

    let mset x = x.mset

    type t = t_

    (** val get : t -> Var.var -> Equality.sort option **)

    let get m x =
      Mv.get m.mv (Obj.magic x)

    (** val set : t_ -> Equality.sort -> Equality.sort -> t_ **)

    let set m x id =
      { mv = (Mv.set m.mv x id); mset = (Sv.add x m.mset) }

    (** val empty_s : Sv.t -> t_ **)

    let empty_s s =
      { mv = Mv.empty; mset = s }

    (** val empty : t_ **)

    let empty =
      empty_s Sv.empty

    (** val merge : t_ -> t_ -> t_ **)

    let merge m1 m2 =
      { mv = (Mv.merge m1.mv m2.mv); mset = (Sv.union m1.mset m2.mset) }

    (** val incl : t_ -> t_ -> bool **)

    let incl m1 m2 =
      (&&) (Mv.incl m1.mv m2.mv) (Sv.subset m2.mset m1.mset)

    (** val inclP : t -> t -> reflect **)

    let inclP m1 m2 =
      equivP ((&&) (Mv.incl m1.mv m2.mv) (Sv.subset m2.mset m1.mset))
        (andP (Mv.incl m1.mv m2.mv) (Sv.subset m2.mset m1.mset))
   end

  (** val check_v : var_i -> var_i -> M.t -> M.t cexec **)

  let check_v xi1 xi2 m =
    let x1 = xi1.v_var in
    let x2 = xi2.v_var in
    if eq_op stype_eqType (Obj.magic Var.vtype x1) (Obj.magic Var.vtype x2)
    then (match M.get m x1 with
          | Some id' ->
            if eq_op Ident.ident x2.Var.vname id'
            then cok m
            else cerror (Cerr_varalloc (xi1, xi2, (String ((Ascii (false,
                   true, true, false, true, true, true, false)), (String
                   ((Ascii (true, false, false, false, false, true, true,
                   false)), (String ((Ascii (false, true, false, false, true,
                   true, true, false)), (String ((Ascii (true, false, false,
                   true, false, true, true, false)), (String ((Ascii (true,
                   false, false, false, false, true, true, false)), (String
                   ((Ascii (false, true, false, false, false, true, true,
                   false)), (String ((Ascii (false, false, true, true, false,
                   true, true, false)), (String ((Ascii (true, false, true,
                   false, false, true, true, false)), (String ((Ascii (false,
                   false, false, false, false, true, false, false)), (String
                   ((Ascii (true, false, true, true, false, true, true,
                   false)), (String ((Ascii (true, false, false, true, false,
                   true, true, false)), (String ((Ascii (true, true, false,
                   false, true, true, true, false)), (String ((Ascii (true,
                   false, true, true, false, true, true, false)), (String
                   ((Ascii (true, false, false, false, false, true, true,
                   false)), (String ((Ascii (false, false, true, false, true,
                   true, true, false)), (String ((Ascii (true, true, false,
                   false, false, true, true, false)), (String ((Ascii (false,
                   false, false, true, false, true, true, false)),
                   EmptyString))))))))))))))))))))))))))))))))))))
          | None ->
            if Sv.mem (Obj.magic x1) m.M.mset
            then cerror (Cerr_varalloc (xi1, xi2, (String ((Ascii (false,
                   true, true, false, true, true, true, false)), (String
                   ((Ascii (true, false, false, false, false, true, true,
                   false)), (String ((Ascii (false, true, false, false, true,
                   true, true, false)), (String ((Ascii (true, false, false,
                   true, false, true, true, false)), (String ((Ascii (true,
                   false, false, false, false, true, true, false)), (String
                   ((Ascii (false, true, false, false, false, true, true,
                   false)), (String ((Ascii (false, false, true, true, false,
                   true, true, false)), (String ((Ascii (true, false, true,
                   false, false, true, true, false)), (String ((Ascii (false,
                   false, false, false, false, true, false, false)), (String
                   ((Ascii (true, false, false, false, false, true, true,
                   false)), (String ((Ascii (false, false, true, true, false,
                   true, true, false)), (String ((Ascii (false, true, false,
                   false, true, true, true, false)), (String ((Ascii (true,
                   false, true, false, false, true, true, false)), (String
                   ((Ascii (true, false, false, false, false, true, true,
                   false)), (String ((Ascii (false, false, true, false,
                   false, true, true, false)), (String ((Ascii (true, false,
                   false, true, true, true, true, false)), (String ((Ascii
                   (false, false, false, false, false, true, false, false)),
                   (String ((Ascii (true, true, false, false, true, true,
                   true, false)), (String ((Ascii (true, false, true, false,
                   false, true, true, false)), (String ((Ascii (false, false,
                   true, false, true, true, true, false)),
                   EmptyString))))))))))))))))))))))))))))))))))))))))))
            else cok (M.set m (Obj.magic x1) x2.Var.vname))
    else cerror (Cerr_varalloc (xi1, xi2, (String ((Ascii (false, false,
           true, false, true, true, true, false)), (String ((Ascii (true,
           false, false, true, true, true, true, false)), (String ((Ascii
           (false, false, false, false, true, true, true, false)), (String
           ((Ascii (true, false, true, false, false, true, true, false)),
           (String ((Ascii (false, false, false, false, false, true, false,
           false)), (String ((Ascii (true, false, true, true, false, true,
           true, false)), (String ((Ascii (true, false, false, true, false,
           true, true, false)), (String ((Ascii (true, true, false, false,
           true, true, true, false)), (String ((Ascii (true, false, true,
           true, false, true, true, false)), (String ((Ascii (true, false,
           false, false, false, true, true, false)), (String ((Ascii (false,
           false, true, false, true, true, true, false)), (String ((Ascii
           (true, true, false, false, false, true, true, false)), (String
           ((Ascii (false, false, false, true, false, true, true, false)),
           EmptyString))))))))))))))))))))))))))))

  (** val check_e : pexpr -> pexpr -> M.t -> M.t cexec **)

  let rec check_e e1 e2 m =
    match e1 with
    | Pconst n1 ->
      (match e2 with
       | Pconst n2 ->
         if eq_op coq_Z_eqType (Obj.magic n1) (Obj.magic n2)
         then cok m
         else cerror (Cerr_neqexpr (e1, e2, salloc))
       | _ -> cerror (Cerr_neqexpr (e1, e2, salloc)))
    | Pbool b1 ->
      (match e2 with
       | Pbool b2 ->
         if eq_op bool_eqType (Obj.magic b1) (Obj.magic b2)
         then cok m
         else cerror (Cerr_neqexpr (e1, e2, salloc))
       | _ -> cerror (Cerr_neqexpr (e1, e2, salloc)))
    | Pcast e3 ->
      (match e2 with
       | Pcast e4 -> check_e e3 e4 m
       | _ -> cerror (Cerr_neqexpr (e1, e2, salloc)))
    | Pvar x1 ->
      (match e2 with
       | Pvar x2 -> check_v x1 x2 m
       | _ -> cerror (Cerr_neqexpr (e1, e2, salloc)))
    | Pget (x1, e3) ->
      (match e2 with
       | Pget (x2, e4) -> Result.bind (check_e e3 e4) (check_v x1 x2 m)
       | _ -> cerror (Cerr_neqexpr (e1, e2, salloc)))
    | Pload (x1, e3) ->
      (match e2 with
       | Pload (x2, e4) -> Result.bind (check_e e3 e4) (check_v x1 x2 m)
       | _ -> cerror (Cerr_neqexpr (e1, e2, salloc)))
    | Pnot e3 ->
      (match e2 with
       | Pnot e4 -> check_e e3 e4 m
       | _ -> cerror (Cerr_neqexpr (e1, e2, salloc)))
    | Papp2 (o1, e11, e12) ->
      (match e2 with
       | Papp2 (o2, e21, e22) ->
         if eq_op sop2_eqType (Obj.magic o1) (Obj.magic o2)
         then Result.bind (check_e e12 e22) (check_e e11 e21 m)
         else cerror (Cerr_neqop2 (o1, o2, salloc))
       | _ -> cerror (Cerr_neqexpr (e1, e2, salloc)))

  (** val check_var : var_i -> var_i -> M.t_ -> M.t cexec **)

  let check_var xi1 xi2 m =
    let x1 = xi1.v_var in
    let x2 = xi2.v_var in
    if eq_op stype_eqType (Obj.magic Var.vtype x1) (Obj.magic Var.vtype x2)
    then cok (M.set m (Obj.magic x1) x2.Var.vname)
    else cerror (Cerr_varalloc (xi1, xi2, (String ((Ascii (false, false,
           true, false, true, true, true, false)), (String ((Ascii (true,
           false, false, true, true, true, true, false)), (String ((Ascii
           (false, false, false, false, true, true, true, false)), (String
           ((Ascii (true, false, true, false, false, true, true, false)),
           (String ((Ascii (false, false, false, false, false, true, false,
           false)), (String ((Ascii (true, false, true, true, false, true,
           true, false)), (String ((Ascii (true, false, false, true, false,
           true, true, false)), (String ((Ascii (true, true, false, false,
           true, true, true, false)), (String ((Ascii (true, false, true,
           true, false, true, true, false)), (String ((Ascii (true, false,
           false, false, false, true, true, false)), (String ((Ascii (false,
           false, true, false, true, true, true, false)), (String ((Ascii
           (true, true, false, false, false, true, true, false)), (String
           ((Ascii (false, false, false, true, false, true, true, false)),
           EmptyString))))))))))))))))))))))))))))

  (** val check_lval : lval -> lval -> M.t -> M.t cexec **)

  let check_lval x1 x2 m =
    match x1 with
    | Lnone _ ->
      (match x2 with
       | Lnone _ -> cok m
       | _ -> cerror (Cerr_neqrval (x1, x2, salloc)))
    | Lvar x3 ->
      (match x2 with
       | Lvar x4 -> check_var x3 x4 m
       | _ -> cerror (Cerr_neqrval (x1, x2, salloc)))
    | Lmem (x3, e1) ->
      (match x2 with
       | Lmem (x4, e2) -> Result.bind (check_e e1 e2) (check_v x3 x4 m)
       | _ -> cerror (Cerr_neqrval (x1, x2, salloc)))
    | Laset (x3, e1) ->
      (match x2 with
       | Laset (x4, e2) ->
         Result.bind (check_var x3 x4)
           (Result.bind (check_e e1 e2) (check_v x3 x4 m))
       | _ -> cerror (Cerr_neqrval (x1, x2, salloc)))
 end

module CheckAllocReg = MakeCheckAlloc(CBAreg)
