open Datatypes
open Eqtype
open Gen_map
open Ssrbool
open Strings
open Type

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module type IDENT =
 sig
  val ident : Equality.coq_type

  module Mid :
   MAP
 end

module MvMake =
 functor (I:IDENT) ->
 struct
  type var = { vtype : stype; vname : Equality.sort }

  (** val vtype : var -> stype **)

  let vtype v =
    v.vtype

  (** val vname : var -> Equality.sort **)

  let vname v =
    v.vname

  (** val var_beq : var -> var -> bool **)

  let var_beq v1 v2 =
    let { vtype = t1; vname = n1 } = v1 in
    let { vtype = t2; vname = n2 } = v2 in
    (&&) (eq_op stype_eqType (Obj.magic t1) (Obj.magic t2))
      (eq_op I.ident n1 n2)

  (** val var_eqP : var Equality.axiom **)

  let var_eqP _top_assumption_ =
    let _evar_0_ = fun t1 n1 _top_assumption_0 ->
      let _evar_0_ = fun t2 n2 ->
        iffP (var_beq { vtype = t1; vname = n1 } { vtype = t2; vname = n2 })
          (idP
            (var_beq { vtype = t1; vname = n1 } { vtype = t2; vname = n2 }))
      in
      let { vtype = x; vname = x0 } = _top_assumption_0 in _evar_0_ x x0
    in
    let { vtype = x; vname = x0 } = _top_assumption_ in _evar_0_ x x0

  (** val var_eqMixin : var Equality.mixin_of **)

  let var_eqMixin =
    { Equality.op = var_beq; Equality.mixin_of__1 = var_eqP }

  (** val var_eqType : Equality.coq_type **)

  let var_eqType =
    Equality.pack var_eqMixin

  (** val var_cmp : var -> var -> comparison **)

  let var_cmp x y =
    match stype_cmp (vtype x) (vtype y) with
    | Eq -> I.Mid.K.cmp (vname x) (vname y)
    | x0 -> x0

  module Mv =
   struct
    type 'to0 rt_ = { dft : (var -> 'to0); tbl : 'to0 I.Mid.t Mt.t }

    (** val dft : 'a1 rt_ -> var -> 'a1 **)

    let dft r =
      r.dft

    (** val tbl : 'a1 rt_ -> 'a1 I.Mid.t Mt.t **)

    let tbl r =
      r.tbl

    type 'to0 t = 'to0 rt_

    (** val empty : (var -> 'a1) -> 'a1 t **)

    let empty dft0 =
      { dft = dft0; tbl = Mt.empty }

    (** val get : 'a1 t -> var -> 'a1 **)

    let get m x =
      match Mt.get (tbl m) (Obj.magic vtype x) with
      | Some mi ->
        (match I.Mid.get mi (vname x) with
         | Some v -> v
         | None -> dft m x)
      | None -> dft m x

    (** val set : 'a1 t -> var -> 'a1 -> 'a1 t **)

    let set m x v =
      let mi =
        match Mt.get (tbl m) (Obj.magic vtype x) with
        | Some mi -> mi
        | None -> I.Mid.empty
      in
      let mi0 = I.Mid.set mi (vname x) v in
      { dft = (dft m); tbl = (Mt.set (tbl m) (Obj.magic vtype x) mi0) }

    (** val remove : 'a1 t -> var -> 'a1 rt_ **)

    let remove m x =
      match Mt.get (tbl m) (Obj.magic vtype x) with
      | Some mi ->
        { dft = (dft m); tbl =
          (Mt.set (tbl m) (Obj.magic vtype x) (I.Mid.remove mi (vname x))) }
      | None -> m

    (** val indom : var -> 'a1 t -> bool **)

    let indom x m =
      match Mt.get (tbl m) (Obj.magic vtype x) with
      | Some mi ->
        (match I.Mid.get mi (vname x) with
         | Some _ -> true
         | None -> false)
      | None -> false

    (** val map : (stype -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

    let map f m =
      { dft = (fun x -> f (vtype x) (dft m x)); tbl =
        (Mt.map (fun t0 mi -> I.Mid.map (Obj.magic f t0) mi) (tbl m)) }

    (** val map2 :
        (var -> 'a3) -> (var -> 'a1 -> 'a2 -> 'a3) -> 'a1 t -> 'a2 t -> 'a3 t **)

    let map2 fd f m1 m2 =
      let dft1 = dft m1 in
      let dft2 = dft m2 in
      let doty = fun ty mi1 mi2 ->
        match mi1 with
        | Some mi3 ->
          (match mi2 with
           | Some mi4 ->
             Some
               (I.Mid.map2 (fun id o1 o2 ->
                 match o1 with
                 | Some v1 ->
                   (match o2 with
                    | Some v2 ->
                      let x = { vtype = ty; vname = id } in Some (f x v1 v2)
                    | None ->
                      let x = { vtype = ty; vname = id } in
                      Some (f x v1 (dft2 x)))
                 | None ->
                   (match o2 with
                    | Some v2 ->
                      let x = { vtype = ty; vname = id } in
                      Some (f x (dft1 x) v2)
                    | None -> None)) mi3 mi4)
           | None ->
             Some
               (I.Mid.mapi (fun id v1 ->
                 let x = { vtype = ty; vname = id } in f x v1 (dft2 x)) mi3))
        | None ->
          (match mi2 with
           | Some mi3 ->
             Some
               (I.Mid.mapi (fun id v2 ->
                 let x = { vtype = ty; vname = id } in f x (dft1 x) v2) mi3)
           | None -> None)
      in
      { dft = fd; tbl = (Mt.map2 (Obj.magic doty) (tbl m1) (tbl m2)) }

    (** val map2Pred :
        (var -> 'a3) -> (var -> 'a1 -> 'a2 -> 'a3) -> 'a1 t -> 'a2 t -> var
        -> (__ -> __ -> 'a4 -> 'a4) -> 'a4 -> 'a4 **)

    let map2Pred _ _ m1 m2 x =
      let _evar_0_ = fun mi1 ->
        let _evar_0_ = fun mi2 ->
          let _evar_0_ =
            let _evar_0_ =
              let _evar_0_ = fun _ _ _ _ _ x0 -> x0 in
              (fun a ->
              let { vtype = x0; vname = x1 } = x in _evar_0_ x0 x1 a)
            in
            let _evar_0_0 =
              let _evar_0_0 = fun _ _ _ _ x0 -> x0 in
              (fun a ->
              let { vtype = x0; vname = x1 } = x in _evar_0_0 x0 x1 a)
            in
            (match I.Mid.get mi2 (vname x) with
             | Some x0 -> _evar_0_ x0
             | None -> _evar_0_0)
          in
          let _evar_0_0 =
            let _evar_0_0 =
              let _evar_0_0 = fun _ _ _ _ x0 -> x0 in
              (fun a ->
              let { vtype = x0; vname = x1 } = x in _evar_0_0 x0 x1 a)
            in
            let _evar_0_1 = fun x0 x1 -> x0 __ __ x1 in
            (match I.Mid.get mi2 (vname x) with
             | Some x0 -> _evar_0_0 x0
             | None -> _evar_0_1)
          in
          (match I.Mid.get mi1 (vname x) with
           | Some x0 -> _evar_0_ x0
           | None -> _evar_0_0)
        in
        let _evar_0_0 =
          let _evar_0_0 =
            let _evar_0_0 = fun _ _ _ _ x0 -> x0 in
            (fun a ->
            let { vtype = x0; vname = x1 } = x in _evar_0_0 x0 x1 a)
          in
          let _evar_0_1 =
            let _evar_0_1 = fun _ _ x0 x1 -> x0 __ __ x1 in
            (fun x0 ->
            let { vtype = x1; vname = x2 } = x in _evar_0_1 x1 x2 x0)
          in
          (match I.Mid.get mi1 (vname x) with
           | Some x0 -> _evar_0_0 x0
           | None -> _evar_0_1)
        in
        (match Mt.get (tbl m2) (Obj.magic vtype x) with
         | Some x0 -> _evar_0_ x0
         | None -> _evar_0_0)
      in
      let _evar_0_0 =
        let _evar_0_0 = fun mi2 ->
          let _evar_0_0 =
            let _evar_0_0 = fun _ _ _ _ x0 -> x0 in
            (fun a ->
            let { vtype = x0; vname = x1 } = x in _evar_0_0 x0 x1 a)
          in
          let _evar_0_1 =
            let _evar_0_1 = fun _ _ x0 x1 -> x0 __ __ x1 in
            (fun x0 ->
            let { vtype = x1; vname = x2 } = x in _evar_0_1 x1 x2 x0)
          in
          (match I.Mid.get mi2 (vname x) with
           | Some x0 -> _evar_0_0 x0
           | None -> _evar_0_1)
        in
        let _evar_0_1 = fun x0 x1 -> x0 __ __ x1 in
        (match Mt.get (tbl m2) (Obj.magic vtype x) with
         | Some x0 -> _evar_0_0 x0
         | None -> _evar_0_1)
      in
      (match Mt.get (tbl m1) (Obj.magic vtype x) with
       | Some x0 -> _evar_0_ x0
       | None -> _evar_0_0)
   end
 end

module Ident =
 struct
  (** val ident : Equality.coq_type **)

  let ident =
    Equality.clone string_eqType (Obj.magic string_eqMixin) (fun x -> x)

  module Mid = Ms
 end

module Var = MvMake(Ident)

module CmpVar =
 struct
  (** val t : Equality.coq_type **)

  let t =
    Equality.clone Var.var_eqType (Obj.magic Var.var_eqMixin) (fun x -> x)

  (** val cmp : Equality.sort -> Equality.sort -> comparison **)

  let cmp =
    Obj.magic Var.var_cmp
 end

module Sv = Smake(CmpVar)

(** val disjoint : Sv.t -> Sv.t -> bool **)

let disjoint s1 s2 =
  Sv.is_empty (Sv.inter s1 s2)

module Mvar = Mmake(CmpVar)
