open BinInt
open BinNums

module type Int =
 sig
  type t

  val i2z : t -> coq_Z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = coq_Z

  (** val _0 : coq_Z **)

  let _0 =
    Z0

  (** val _1 : coq_Z **)

  let _1 =
    Zpos Coq_xH

  (** val _2 : coq_Z **)

  let _2 =
    Zpos (Coq_xO Coq_xH)

  (** val _3 : coq_Z **)

  let _3 =
    Zpos (Coq_xI Coq_xH)

  (** val add : coq_Z -> coq_Z -> coq_Z **)

  let add =
    Z.add

  (** val opp : coq_Z -> coq_Z **)

  let opp =
    Z.opp

  (** val sub : coq_Z -> coq_Z -> coq_Z **)

  let sub =
    Z.sub

  (** val mul : coq_Z -> coq_Z -> coq_Z **)

  let mul =
    Z.mul

  (** val max : coq_Z -> coq_Z -> coq_Z **)

  let max =
    Z.max

  (** val eqb : coq_Z -> coq_Z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : coq_Z -> coq_Z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : coq_Z -> coq_Z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : coq_Z -> coq_Z -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : coq_Z -> coq_Z -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : coq_Z -> coq_Z -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> coq_Z **)

  let i2z n =
    n
 end
