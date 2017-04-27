open BinNums
open BinPos
open Datatypes

module Z :
 sig
  val double : coq_Z -> coq_Z

  val succ_double : coq_Z -> coq_Z

  val pred_double : coq_Z -> coq_Z

  val pos_sub : positive -> positive -> coq_Z

  val add : coq_Z -> coq_Z -> coq_Z

  val opp : coq_Z -> coq_Z

  val sub : coq_Z -> coq_Z -> coq_Z

  val mul : coq_Z -> coq_Z -> coq_Z

  val compare : coq_Z -> coq_Z -> comparison

  val leb : coq_Z -> coq_Z -> bool

  val ltb : coq_Z -> coq_Z -> bool

  val geb : coq_Z -> coq_Z -> bool

  val gtb : coq_Z -> coq_Z -> bool

  val eqb : coq_Z -> coq_Z -> bool

  val max : coq_Z -> coq_Z -> coq_Z

  val to_nat : coq_Z -> nat

  val of_nat : nat -> coq_Z

  val eq_dec : coq_Z -> coq_Z -> bool
 end
