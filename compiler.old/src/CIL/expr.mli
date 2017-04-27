open BinNums
open Datatypes
open Eqtype
open Seq
open Ssrbool
open Ssrnat
open Utils0
open Var0

type sop2 =
| Oand
| Oor
| Oadd
| Omul
| Osub
| Oeq
| Oneq
| Olt
| Ole
| Ogt
| Oge

type sopn =
| Olnot
| Oxor
| Oland
| Olor
| Olsr
| Olsl
| Oif
| Omulu
| Omuli
| Oaddcarry
| Osubcarry

val sop2_beq : sop2 -> sop2 -> bool

val sop2_eq_axiom : sop2 Equality.axiom

val sop2_eqMixin : sop2 Equality.mixin_of

val sop2_eqType : Equality.coq_type

val sopn_beq : sopn -> sopn -> bool

val sopn_eq_axiom : sopn Equality.axiom

val sopn_eqMixin : sopn Equality.mixin_of

val sopn_eqType : Equality.coq_type

type var_info = positive

type var_i = { v_var : Var.var; v_info : var_info }

val v_var : var_i -> Var.var

type pexpr =
| Pconst of coq_Z
| Pbool of bool
| Pcast of pexpr
| Pvar of var_i
| Pget of var_i * pexpr
| Pload of var_i * pexpr
| Pnot of pexpr
| Papp2 of sop2 * pexpr * pexpr

val var_i_beq : var_i -> var_i -> bool

val var_i_eq_axiom : var_i Equality.axiom

val var_i_eqMixin : var_i Equality.mixin_of

val var_i_eqType : Equality.coq_type

module Eq_pexpr :
 sig
  val eqb : pexpr -> pexpr -> bool

  val eq_axiom : pexpr Equality.axiom

  val eqMixin : pexpr Equality.mixin_of

  module Exports :
   sig
    val eqType : Equality.coq_type
   end
 end

type lval =
| Lnone of var_info
| Lvar of var_i
| Lmem of var_i * pexpr
| Laset of var_i * pexpr

val lval_beq : lval -> lval -> bool

val lval_eq_axiom : lval Equality.axiom

val lval_eqMixin : lval Equality.mixin_of

val lval_eqType : Equality.coq_type

type dir =
| UpTo
| DownTo

val dir_beq : dir -> dir -> bool

val dir_eq_axiom : dir Equality.axiom

val dir_eqMixin : dir Equality.mixin_of

val dir_eqType : Equality.coq_type

type range = (dir * pexpr) * pexpr

type instr_info = positive

val dummy_iinfo : positive

type assgn_tag =
| AT_keep
| AT_rename
| AT_inline

val assgn_tag_beq : assgn_tag -> assgn_tag -> bool

val assgn_tag_eq_axiom : assgn_tag Equality.axiom

val assgn_tag_eqMixin : assgn_tag Equality.mixin_of

val assgn_tag_eqType : Equality.coq_type

type funname = positive

type inline_info =
| InlineFun
| DoNotInline

val inline_info_beq : inline_info -> inline_info -> bool

val inline_info_eq_axiom : inline_info Equality.axiom

val inline_info_eqMixin : inline_info Equality.mixin_of

val inline_info_eqType : Equality.coq_type

type instr_r =
| Cassgn of lval * assgn_tag * pexpr
| Copn of lval list * sopn * pexpr list
| Cif of pexpr * instr list * instr list
| Cfor of var_i * range * instr list
| Cwhile of pexpr * instr list
| Ccall of inline_info * lval list * funname * pexpr list
and instr =
| MkI of instr_info * instr_r

type fundef = { f_iinfo : instr_info; f_params : var_i list;
                f_body : instr list; f_res : var_i list }

val f_iinfo : fundef -> instr_info

val f_params : fundef -> var_i list

val f_body : fundef -> instr list

val f_res : fundef -> var_i list

type prog = (funname * fundef) list

val dummy_fundef : fundef

val instr_r_beq : instr_r -> instr_r -> bool

val instr_beq : instr -> instr -> bool

val instr_eq_axiom_ : (instr_r -> instr_r -> reflect) -> instr Equality.axiom

val instr_r_eq_axiom : instr_r Equality.axiom

val instr_eq_axiom : instr Equality.axiom

val instr_eqMixin : instr Equality.mixin_of

val instr_eqType : Equality.coq_type

val fundef_beq : fundef -> fundef -> bool

val fundef_eq_axiom : fundef Equality.axiom

val fundef_eqMixin : fundef Equality.mixin_of

val fundef_eqType : Equality.coq_type

val get_fundef :
  (Equality.sort * fundef) list -> Equality.sort -> fundef option

val map_prog :
  (fundef -> fundef) -> (funname * fundef) list -> (funname * fundef) list

val vrv_rec : Sv.t -> lval -> Sv.t

val vrvs_rec : Sv.t -> lval list -> Sv.t

val vrv : lval -> Sv.t

val vrvs : lval list -> Sv.t

val write_i_rec : Sv.t -> instr_r -> Sv.t

val write_I_rec : Sv.t -> instr -> Sv.t

val write_i : instr_r -> Sv.t

val write_c_rec : Sv.t -> instr list -> Sv.t

val read_e_rec : Sv.t -> pexpr -> Sv.t

val read_es_rec : Sv.t -> pexpr list -> Sv.t

val read_es : pexpr list -> Sv.t

val read_rv_rec : Sv.t -> lval -> Sv.t

val read_rv : lval -> Sv.t

val read_rvs_rec : Sv.t -> lval list -> Sv.t

val read_i_rec : Sv.t -> instr_r -> Sv.t

val read_I_rec : Sv.t -> instr -> Sv.t

val read_i : instr_r -> Sv.t

val is_const : pexpr -> coq_Z option

val is_bool : pexpr -> bool option
