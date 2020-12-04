open SafetyVar
open SafetyPreanalysis
open SafetyInterfaces

(*------------------------------------------------------------*)
(* Domains Product *)

type v_dom = Nrd of int | Ppl of int

type dom_st
    
module type VDomWrap = sig
  (* Associate a domain (ppl or non-relational) to every variable.
     An array element must have the same domain that its blasted component. 
     The second argument is a state, which allows to change a variable domain
     during the analysis. 
     Only [Mvalue (Avar _)] and [MvarOffset _] can change domain. *)
  val vdom : mvar -> dom_st -> v_dom

  (* Initial state. *)
  val dom_st_init : dom_st

  (* [dom_st_update dom_st xs info] updates the packing partition to prepare for
     the assignments of variables xs. *)
  val dom_st_update : dom_st -> mvar list -> minfo -> dom_st

  val merge_dom : dom_st -> dom_st -> dom_st
  val fold_dom_st : (mvar -> v_dom -> 'a -> 'a) -> dom_st -> 'a -> 'a
end

(* Statique Packing *)
module PIMake (PW : ProgWrap) : VDomWrap

(* Dynamic Packing *)
module PIDynMake (PW : ProgWrap) : VDomWrap

(*---------------------------------------------------------------*)

(* For now we fixed the domains, and we use only two of them, one non-relational
   and one Ppl. Still, we generalized to n different domains whenever possible
   to help future possible extentions. *)
module AbsNumProd (VDW : VDomWrap) (NonRel : AbsNumType) (PplDom : AbsNumType)
  : AbsNumProdT

(*------------------------------------------------------------*)
(* Reduced Product *)

module type RProdParam = sig
  module A : AbsDisjType
  module B : AbsDisjType
  val print : ?full:bool -> Format.formatter -> (A.t * B.t) -> unit
  val reduce : (A.t * B.t) -> (A.t * B.t)
end

(* Asymmetric reduced product.   
   Careful, to_box, of_box are only using the left abstract values. *)
module ReducedProd (P : RProdParam) : AbsDisjType
