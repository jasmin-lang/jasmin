open Jasmin
open Prog
open Wsize
open Apron

open SafetyUtils
open SafetyVar
open SafetyExpr 
open SafetyConstr
open SafetyPreanalysis
  
(*---------------------------------------------------------------*)
module type ProgWrap = sig
  val main_source : (unit, X86_extra.x86_extended_op) Prog.func
  val main : (minfo, X86_extra.x86_extended_op) Prog.func
  val prog : (minfo, X86_extra.x86_extended_op) Prog.prog
  val param : analyzer_param
end


(*---------------------------------------------------------------*)
module type AbsNumType = sig
  type t

  (* Make a top value defined on the given variables *)
  val make : mvar list -> t

  val meet : t -> t -> t
  val meet_list : t list -> t

  val join : t -> t -> t
  val join_list : t list -> t

  (* Because we do not have a backward analysis, we can give the loop condition
     to the widening, which uses it as threshold. *)
  val widening : Mtcons.t option -> t -> t -> t

  val forget_list : t -> mvar list -> t

  val is_included : t -> t -> bool
  val is_bottom : t -> bool
  val bottom : t -> t
  val top : t -> t

  (* expand t v v_list : v and v_list cannot contain Mvalue (AarrayEl)
     elements *)
  val expand : t -> mvar -> mvar list -> t
  (* fold t v_list : v_list cannot contain Mvalue (AarrayEl)
     elements *)
  val fold : t -> mvar list -> t

  val bound_variable : t -> mvar -> Interval.t
  val bound_texpr : t -> Mtexpr.t -> Interval.t

  val assign_expr : ?force:bool -> t -> (mvar * Mtexpr.t) list -> t

  val sat_constr : t -> Mtcons.t -> bool
    
  val meet_constr : t -> Mtcons.t -> t
  val meet_constr_list : t -> Mtcons.t list -> t

  (* Unify the two abstract values on their least common environment. *)
  val unify : t -> t -> t

  (* Variables that are removed are first existentially quantified, and
     variables that are introduced are unconstrained. *)
  val change_environment : t -> mvar list -> t
  val remove_vars : t -> mvar list -> t

  val to_box : t -> Box.t Abstract1.t
  val of_box : Box.t Abstract1.t -> t

  val get_env : t -> Environment.t

  val print : ?full:bool -> Format.formatter -> t -> unit
end


(*---------------------------------------------------------------*)
module type AbsNumProdT = sig
  include AbsNumType

  (* Overwrite [AbsNumType] signature for [of_box].
     We use the domain information in the argument of type [t]. *)
  val of_box : Box.t Abstract1.t -> t -> t
    
  val set_rel   : t -> mvar -> t
  val set_unrel : t -> mvar -> t

  (* [dom_st_update a xs info] updates the packing partition to prepare for
     the assignments of variables [xs]. *)
  val dom_st_update : t -> mvar list -> minfo -> t
end


(*---------------------------------------------------------------*)
(* Trace partitionning, see the description of the [node] type in 
   the module [Ptree]. *)
module type AbsDisjType = sig
  include AbsNumProdT

  (* Make a top value with *no* disjunction *)
  val top_no_disj : t -> t

  (* [to_shape t shp] : lifts [t] to the shape of [shp] 
     Remark: [t] must be without disjunction. *)
  val to_shape : t -> t -> t

  val remove_disj : t -> t

  (* Adds a block of constraints for the disjunctive domain *)
  val new_cnstr_blck : t -> L.i_loc -> t

  (* Add a constraint to the top-most block.
     If [meet] is true, meet the resulting branch with, respectively,
     the constraint and its negation. *)
  val add_cnstr : t -> meet:bool -> Mtcons.t -> L.i_loc -> t * t

  (* Pop the top-most block of constraints in the disjunctive domain *)
  val pop_cnstr_blck : t -> L.i_loc -> t

  (* Pop all constraints in the disjunctive domain *)
  val pop_all_blcks : t -> t
end


(***************************************)
(* Symbolic Expression Abstract Domain *)
(***************************************)

module type SymExpr = sig
  type t

  (* Make a top value. *)
  val make : unit -> t

  val assign_expr  : ?force:bool -> t -> (mvar * Mtexpr.t) list -> t
  val assign_bexpr : t -> mvar -> btcons -> t
    
  val meet : t -> t -> t
  val join : t -> t -> t
  val widening : t -> t -> t

  val forget_list : t -> mvar list -> t

  val change_environment : t -> mvar list -> t

  val support : t -> mvar list * Bvar.t list

  (* (\* [subst_expr t e] returns an expression [e'] equivalent to
   *    [e] in any state satisfying [t]. *\)
   * val subst_expr : t -> Mtexpr.t -> Mtexpr.t *)

  (* [subst_btcons t c] returns an constraint [c'] equivalent to
     [c] in any state satisfying [t]. *)
  val subst_btcons : t -> btcons -> btcons

  val print : Format.formatter -> t -> unit
end


(*****************************)
(* Points-to Abstract Domain *)
(*****************************)

(* Pointer expressions *)
type ptr_expr = PtVars of mvar list | PtTopExpr

(* Symbolic pointers *)
type ptrs = Ptrs of mem_loc list | TopPtr


module type PointsTo = sig
  type t

  (* make takes as input the set of memory locations of the program *)
  val make : mem_loc list -> t

  val meet : t -> t -> t
  val join : t -> t -> t

  val widening : t -> t -> t

  val forget_list : t -> mvar list -> t
  val is_included : t -> t -> bool

  val var_points_to : t -> mvar -> ptrs
  val assign_ptr_expr : t -> mvar -> ptr_expr -> t

  val print : Format.formatter -> t -> unit
end


(*************************************************)
(* Numerical Domain with Two Levels of Precision *)
(*************************************************)

module type AbsNumT = sig
  module R : AbsDisjType
  module NR : AbsNumType

  val downgrade : R.t -> NR.t
  (* The second argument is used as a shape *)
  val upgrade : NR.t -> R.t -> R.t
end


(************************************************)
(* Abstraction of numerical and boolean values. *)
(************************************************)

(* Add boolean variable abstractions and keep track initialized variables,
   points-to information and alignment of input pointers. *)
module type AbsNumBoolType = sig
  type t

  (* Make a top value defined on the given variables *)
  val make : mvar list -> mem_loc list -> t

  val meet : join_align:bool -> t -> t -> t
  val join : t -> t -> t
  val widening : Mtcons.t option -> t -> t -> t

  val forget_list : t -> mvar list -> t
  val forget_bvar : t -> mvar -> t

  val is_included : t -> t -> bool
  val is_bottom : t -> bool

  (* val expand : t -> mvar -> mvar list -> t
   * val fold : t -> mvar list -> t *)

  val bound_variable : t -> mvar -> Interval.t
  val bound_texpr : t -> Mtexpr.t -> Interval.t

  (* Does not change the points-to information.
     The location option argument must be:
     - [Some info], where [info] is the information attached to the location
     where the assignment takes place, if the [mvar] argument is
     a [Mvalue (Avar _)].
     - anything otherwise. *)
  val assign_sexpr :
    ?force:bool -> t -> minfo option -> (mvar * s_expr) list -> t
  val assign_bexpr : t -> mvar -> btcons -> t

  val var_points_to : t -> mvar -> ptrs
  val assign_ptr_expr : t -> mvar -> ptr_expr -> t

  (* [subst_btcons t c] returns an constraint [c'] equivalent to
     [c] in any state satisfying [t]. *)
  val subst_btcons : t -> btcons -> btcons

  val meet_btcons : t -> btcons -> t

  (* (\* Unify the two abstract values on their least common environment. *\)
   * val unify : t -> t -> t *)

  (* Variables that are removed are first existentially quantified, and
     variables that are introduced are unconstrained. *)
  val change_environment : t -> mvar list -> t
  val remove_vars : t -> mvar list -> t

  (* Make a top value define on the same variables that the argument.
     All variables are assumed *not* initialized.
     All variables alias to everybody. 
     There are no disjunction. *)
  val top_ni : t -> t

  (* [to_shape t shp] : lifts [t] to the shape of [shp] 
     Remark: [t] must be without disjunction. *)
  val to_shape : t -> t -> t

  val remove_disj : t -> t

  val is_init    : t -> atype -> t
  val copy_init  : t -> mvar -> mvar -> t
  val check_init : t -> atype -> bool

  (* [base_align t m ws] state that [m] must be aligned for [ws]. *)
  val base_align : t -> mem_loc -> wsize -> t
  (* [check_align t e ws] checks that [e] is aligned for [ws]. *)
  val check_align : t -> Mtexpr.t -> wsize -> bool

  val print : ?full:bool -> Format.formatter -> t -> unit

  val new_cnstr_blck : t -> L.i_loc -> t
  val add_cnstr      : t -> meet:bool -> Mtcons.t -> L.i_loc -> t * t
  val pop_cnstr_blck : t -> L.i_loc -> t
  val pop_all_blcks  : t -> t
end

