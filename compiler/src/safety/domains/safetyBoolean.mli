open SafetyInterfaces

(*------------------------------------------------------------*)
(* Numerical Domain with Two Levels of Precision *)

module AbsNumTMake (PW : ProgWrap) : AbsNumT

(*------------------------------------------------------------*)
(* Abstraction of numerical and boolean values. *)

(* Add boolean variable abstractions and keep track of initialized variables 
   and points-to information.
   The boolean abstraction use a non-relational abstract domain. *)
module AbsBoolNoRel (AbsNum : AbsNumT) (Pt : PointsTo) (Sym : SymExpr)
  : AbsNumBoolType
