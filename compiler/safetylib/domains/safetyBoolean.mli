open SafetyInterfaces

(*------------------------------------------------------------*)
(* Numerical Domain with Two Levels of Precision *)

module AbsNumTMake (Arch : SafetyArch.SafetyArch) (PW : ProgWrap with type extended_op = Arch.extended_op) : AbsNumT

(*------------------------------------------------------------*)
(* Abstraction of numerical and boolean values. *)

(* Add boolean variable abstractions and keep track initialized variables,
   points-to information and alignment of input pointers.
   The boolean abstraction use a non-relational abstract domain. *)
module AbsBoolNoRel (AbsNum : AbsNumT) (Pt : PointsTo) (Sym : SymExpr)
  : AbsNumBoolType
