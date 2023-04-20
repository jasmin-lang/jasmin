open SafetyInterfaces

(* Disjunctive domain. Leaves are already constrained under the branch
   conditions. *)
module AbsDisj (A : AbsNumProdT) : AbsDisjType
  
(* Lifts a non-relational domain without disjunctions. *)
module LiftToDisj (A : AbsNumType) : AbsDisjType
