(**
    module derived from `Visitor`. It apply given functions to all expressions and variables of the program. 
    For the sake of modularity, we defines three functions to check expressions and variables: 
    - `check_expr` : check an expression (right expression)
    - `check_return_variable` : check a variable that is used as a return value
    - `check_lv_variable` : check lvalues
*)
module type ExpressionCheckerLogic = sig
  type domain

  type self

  val check_expr : self -> domain -> Jasmin.Location.i_loc -> Jasmin.Prog.expr -> self

  val check_return_variable : self -> domain -> Jasmin.Prog.var_i -> self

  val check_lv_variable : self -> domain -> Jasmin.Prog.var_i -> self
end

module ExpressionChecker : sig
  module Make : functor (Logic : ExpressionCheckerLogic) ->
    ProgramVisitor.Visitor.S with type data = Logic.self and type annotation = Logic.domain
end
