(**
    module derived from [ProgramVisitor]. It apply given functions to all expressions and left values of the program.
    For the sake of modularity, we defines three functions to check expressions and left values:
    - [check_expr] : check an expression
    - [check_return_variable] : check a variable that is used as a return value
    - [check_lv_variable] : check lvalues
*)
module type Logic = sig
  type domain

  type self

  val check_expr : self -> domain -> Jasmin.Location.i_loc -> Jasmin.Prog.expr -> self

  val check_return_variable : self -> domain -> Jasmin.Prog.var_i -> self

  val check_lv_variable : self -> domain -> Jasmin.Prog.var_i -> self
end

module Make : functor (Logic : Logic) ->
  ProgramVisitor.S with type data = Logic.self and type annotation = Logic.domain
