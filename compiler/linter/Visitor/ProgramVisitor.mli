(**
    This module is a generic visitor for Jasmin programs (from `Jasmin.Prog`). 
    It is designed to be used on an annotated program (for example produced by `Analyser` module).

    We choose to limit visitor deepness to instruction level. If there is a need to visit expressions, you will need to implement logic yourself.

    It defines two types : 
    - data : Inner state of the visitor. Each function must return a new state
    - annotation : Type of the annotation of decorated Jasmin Program

    It define a function for all logic blocs of a Jasmin Program (function, statement, instruction, etc.).
    Some functions may take a particular function as an argument : 
    - visit_instr : (annotation, 'asm) Jasmin.Prog.instr -> data -> data
    
    this is a function defined by the functor `Visitor.Make` that will be used to visit instructions without having to match their content.

*)
module type PartialVisitor = sig
  type data

  type annotation

  val visit_prog :
       ((annotation, 'asm) Jasmin.Prog.instr -> data -> data)
    -> (annotation, 'asm) Jasmin.Prog.prog
    -> data
    -> data

  val visit_function :
       ((annotation, 'asm) Jasmin.Prog.instr -> data -> data)
    -> (annotation, 'asm) Jasmin.Prog.func
    -> data
    -> data

  val visit_stmt :
       ((annotation, 'asm) Jasmin.Prog.instr -> data -> data)
    -> (annotation, 'asm) Jasmin.Prog.stmt
    -> data
    -> data

  val visit_funcall :
       Jasmin.Location.i_loc
    -> annotation
    -> Jasmin.Prog.lvals
    -> Jasmin.CoreIdent.funname
    -> Jasmin.Prog.exprs
    -> data
    -> data

  val visit_syscall :
       Jasmin.Location.i_loc
    -> annotation
    -> Jasmin.Prog.lvals
    -> Jasmin.BinNums.positive Jasmin.Syscall_t.syscall_t
    -> Jasmin.Prog.exprs
    -> data
    -> data

  val visit_assign :
       Jasmin.Location.i_loc
    -> annotation
    -> Jasmin.Prog.lval
    -> Jasmin.Expr.assgn_tag
    -> Jasmin.Prog.ty
    -> Jasmin.Prog.expr
    -> data
    -> data

  val visit_copn :
       Jasmin.Location.i_loc
    -> annotation
    -> Jasmin.Prog.lvals
    -> Jasmin.Expr.assgn_tag
    -> 'asm Jasmin.Sopn.sopn
    -> Jasmin.Prog.exprs
    -> data
    -> data

  val visit_for :
       ((annotation, 'asm) Jasmin.Prog.instr -> data -> data)
    -> Jasmin.Location.i_loc
    -> annotation
    -> Jasmin.Prog.var_i
    -> int Jasmin.Prog.grange
    -> (annotation, 'asm) Jasmin.Prog.stmt
    -> data
    -> data

  val visit_while :
       ((annotation, 'asm) Jasmin.Prog.instr -> data -> data)
    -> Jasmin.Location.i_loc
    -> annotation
    -> Jasmin.IInfo.t * annotation
    -> Jasmin.Expr.align
    -> (annotation, 'asm) Jasmin.Prog.stmt
    -> Jasmin.Prog.expr
    -> (annotation, 'asm) Jasmin.Prog.stmt
    -> data
    -> data

  val visit_if :
       ((annotation, 'asm) Jasmin.Prog.instr -> data -> data)
    -> Jasmin.Location.i_loc
    -> annotation
    -> Jasmin.Prog.expr
    -> (annotation, 'asm) Jasmin.Prog.stmt
    -> (annotation, 'asm) Jasmin.Prog.stmt
    -> data
    -> data
end

module Visitor : sig
  module type S = sig
    type data

    type annotation

    (*
        Program traversal function. This is the only accepted entrypoint for the visitor.
    *)
    val visit_prog : (annotation, 'asm) Jasmin.Prog.prog -> data -> data
  end

  module Make : functor (V : PartialVisitor) ->
    S with type data = V.data and type annotation = V.annotation
end
