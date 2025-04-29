open ProgramVisitor

module type ExpressionCheckerLogic = sig
  type domain

  type self

  val check_expr : self -> domain -> Jasmin.Location.i_loc -> Jasmin.Prog.expr -> self

  val check_return_variable : self -> domain -> Jasmin.Prog.var_i -> self

  val check_lv_variable : self -> domain -> Jasmin.Prog.var_i -> self
end

module ExpressionChecker = struct
  module Make (Logic : ExpressionCheckerLogic) = struct
    module VisitorLogic :
      PartialVisitor with type annotation = Logic.domain and type data = Logic.self = struct
      type data = Logic.self

      type annotation = Logic.domain

      let check_lv
          (self : data)
          (domain : annotation)
          (lv : Jasmin.Prog.lval)
          (loc : Jasmin.Location.i_loc) : data =
          match lv with
          | Lnone _
           |Lvar _ ->
              self
          | Lmem (_, _, gv, expr)
           |Laset (_, _, _, gv, expr)
           |Lasub (_, _, _, gv, expr) ->
              let self = Logic.check_expr self domain loc expr in
              Logic.check_lv_variable self domain gv

      let visit_funcall
          (loc : Jasmin.Location.i_loc)
          (domain : annotation)
          (lvs : Jasmin.Prog.lvals)
          (_ : Jasmin.Prog.funname)
          (params : Jasmin.Prog.exprs)
          (self : data) : data =
          let self = List.fold_left (fun self lv -> check_lv self domain lv loc) self lvs in
          List.fold_left (fun self expr -> Logic.check_expr self domain loc expr) self params

      let visit_syscall
          (loc : Jasmin.Location.i_loc)
          (domain : annotation)
          (lvs : Jasmin.Prog.lvals)
          (_ : 'asm Jasmin.Syscall_t.syscall_t)
          (params : Jasmin.Prog.exprs)
          (self : data) : data =
          let self = List.fold_left (fun self lv -> check_lv self domain lv loc) self lvs in
          List.fold_left (fun self expr -> Logic.check_expr self domain loc expr) self params

      let visit_assign
          (loc : Jasmin.Location.i_loc)
          (domain : annotation)
          (lv : Jasmin.Prog.lval)
          (_ : Jasmin.Expr.assgn_tag)
          (_ : Jasmin.Prog.ty)
          (expr : Jasmin.Prog.expr)
          (self : data) : data =
          let self = check_lv self domain lv loc in
          Logic.check_expr self domain loc expr

      let visit_copn
          (loc : Jasmin.Location.i_loc)
          (domain : annotation)
          (lvs : Jasmin.Prog.lvals)
          (_ : Jasmin.Expr.assgn_tag)
          (_ : 'asm Jasmin.Sopn.sopn)
          (exprs : Jasmin.Prog.exprs)
          (self : data) : data =
          let self = List.fold_left (fun self lv -> check_lv self domain lv loc) self lvs in
          List.fold_left (fun self expr -> Logic.check_expr self domain loc expr) self exprs

      let rec visit_for
          (visit_instr : (annotation, 'asm) Jasmin.Prog.instr -> data -> data)
          (loc : Jasmin.Location.i_loc)
          (domain : annotation)
          (_ : Jasmin.Prog.var_i)
          ((_, r1, r2) : int Jasmin.Prog.grange)
          (stmt : (annotation, 'asm) Jasmin.Prog.stmt)
          (self : data) : data =
          let self = Logic.check_expr self domain loc r1 in
          let self = Logic.check_expr self domain loc r2 in
          visit_stmt visit_instr stmt self

      and visit_while
          (visit_instr : (annotation, 'asm) Jasmin.Prog.instr -> data -> data)
          (loc : Jasmin.Location.i_loc)
          (_ : annotation)
          ((_, domain) : Jasmin.IInfo.t * annotation)
          (_ : Jasmin.Expr.align)
          (b1 : (annotation, 'asm) Jasmin.Prog.stmt)
          (cond : Jasmin.Prog.expr)
          (b2 : (annotation, 'asm) Jasmin.Prog.stmt)
          (self : data) : data =
          let self = visit_stmt visit_instr b1 self in
          let self = Logic.check_expr self domain loc cond in
          visit_stmt visit_instr b2 self

      and visit_if
          (visit_instr : (annotation, 'asm) Jasmin.Prog.instr -> data -> data)
          (loc : Jasmin.Location.i_loc)
          (domain : annotation)
          (cond : Jasmin.Prog.expr)
          (th : (annotation, 'asm) Jasmin.Prog.stmt)
          (el : (annotation, 'asm) Jasmin.Prog.stmt)
          (self : data) : data =
          let self = Logic.check_expr self domain loc cond in
          let self = visit_stmt visit_instr th self in
          visit_stmt visit_instr el self

      and visit_stmt visit_instr stmt self : data =
          List.fold_left (fun self instr -> visit_instr instr self) self stmt

      let visit_function
          (visit_instr : (annotation, 'asm) Jasmin.Prog.instr -> data -> data)
          (func : (annotation, 'asm) Jasmin.Prog.func)
          self : data =
          let self = visit_stmt visit_instr func.f_body self in
          List.fold_left
            (fun self rv -> Logic.check_return_variable self func.f_info rv)
            self func.f_ret

      let visit_prog
          (visit_instr : (annotation, 'asm) Jasmin.Prog.instr -> data -> data)
          ((_, funcs) : (annotation, 'asm) Jasmin.Prog.prog)
          self : data =
          List.fold_left (fun self f -> visit_function visit_instr f self) self funcs
    end

    include ProgramVisitor.Visitor.Make (VisitorLogic)
  end
end
