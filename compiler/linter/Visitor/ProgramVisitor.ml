open Jasmin
open Prog

module type PartialVisitor = sig
  type data

  type annotation

  val visit_prog :
    ((annotation, 'asm) Prog.instr -> data -> data) -> (annotation, 'asm) Prog.prog -> data -> data

  val visit_function :
    ((annotation, 'asm) Prog.instr -> data -> data) -> (annotation, 'asm) Prog.func -> data -> data

  val visit_stmt :
    ((annotation, 'asm) Prog.instr -> data -> data) -> (annotation, 'asm) Prog.stmt -> data -> data

  val visit_funcall : Location.i_loc -> annotation -> lvals -> funname -> exprs -> data -> data

  val visit_syscall :
       Location.i_loc
    -> annotation
    -> lvals
    -> BinNums.positive Syscall_t.syscall_t
    -> exprs
    -> data
    -> data

  val visit_assign : L.i_loc -> annotation -> lval -> E.assgn_tag -> ty -> expr -> data -> data

  val visit_copn :
    L.i_loc -> annotation -> lvals -> E.assgn_tag -> 'asm Sopn.sopn -> exprs -> data -> data

  val visit_for :
       ((annotation, 'asm) Prog.instr -> data -> data)
    -> L.i_loc
    -> annotation
    -> var_i
    -> int grange
    -> (annotation, 'asm) Prog.stmt
    -> data
    -> data

  val visit_while :
       ((annotation, 'asm) Prog.instr -> data -> data)
    -> L.i_loc
    -> annotation
    -> IInfo.t * annotation
    -> E.align
    -> (annotation, 'asm) Prog.stmt
    -> expr
    -> (annotation, 'asm) Prog.stmt
    -> data
    -> data

  val visit_if :
       ((annotation, 'asm) Prog.instr -> data -> data)
    -> L.i_loc
    -> annotation
    -> expr
    -> (annotation, 'asm) Prog.stmt
    -> (annotation, 'asm) Prog.stmt
    -> data
    -> data
end

module Visitor = struct
  module type S = sig
    type data

    type annotation

    val visit_prog : (annotation, 'asm) Prog.prog -> data -> data
  end

  module Make (V : PartialVisitor) : S with type data = V.data and type annotation = V.annotation =
  struct
    type data = V.data

    type annotation = V.annotation

    let rec _visit_instr (instr : (int, V.annotation, 'asm) ginstr) (data : V.data) : V.data =
        match instr.i_desc with
        | Prog.Cassgn (l, a, ty, e) -> V.visit_assign instr.i_loc instr.i_info l a ty e data
        | Prog.Copn (l, a, sopn, es) -> V.visit_copn instr.i_loc instr.i_info l a sopn es data
        | Prog.Cif (e, s1, s2) -> V.visit_if _visit_instr instr.i_loc instr.i_info e s1 s2 data
        | Prog.Cfor (i, r, s) -> V.visit_for _visit_instr instr.i_loc instr.i_info i r s data
        | Prog.Cwhile (a, s1, e, info, s2) ->
            V.visit_while _visit_instr instr.i_loc instr.i_info info a s1 e s2 data
        | Prog.Ccall (l, f, es) -> V.visit_funcall instr.i_loc instr.i_info l f es data
        | Prog.Csyscall (l, s, es) -> V.visit_syscall instr.i_loc instr.i_info l s es data

    let visit_prog prog data : data = V.visit_prog _visit_instr prog data
  end
end

(* simple example of a visitor for copy-paste and avoiding rewriting *)
(* module ExampleVisitor : PartialVisitor = struct
     type data = Sf.t

     type annotation = unit

     let visit_funcall
         (loc : L.i_loc)
         (annot : annotation)
         (lvs : lvals)
         (funname : funname)
         (params : exprs)
         (data : data) : data =
         data

     let visit_syscall
         (loc : L.i_loc)
         (annot : annotation)
         (lvs : lvals)
         (syscall : 'asm Syscall_t.syscall_t)
         (params : exprs)
         (data : data) : data =
         data

     let visit_assign
         (loc : L.i_loc)
         (annot : annotation)
         (lv : lval)
         (tag : E.assgn_tag)
         (gty : ty)
         (expr : expr)
         (data : data) : data =
         data

     let visit_copn
         (loc : L.i_loc)
         (annot : annotation)
         (lvs : lvals)
         (tag : E.assgn_tag)
         (opn : 'asm Sopn.sopn)
         (exprs : exprs)
         (data : data) : data =
         data

     let visit_for
         (visit_instr : (annotation, 'asm) instr -> data -> data)
         (loc : L.i_loc)
         (annot : annotation)
         (var : var_i)
         (range : range)
         (stmt : (annotation, 'asm) stmt)
         (data : data) : data =
         data

     let visit_while
         (visit_instr : (annotation, 'asm) instr -> data -> data)
         (loc : L.i_loc)
         (annot : annotation)
         (info : IInfo.t * annotation)
         (align : E.align)
         (b1 : (annotation, 'asm) stmt)
         (cond : expr)
         (b2 : (annotation, 'asm) stmt)
         (data : data) : data =
         data

     let visit_if
         (visit_instr : (annotation, 'asm) instr -> data -> data)
         (loc : L.i_loc)
         (annot : annotation)
         (cond : expr)
         (th : (annotation, 'asm) stmt)
         (el : (annotation, 'asm) stmt)
         (data : data) : data =
         data

     let visit_stmt visit_instr stmt data : data = data

     let visit_function
         (visit_instr : (annotation, 'asm) instr -> data -> data)
         (func : (annotation, 'asm) func)
         data : data =
         data

     let visit_prog
         (visit_instr : (annotation, 'asm) instr -> data -> data)
         (prog : (annotation, 'asm) prog)
         data : data =
         data
   end *)
