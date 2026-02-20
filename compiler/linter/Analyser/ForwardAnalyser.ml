open Jasmin
open Prog
open Annotation

module type Logic = sig
  type domain

  val initialize : ('info, 'asm) Prog.func -> domain annotation

  val pp : Format.formatter -> Location.i_loc * domain -> unit

  val included : domain -> domain -> bool

  val assume : expr -> domain annotation -> domain annotation * domain annotation

  val merge : domain -> domain -> domain

  val forget : var_i -> domain -> domain annotation

  val funcall : Location.i_loc -> lvals -> funname -> exprs -> domain -> domain annotation

  val syscall :
       Location.i_loc
    -> lvals
    -> (Wsize.wsize * BinNums.positive) Syscall_t.syscall_t
    -> exprs
    -> domain
    -> domain annotation

  val assign : Location.i_loc -> lval -> E.assgn_tag -> ty -> expr -> domain -> domain annotation

  val opn :
    Location.i_loc -> lvals -> E.assgn_tag -> 'asm Sopn.sopn -> exprs -> domain -> domain annotation

  val assertion : Location.i_loc -> string -> expr -> domain -> domain annotation
end

module type S = sig
  type domain

  val analyse_function : ('info, 'asm) Prog.func -> (domain annotation, 'asm) Prog.func
end

(** Functor used to build TreeAnalyser modules*)
module Make (Logic : Logic) : S with type domain = Logic.domain = struct
  (**
    Herited domain type from the [Logic] module
  *)
  type domain = Logic.domain

  (**
    Annotation wrapper type arround the domain type
  *)
  type annot = domain annotation

  (**
    Assign instruction analysis function
  *)
  let analyse_assign (loc : Location.i_loc) (lv : lval) tag ty (expr : expr) (annotation : annot)
      =
      let annotation = Annotation.bind annotation (Logic.assign loc lv tag ty expr) in
      (Cassgn (lv, tag, ty, expr), annotation)

  (**
    Proxy variable builder used in the for loop. (see function [analyse_for])
  *)
  let build_for_proxy_variable loc (x : var_i) : var_i =
      Location.mk_loc loc (GV.clone (Location.unloc x))

  (**
    Assign expression builder (for example [proxy = proxy + 1]) for proxy variable used in for loop. (see function [analyse_for])
  *)
  let build_for_assign_expr (x : var_i) (r : range) : expr =
      let assign_op = Grange.incr_operator r in
      let x_ggvar = {gv= x; gs= Slocal} in
      Papp2 (assign_op, Pvar x_ggvar, Pconst (Z.of_int 1))

  (**
    Condition expression builder (for example [proxy < 10]) for proxy variable used in for loop. (see function [analyse_for])
  *)
  let build_for_condition_expr (x : var_i) (r : range) : expr =
      let gend = Grange.last r in
      let comp_op = Grange.cmp_operator r in
      let x_ggvar = {gv= x; gs= Slocal} in
      Papp2 (comp_op, Pvar x_ggvar, gend)

  (**
  For loop analysis function :
  the logic is to convert the for loop as follow :

    [
    inline int i;
    for i = 0 to 10 {
      ...
    }
  ]

  becomes :

  [
    inline int i;
    inline int i_proxy = 0;
    while (i_proxy < 10) {
      i = i_proxy;
      ...
      i_proxy++;
    }
  ]

  The proxy variable is used to avoid modifying the original variable during the loop.
  The proxy variable is then removed from the annotation after fixpoint is reached.

  For simpler implementation, we do not call the analyse_while function here and prefer to mimic it's behavior.
  *)
  let rec analyse_for
      (loc : Location.i_loc)
      (variable : var_i)
      (range : range)
      (body : ('info, 'asm) stmt)
      in_annotation : (annot, 'asm) instr_r * annot =
      (* Defining proxy variable *)
      let proxy_var = build_for_proxy_variable loc.base_loc variable in
      (* First assign to range begin*)
      let _, annotation =
          analyse_assign loc (Lvar proxy_var) AT_none (Location.unloc variable).v_ty
            (Grange.first range) in_annotation
      in
      (* Building loop out condition *)
      let condition = build_for_condition_expr proxy_var range in
      let rec loop in_annotation =
          let loop_annotation, out_annotation = Logic.assume condition in_annotation in
          let _, loop_annotation =
              (* Assigning proxy_var to for variable*)
              analyse_assign loc (Lvar variable) AT_none (Location.unloc variable).v_ty
                (Pvar {gv= proxy_var; gs= Slocal})
                loop_annotation
          in
          let body, loop_annotation = analyse_stmt body loop_annotation in
          let _, loop_annotation =
              analyse_assign loc (Lvar proxy_var) AT_none (Location.unloc variable).v_ty
                (build_for_assign_expr proxy_var range)
                loop_annotation
          in
          if Annotation.included loop_annotation in_annotation Logic.included then
            (Cfor (variable, range, body), out_annotation)
          else
            loop (Annotation.merge loop_annotation in_annotation Logic.merge)
      in
      let body, annotation = loop annotation in
      let out_annotation = Annotation.bind annotation (Logic.forget proxy_var) in
      (body, out_annotation)
      (* Should we really remove the proxy_var ?*)

  (**
  Analysis of while loop
  *)
  and analyse_while
      (al : E.align)
      (cond : expr)
      ((a, _) : IInfo.t * 'info)
      (b1 : ('info, 'asm) stmt)
      (b2 : ('info, 'asm) stmt)
      (domain : annot) =
      let rec loop (in_annotation : annot) =
          let b1, annotation_s1 = analyse_stmt b1 in_annotation in
          let loop_annotation, result_annotation = Logic.assume cond annotation_s1 in
          let b2, annotation_s2 = analyse_stmt b2 loop_annotation in
          if Annotation.included annotation_s2 in_annotation Logic.included then
            (Cwhile (al, b1, cond, (a, annotation_s1), b2), result_annotation)
          else
            loop (Annotation.merge annotation_s2 in_annotation Logic.merge)
      in
      let cwhile, result = loop domain in
      (cwhile, result)

  and analyse_instr_r
      (loc : Location.i_loc)
      (instr : ('info, 'asm) instr_r)
      (annotation : annot) : (annot, 'asm) instr_r * annot =
      match instr with
      | Cassgn (lv, tag, ty, expr) -> analyse_assign loc lv tag ty expr annotation
      | Copn (lvs, tag, sopn, es) ->
          let annotation = Annotation.bind annotation (Logic.opn loc lvs tag sopn es) in
          (Copn (lvs, tag, sopn, es), annotation)
      | Cassert (msg, e) ->
          let annotation = Annotation.bind annotation (Logic.assertion loc msg e) in
          (Cassert (msg, e), annotation)
      | Ccall (lvs, fn, es) ->
          let annotation = Annotation.bind annotation (Logic.funcall loc lvs fn es) in
          (Ccall (lvs, fn, es), annotation)
      | Csyscall (lvs, sc, es) ->
          let annotation = Annotation.bind annotation (Logic.syscall loc lvs sc es) in
          (Csyscall (lvs, sc, es), annotation)
      | Cif (expr, th, el) ->
          let annotation_th, annotation_el = Logic.assume expr annotation in
          let th, annotation_th = analyse_stmt th annotation_th in
          let el, annotation_el = analyse_stmt el annotation_el in
          (Cif (expr, th, el), Annotation.merge annotation_th annotation_el Logic.merge)
      | Cfor (var, range, bloc) -> analyse_for loc var range bloc annotation
      | Cwhile (align, b1, cond, info, b2) -> analyse_while align cond info b1 b2 annotation

  and analyse_instr (in_annotation : annot) (instr : ('info, 'asm) instr) :
      annot * (annot, 'asm) instr =
      let instr_r, out_annotation = analyse_instr_r instr.i_loc instr.i_desc in_annotation in
      (out_annotation, {instr with i_desc= instr_r; i_info= in_annotation})

  and analyse_stmt (stmt : ('info, 'asm) stmt) in_annotation =
      let out_annotation, stmt = List.fold_left_map analyse_instr in_annotation stmt in
      (stmt, out_annotation)

  let analyse_function (func : ('info, 'asm) Prog.func) : (annot, 'asm) Prog.func =
      let in_domain = Logic.initialize func in
      let body, out_domain = analyse_stmt func.f_body in_domain in
      {func with f_info= out_domain; f_body= body}
end
