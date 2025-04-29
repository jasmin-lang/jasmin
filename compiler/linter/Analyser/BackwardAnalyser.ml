open Jasmin
open Prog
open Types
open Annotation

module type BackwardAnalyserLogic = sig
  (** type of annotation for the program*)
  type domain

  (** Pretty printing function*)
  val pp : Format.formatter -> Location.i_loc * domain -> unit

  val initialize : ('info, 'asm) Prog.func -> domain annotation

  (** Incusion test
     Check if an annotation is included in another one.

     args :
     - prev : previous domain
     - domain : current domain

     returns :
     - bool : true if the fixpoint is reached, false otherwise

    Inclusion : for all A1, A2 , (included A1 A2) => for all s , (s in I(A2) => s in I(A1)) 
  *)

  val included : domain -> domain -> bool

  (**
    Account : for all A1, A2, e, s , s in I(account e A1 A2) => if [e]s then s in I(A1) else s in I(A2)
    eq : for all A1, A2, e, s , s in I(account e A1 A2) => s in I(if [e]s then A1 else A2)
  *)
  val account : int gexpr -> domain annotation -> domain annotation -> domain annotation

  (** Function that remove a proxy variable from the annotation if necessary
       Some part of the tree walking will introduce proxy variables to handle some specific cases.
       This function is called to remove them from the annotation when they are not needed anymore
     *)
  val forget : int gvar_i -> domain -> domain annotation

  val funcall : Location.i_loc -> int glvals -> funname -> int gexprs -> domain -> domain annotation

  val syscall :
       Location.i_loc
    -> int glvals
    -> BinNums.positive Syscall_t.syscall_t
    -> int gexprs
    -> domain
    -> domain annotation

  val assign :
       Location.i_loc
    -> int glval
    -> E.assgn_tag
    -> int gty
    -> int gexpr
    -> domain
    -> domain annotation

  val opn :
       Location.i_loc
    -> int glval list
    -> E.assgn_tag
    -> 'asm Sopn.sopn
    -> int gexprs
    -> domain
    -> domain annotation
end

module BackwardAnalyser = struct
  module type S = sig
    (** anotation type*)
    type domain

    (**
       Entrypoint for analysis. Using domain, the domain for the previous instruction is computed. Annotation are then generated using `AnalyserLogic.to_annotation` function

       args :
       - Prog.func (function to analyse)
       - annotation (initial annotation that will be modified during analysis)

       returns :
       - Prog.func (annotated function)
       - annotation (out annotation)
    *)
    val analyse_function : ('info, 'asm) Prog.func -> (domain annotation, 'asm) Prog.func
  end

  (** Functor used to build TreeAnalyser modules*)
  module Make
      (L : BackwardAnalyserLogic)
  (*: S with type annotation = L.annotation and type domain = L.domain  *) =
  struct
    type domain = L.domain

    (** type of the annotation*)
    type annot = L.domain annotation

    let analyse_assign
        (loc : Location.i_loc)
        (lv : int glval)
        tag
        ty
        (expr : int gexpr)
        (annotation : annot) : (int, annot, 'asm) ginstr_r * annot =
        let annotation = Annotation.bind annotation (L.assign loc lv tag ty expr) in
        (Cassgn (lv, tag, ty, expr), annotation)

    let build_for_proxy_variable loc (x : int gvar_i) : var_i =
        Location.mk_loc loc (GV.clone (Location.unloc x))

    let build_for_assign_expr (x : int gvar_i) (r : int grange) : int gexpr =
        let assign_op = Grange.incr_operator r in
        let x_ggvar = {gv= x; gs= Slocal} in
        Papp2 (assign_op, Pvar x_ggvar, Pconst (Z.of_int 1))

    let build_for_condition_expr (x : int gvar_i) (r : int grange) : int gexpr =
        let gend = Grange.last r in
        let comp_op = Grange.cmp_operator r in
        let x_ggvar = {gv= x; gs= Slocal} in
        Papp2 (comp_op, Pvar x_ggvar, gend)

    let rec analyse_for
        (loc : Location.i_loc)
        variable
        (range : int grange)
        (body : ('info, 'asm) stmt)
        (out_annotation : annot) : (int, annot, 'asm) ginstr_r * annot =
        let proxy_var = build_for_proxy_variable loc.base_loc variable in
        let condition = build_for_condition_expr proxy_var range in
        let rec loop out_annotation =
            let _, annotation =
                (* Incrementing loop counter (proxy_var (+|-)= 1) *)
                analyse_assign loc (Lvar proxy_var) AT_none (Location.unloc variable).v_ty
                  (build_for_assign_expr proxy_var range)
                  out_annotation
            in
            let body, annotation = analyse_stmt body annotation in
            let _, domain =
                (* Assigning proxy_var to for variable*)
                analyse_assign loc (Lvar variable) AT_none (Location.unloc variable).v_ty
                  (Pvar {gv= proxy_var; gs= Slocal})
                  annotation
            in
            let domain = L.account condition domain out_annotation in
            (* Check if the loop is finished *)
            if Annotation.included domain out_annotation L.included then
              (Cfor (variable, range, body), domain)
            else
              loop domain
        in
        let body, in_annotation = loop out_annotation in
        let _, in_annotation =
            (* Assigning proxy_var to range beginning*)
            analyse_assign loc (Lvar proxy_var) AT_none (Location.unloc variable).v_ty
              (Grange.first range) in_annotation
        in
        let in_annotation = Annotation.bind in_annotation (L.forget proxy_var) in
        (body, in_annotation)

    and analyse_while
        (al : E.align)
        (cond : int gexpr)
        ((a, _) : IInfo.t * 'info)
        (b1 : (int, 'info, 'asm) gstmt)
        (b2 : (int, 'info, 'asm) gstmt)
        (out_annotation : annot) : (int, annot, 'asm) ginstr_r * annot =
        (*
        Invariant : L.included out_domain cond_out_domain
        *)
        let domain = L.account cond out_annotation Empty in
        let rec loop (cond_out_annotation : annot) =
            let b1, annotation_b1 = analyse_stmt b1 cond_out_annotation in
            let b2, annotation_b2 = analyse_stmt b2 annotation_b1 in
            let annotation = L.account cond annotation_b2 cond_out_annotation in
            if Annotation.included annotation cond_out_annotation L.included then
              (Cwhile (al, b1, cond, (a, domain), b2), annotation_b1)
            else
              loop annotation
        in
        loop domain

    and analyse_instr_r
        (loc : Location.i_loc)
        (instr : (int, 'info, 'asm) ginstr_r)
        (annotation : annot) : (int, annot, 'asm) ginstr_r * annot =
        match instr with
        | Cassgn (lv, tag, ty, expr) -> analyse_assign loc lv tag ty expr annotation
        | Copn (lvs, tag, sopn, es) ->
            let annotation = Annotation.bind annotation (L.opn loc lvs tag sopn es) in
            (Copn (lvs, tag, sopn, es), annotation)
        | Ccall (lvs, fn, es) ->
            let annotation = Annotation.bind annotation (L.funcall loc lvs fn es) in
            (Ccall (lvs, fn, es), annotation)
        | Csyscall (lvs, sc, es) ->
            let annotation = Annotation.bind annotation (L.syscall loc lvs sc es) in
            (Csyscall (lvs, sc, es), annotation)
        | Cif (cond, th, el) ->
            let th, annotation_th = analyse_stmt th annotation in
            let el, annotation_el = analyse_stmt el annotation in
            (Cif (cond, th, el), L.account cond annotation_th annotation_el)
        | Cfor (var, range, bloc) -> analyse_for loc var range bloc annotation
        | Cwhile (align, b1, cond, info, b2) -> analyse_while align cond info b1 b2 annotation

    and analyse_instr (out_annotation : annot) (instr : ('info, 'asm) instr) :
        (annot, 'asm) instr * annot =
        let instr_r, in_annotation = analyse_instr_r instr.i_loc instr.i_desc out_annotation in
        ( {i_desc= instr_r; i_loc= instr.i_loc; i_info= in_annotation; i_annot= instr.i_annot}
        , in_annotation )

    and analyse_stmt (stmt : ('info, 'asm) stmt) (out_annotation : annot) :
        (annot, 'asm) stmt * annot =
        let stmt, in_annotation =
            List.fold_right
              (fun instr (acc, out_annotation) ->
                let instr, in_annotation = analyse_instr out_annotation instr in
                (instr :: acc, in_annotation) )
              stmt ([], out_annotation)
        in
        (stmt, in_annotation)

    let analyse_function (func : ('info, 'asm) Prog.func) : (annot, 'asm) Prog.func =
        let out_annotation = L.initialize func in
        (* The function is analysed in the context of the initial domain *)
        let body, in_annotation = analyse_stmt func.f_body out_annotation in
        {func with f_info= in_annotation; f_body= body}
  end
end
