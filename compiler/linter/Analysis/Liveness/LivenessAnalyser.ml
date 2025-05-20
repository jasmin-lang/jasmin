open Jasmin
open Prog
open Analyser.Annotation
open Analyser

(**
    Computes used variables in an lvalue

*)
let lv_dep domain lv =
    match lv with
    | Lvar var -> Sv.remove (L.unloc var) domain
    | _ -> vars_lv domain lv

let lvs_dep domain lvs = List.fold_left lv_dep domain lvs

let pp_sv fmt sv =
    Format.fprintf fmt "{ %a }\n"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
         (fun fmt v -> Format.fprintf fmt "%s" v.v_name) )
      (Sv.to_list sv)

let live_assigns domain lvs exprs =
    let domain = lvs_dep domain lvs in
    Sv.union domain (Prog.vars_es exprs)

module LivenessDomain : BackwardAnalyser.Logic with type domain = Sv.t = struct
  type domain = Sv.t

  let initialize fd = Annotation (Sv.of_list (List.map L.unloc fd.f_ret))

  let pp (fmt : Format.formatter) ((_, domain) : L.i_loc * domain) = pp_sv fmt domain

  let included a b = Sv.subset a b

  let account (expr : expr) (d1 : domain annotation) (d2 : domain annotation) =
    match (d1, d2) with
    | Empty, _ -> d2
    | _, Empty -> d1
    | Annotation d1, Annotation d2 -> Annotation (Sv.union (Prog.vars_e expr) (Sv.union d1 d2))

  let forget (var : var_i) (domain : domain) =
    assert (not (Sv.mem (L.unloc var) domain));
    Annotation domain

  let funcall (_ : Location.i_loc) (lvs : lvals) (_ : funname) (exprs : exprs) (domain : domain) =
      Annotation (live_assigns domain lvs exprs)

  let syscall
    (_ : Location.i_loc)
    (lvs : lvals)
    (_ : BinNums.positive Syscall_t.syscall_t)
    (exprs : exprs)
    (domain : domain) =
    Annotation (live_assigns domain lvs exprs)

  let assign
    (_ : Location.i_loc)
    (lv : lval)
    (_ : E.assgn_tag)
    (_ : ty)
    (expr : expr)
    (domain : domain) =
    Annotation (live_assigns domain [lv] [expr])

  let opn
    (_ : Location.i_loc)
    (lvs : lvals)
    (_ : E.assgn_tag)
    (_ : 'asm Sopn.sopn)
    (exprs : exprs)
    (domain : domain) =
    Annotation (live_assigns domain lvs exprs)
end

include BackwardAnalyser.Make (LivenessDomain)
