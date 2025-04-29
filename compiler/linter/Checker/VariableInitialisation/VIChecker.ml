open Jasmin
open Prog
open Analysis.ReachingDefinitions
open Types
open VIError
open Error.CompileError
open Analyser.Annotation
open Visitor


type check_mode =
| Strict
| NotStrict

(**
Visitor inner state
mode : check_mode mode of the analysis
errors : list of error found during analysis
*)
type vi_data =
{ mode: check_mode
; errors: compile_error list }


let is_local_var (v : var) = not (Jasmin.Prog.V.is_glob v)

(*
Error checking function of the analysis. Check if variable `var` passed as argument is initialised in the current domain. It also check if the variable is local (because initialisation problem only make sense for local variables).
args :
- data : vi_data state of the visitor
- domain : RDDomain.t In domain of the reaching definition analysis for current instruction
- loc : Jasmin.Location.t location of the variable
- var : var variable to check
return : vi_data (updated the list of error if `var` is not initialised)
*)
let check_iv_error (data : vi_data) (domain : RDDomain.t) (loc : Jasmin.Location.t) (var : var) =
    if is_local_var var then
      match Mv.find_opt var domain with
      | None -> assert false (*This case is not possible with current version*)
      | Some iset ->
      match data.mode with
      | Strict ->
          if SIloc.mem Default iset then
            {data with errors= create_vi_error var loc :: data.errors}
          else
            data
      | NotStrict ->
          if SIloc.equal iset (SIloc.singleton Default) then
            {data with errors= create_vi_error var loc :: data.errors}
          else
            data
    else
      data

(**
Pre error checking function. It is used to check if variable `var` is an non ptr array (because non ptr array are by default initialised in Jasmin specification).
args :
- data : vi_data state of the visitor
- domain : RDDomain.t In domain of the reaching definition analysis for current instruction
- var : var_i variable to check
return : vi_data (updated state)
*)
let check_iv_error (data : vi_data) (domain : RDDomain.t) (var : var_i) : vi_data =
    let loc, var = (L.loc var, L.unloc var) in
    match var.v_ty with
    | Arr _ -> (
        match var.v_kind with
        | Stack Direct
         |Reg (_, Direct) ->
            data
        | _ -> check_iv_error data domain loc var )
    | _ -> check_iv_error data domain loc var

module VariableInitialisationLogic :
  ExpressionChecker.Logic
    with type domain = RDDomain.t annotation
     and type self = vi_data = struct
  type domain = RDDomain.t annotation

  type self = vi_data

  (**
  Check variable initialisation for expressions in the program
  args :
  - self : (vi_data) state of the visitor
  - domain : (RDDomain.t) In domain of the reaching definition analysis for current instruction
  - expr : (expr) checked expression
  *)
  let rec check_expr
      (self : self)
      (domain : domain)
      (loc : Jasmin.Location.i_loc)
      (expr : Jasmin.Prog.expr) : self =
      match expr with
      | Pconst _ -> self
      | Pbool _ -> self
      | Parr_init _ -> self
      | Pvar var -> check_iv_error self (unwrap domain) var.gv
      | Pget (_, _, _, var, expr) ->
          let self = check_expr self domain loc expr in
          check_iv_error self (unwrap domain) var.gv
      | Psub (_, _, _, var, expr) ->
          let self = check_expr self domain loc expr in
          check_iv_error self (unwrap domain) var.gv
      | Pload (_, _, expr) ->
          check_expr self domain loc expr
      | Papp1 (_, expr) -> check_expr self domain loc expr
      | Papp2 (_, l, r) -> check_expr (check_expr self domain loc l) domain loc r
      | PappN (_, exprs) -> List.fold_left (fun d e -> check_expr d domain loc e) self exprs
      | Pif (_, e1, e2, e3) ->
          let self = check_expr self domain loc e1 in
          let self = check_expr self domain loc e2 in
          check_expr self domain loc e3

  let check_return_variable (self : self) (domain : domain) (var : Jasmin.Prog.var_i) : self =
      check_iv_error self (unwrap domain) var

  (**
  Check for variable initialisation in left values. It apply initialisation check for expressions in left values (array access, slice, memory access).
    args :
    - self : vi_data state of the visitor
    - domain : RDDomain.t In domain of the reaching definition analysis for current instruction
    - lv : lval left value to check
    return : vi_data (updated state)
  *)
  let check_lv_variable (self : self) (domain : domain) (var : Jasmin.Prog.var_i) : self =
      check_iv_error self (unwrap domain) var
end

module VIVisitor :
  ProgramVisitor.S
    with type data = vi_data
     and type annotation = Analysis.ReachingDefinitions.RDDomain.t annotation =
  ExpressionChecker.Make (VariableInitialisationLogic)

let initial_state : vi_data = {mode= NotStrict; errors= []}

let check_vi ((globs, funcs) : ('info, 'asm) prog) (mode : check_mode) : compile_error list =
    let funcs =
        List.map
          (fun f ->
            let f = Analysis.ReachingDefinitions.RDAnalyser.analyse_function f in
            f )
          funcs
    in
    let prog = (globs, funcs) in
    let data = {initial_state with mode} in
    let data = VIVisitor.visit_prog prog data in
    List.rev data.errors
