



let bound_list (bound: 'a -> 'a -> 'a) (minimum : 'a) (lst: 'a list): 'a =
  List.fold_left (fun acc x -> bound acc x) minimum lst


module Resolution = struct

  (*
  resolution time of a program item : it correspond to the time where information on it are known :
    variable :
      - Static : known at compile time, ie inline variables
      - Dynamic : known at runtime, ie all other variables
    expression :
      - Static : contains only static variables and constants
      - Dynamic : all other expressions
    lval : resolution time of target variable
    instruction :
      assignment :
        - Static if it assigns a static left value
        - Dynamic otherwise
      control flow :
        return the minimum resolution time of the branches

  *)
  type t = Static | Dynamic

  let max (res1: t) (res2: t) : t =
    match res1, res2 with
    | Static, Dynamic -> Dynamic
    | Dynamic, Static -> Dynamic
    | Static, Static -> Static
    | Dynamic, Dynamic -> Dynamic

  let min (res1: t) (res2: t) : t =
    match res1, res2 with
    | Static, Dynamic -> Static
    | Dynamic, Static -> Static
    | Static, Static -> Static
    | Dynamic, Dynamic -> Dynamic

  let (<) (res1: t) (res2: t) : bool =
    match res1, res2 with
    | Static, Dynamic -> true
    | Dynamic, Static -> false
    | Static, Static -> false
    | Dynamic, Dynamic -> false

  (*
    Check variable resolution time : all variables are dynamic except inline variables, which diseappear during compilation.
  *)
  let of_var (var: Jasmin.Prog.var) : t =
    if var.v_kind = Inline then Static
    else Dynamic

  let rec of_expr (expr: Jasmin.Prog.expr) : t =
    match expr with
    | Jasmin.Prog.Pconst _ -> Static
    | Jasmin.Prog.Pbool _ -> Static
    | Jasmin.Prog.Parr_init _ -> Static
    | Jasmin.Prog.Pvar v -> of_var (Jasmin.Location.unloc v.gv)
    | Jasmin.Prog.Pget (_, _, _, var, e) -> max (of_var (Jasmin.Location.unloc var.gv)) (of_expr e)
    | Jasmin.Prog.Psub (_, _, _, var, e) -> max (of_var (Jasmin.Location.unloc var.gv)) (of_expr e)
    | Jasmin.Prog.Pload (_, _, e) -> (of_expr e)
    | Jasmin.Prog.Papp1 (_, e) -> of_expr e
    | Jasmin.Prog.Papp2 (_, e1, e2) -> max (of_expr e1) (of_expr e2)
    | Jasmin.Prog.PappN (_, es) -> bound_list max Static (List.map of_expr es)
    | Jasmin.Prog.Pif (_, e1, e2, e3) -> max (max (of_expr e1) (of_expr e2)) (of_expr e3)

  let of_lv (lv : Jasmin.Prog.lval) : t =
    match lv with
      | Jasmin.Prog.Lnone (_, _) -> Dynamic
      | Jasmin.Prog.Lmem (_, _, _, _) -> Dynamic (* fishy line here : inline int x; [x]=3; need review*)
      | Jasmin.Prog.Lvar v
      | Jasmin.Prog.Laset (_, _, _, v, _)
      | Jasmin.Prog.Lasub (_, _, _, v, _) -> of_var (Jasmin.Location.unloc v) (* resolution of assigned variable *)

end

(* ============================================================================================ *)
(* Errors raised by the check *)

let build_sd_lval_error (loc: Jasmin.Location.t) (var : Jasmin.Prog.var) (expr : Jasmin.Prog.expr) : Error.CompileError.t =
  {
    location = loc;
    code = "SD-E001";
    error_strategy = Recoverable;
    to_text = (fun fmt ->
      Format.fprintf fmt "Static to dynamic error: variable '%s' is static (inline) but assigned a dynamic expression %a"
        var.v_name (Jasmin.Printer.pp_expr ~debug:false) expr);
  }

let build_sd_expr_error (loc: Jasmin.Location.t) (lv: Jasmin.Prog.lval) (expr : Jasmin.Prog.expr) : Error.CompileError.t =
  {
    location = loc;
    code = "SD-E002";
    error_strategy = Recoverable;
    to_text = (fun fmt ->
      Format.fprintf fmt "Static to dynamic error: left value '%a' is static (target inline variable) but is assigned a dynamic expression %a"
        (Jasmin.Printer.pp_lval ~debug:false) lv (Jasmin.Printer.pp_expr ~debug:false) expr);
  }

let build_sd_syscall_error (loc: Jasmin.Location.t) (lv: Jasmin.Prog.lval) : Error.CompileError.t =
  {
    location = loc;
    code = "SD-E003";
    error_strategy = Recoverable;
    to_text = (fun fmt ->
      Format.fprintf fmt "Static to dynamic error: trying to assign a syscall (which is dynamic) to static left values %a"
        (Jasmin.Printer.pp_lval ~debug:false) lv);
  }

let build_sd_call_error (loc: Jasmin.Location.t) (lv: Jasmin.Prog.lval) (exprs: Jasmin.Prog.expr list) (funname: Jasmin.CoreIdent.funname): Error.CompileError.t =
  {
    location = loc;
    code = "SD-E004";
    error_strategy = Recoverable;
    to_text = fun fmt ->
      Format.fprintf fmt "Static to dynamic error: trying to assign a the result of dynamic function call '%s' to static left-value '%a'. The call is dynamic because of expressions %a"
        funname.fn_name
        (Jasmin.Printer.pp_lval ~debug:false) lv
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") (Jasmin.Printer.pp_expr ~debug:false)) exprs
        ;
  }

let build_sd_if_error (loc: Jasmin.Location.t) : Error.CompileError.t =
  {
    location = loc;
    code = "SD-E005";
    error_strategy = Recoverable;
    to_text = (fun fmt ->
      Format.fprintf fmt "Static to dynamic error: condition of if statement is dynamic but branches are static."
    )
  }

let build_sd_while_error (loc: Jasmin.Location.t) : Error.CompileError.t =
  {
    location = loc;
    code = "SD-E006";
    error_strategy = Recoverable;
    to_text = (fun fmt ->
      Format.fprintf fmt "Static to dynamic error: condition of while statement is dynamic but branches are static."
    )
  }


(* ============================================================================================ *)
(* The checker itself *)

let check_lval_inner (lval: Jasmin.Prog.lval) : Error.CompileError.t list =
  match lval with
  | Jasmin.Prog.Lnone (_, _)
  | Jasmin.Prog.Lvar _
  | Jasmin.Prog.Lmem (_, _, _, _) -> [] (* if resolution definition of mem is changed, we should add a case to handle Lmem*)
  | Jasmin.Prog.Laset (_, _, _, v, expr)
  | Jasmin.Prog.Lasub (_, _, _,v,expr) ->
    let var_res = Resolution.of_var (Jasmin.Location.unloc v) in
    let expr_res = Resolution.of_expr expr in
    if var_res < expr_res then
      let error = build_sd_lval_error (Jasmin.Location.loc v) (Jasmin.Location.unloc v) expr in
      [error]
    else []

let check_lval_outer (loc: Jasmin.Location.t) (lval: Jasmin.Prog.lval) (expr : Jasmin.Prog.expr) : Error.CompileError.t list =
  let lv_res = Resolution.of_lv lval in
  let expr_res = Resolution.of_expr expr in
  if lv_res < expr_res then
    let error = build_sd_expr_error loc lval expr in
    [error]
  else []

let check_assign (loc: Jasmin.Location.t) (lval: Jasmin.Prog.lval) (expr : Jasmin.Prog.expr) : Error.CompileError.t list * Resolution.t =
  let inner_errors = check_lval_inner lval in
  let outer_errors = check_lval_outer loc lval expr in
  let lv_resolution = Resolution.of_lv lval in
  (inner_errors @ outer_errors, lv_resolution)

let check_function (func: ('info,'asm) Jasmin.Prog.func)  =
  let errors = ref [] in
  let rec check_instr (instr: ('info,'asm) Jasmin.Prog.instr) : Resolution.t =
    match instr.i_desc with
    | Jasmin.Prog.Cassgn (lv, _, _, expr) ->
      let (errs, lvs_resolution) = check_assign (instr.i_loc.base_loc) lv expr in
      (* if the assignment is dynamic, we add the error to the list *)
      errors := !errors @ errs;
      lvs_resolution

    | Jasmin.Prog.Copn (lvs, _, _, exprs) ->
      List.fold_left (
        fun (res) (lv, expr) ->
          let (lv_errors, lv_res) = check_assign (instr.i_loc.base_loc) lv expr in
          errors := !errors @ lv_errors;
          Resolution.min res lv_res
      )
      (Resolution.Dynamic)
      (List.combine lvs exprs)

    | Jasmin.Prog.Csyscall (lvs, _,_) ->
      List.fold_left (
        fun acc lv ->
          let lv_res = Resolution.of_lv lv in
          begin
          if (lv_res = Resolution.Static) then
            let error = build_sd_syscall_error (instr.i_loc.base_loc) lv in
            errors := !errors @ [error]
          end;
          Resolution.min acc lv_res
      ) (Resolution.Dynamic) lvs

    | Jasmin.Prog.Ccall (lvs, fname, exprs) ->
      let dynamic_exprs = List.filter_map (
          fun e ->
            match Resolution.of_expr e with
            | Resolution.Dynamic -> Some e
            | Resolution.Static -> None
      )  exprs in
      List.fold_left (
        fun (res) lv ->
          match Resolution.of_lv lv with
          | Resolution.Dynamic -> res
          | Resolution.Static ->
            let error = build_sd_call_error (instr.i_loc.base_loc) lv dynamic_exprs fname in
            errors := !errors @ [error];
            Resolution.Static
      ) Resolution.Dynamic lvs

    | Jasmin.Prog.Cif (cond, th, el) ->
      let cond_res = Resolution.of_expr cond in
      let th_res = check_stmt th in
      let el_res = check_stmt el in
      let block_resolution = Resolution.min th_res el_res in
      begin
      if cond_res > block_resolution then
        let error = build_sd_if_error (instr.i_loc.base_loc) in
        errors := !errors @ [error]
      end;
      (* return the max resolution time of the condition and the two branches *)
      block_resolution
    | Jasmin.Prog.Cfor (_, _, stmt) -> check_stmt stmt
    | Jasmin.Prog.Cwhile (_, b1, cond, _, b2) ->
      let cond_res = Resolution.of_expr cond in
      let b1_res = check_stmt b1 in
      let b2_res = check_stmt b2 in
      let block_resolution = Resolution.min b1_res b2_res in
      begin
        if cond_res > block_resolution then
          let error = build_sd_while_error (instr.i_loc.base_loc) in
          errors := !errors @ [error]
      end;
      (* return the max resolution time of the two branches *)
      block_resolution


    (*
    The resolution time of a statement is the static if at least one instruction is static. It means that it must be known at compile time.
      ie : if a static variable is assigned inside a statement, the whole statement is static.
    *)
    and check_stmt (stmt: ('info,'asm) Jasmin.Prog.stmt) : Resolution.t =
      bound_list min Resolution.Dynamic (List.map check_instr stmt)

    in
    let _ = check_stmt func.f_body in
    !errors

(**
Checker entrypoint
*)
let check_prog ((_,funcs): ('info,'asm) Jasmin.Prog.prog) : Error.CompileError.t list =
  List.fold_left (
    fun acc func ->
      let errors = check_function func in
       errors @ acc
  ) [] funcs