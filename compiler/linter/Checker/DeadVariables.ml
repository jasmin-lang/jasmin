open Jasmin
open Utils
open Prog

let create_dv_error err_payload loc =
  let open CompileError in
  {
    location = loc;
    error_strategy = CompileError.Fail;
    code = "DV-E001";
    to_text =
      (
        fun fmt -> Format.fprintf fmt "Variable '%s' is affected but never used" err_payload.v_name
      );
  }

let create_dv_error_instr (variables) loc =
  let open CompileError in
  {
    location = loc;
    error_strategy = CompileError.Fail;
    code = "DV-E002";
    to_text =
      (
        fun fmt ->
          Format.fprintf fmt "Instruction contains at least one unused variables. %a " 
          (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",") (Printer.pp_var ~debug:false))variables
        );
  }

let check_func func =
  let dv_errors = ref [] in
  let dv_errors_instr = ref [] in

  let check_instr ({ i_desc; i_info; i_loc; _}:('info,'asm) Prog.instr) =
    let domain = Annotation.unwrap i_info in
    let assigns = Jasmin.Prog.assigns i_desc in
    let dead_variables = Sv.diff assigns domain in
    if (Sv.is_empty (Sv.inter assigns domain)) then (* We check if at least one lvalue is alive. If then, we do not create an error*)
      Sv.iter (fun v ->
        let err_payload= create_dv_error v (i_loc.base_loc) in
        dv_errors := err_payload :: !dv_errors
      ) dead_variables;
    if (not (Sv.is_empty dead_variables)) then
      let err_payload = create_dv_error_instr (Sv.elements dead_variables) (i_loc.base_loc) in
      dv_errors_instr := err_payload :: !dv_errors_instr
  in

  iter_instr check_instr func.f_body ;
  !dv_errors, !dv_errors_instr

let check_prog (_,funcs) =
  List.fold (
    fun (ev,ei) fd ->
      let errors_var, errors_instr = check_func fd in
      (List.rev_append  errors_var ev), (List.rev_append errors_instr ei)
  )
  ([],[])
  funcs
