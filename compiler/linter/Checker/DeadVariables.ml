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


let check_func func =
  let errors = ref [] in

  let check_instr { i_desc; i_info; i_loc; _} =
    let domain = Annotation.unwrap i_info in
    let dead_variables = Sv.diff (Jasmin.Prog.assigns i_desc) domain in
    Sv.iter (fun v ->
      let err_payload= create_dv_error v (i_loc.base_loc) in
      errors := err_payload :: !errors
    ) dead_variables
  in

  iter_instr check_instr func.f_body ;
  !errors

let check_prog (_,funcs) =
  List.fold (
    fun acc fd ->
      let errors = check_func fd in
      List.rev_append errors acc
  )
  []
  funcs
