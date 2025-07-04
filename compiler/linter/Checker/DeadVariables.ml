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


let check_func func (known_implicits : (string * string) list) =
  let errors = ref [] in

  let check_instr ({ i_desc; i_info; i_loc; _}:('info,'asm) Prog.instr) =
    let domain = Annotation.unwrap i_info in
    let dead_variables = Sv.diff (Jasmin.Prog.assigns i_desc) domain in
    if (Sv.is_empty (Sv.diff (Jasmin.Prog.assigns i_desc) dead_variables)) then (* We check if at least one lvalue is alive. If then, we do not create an error*)
      Sv.iter (fun v ->
        if not (List.exists (fun (_,var) ->  var = v.v_name) known_implicits) then
        (* We do not create an error for parameters, since they are not dead variables *)
          let err_payload= create_dv_error v (i_loc.base_loc) in
          errors := err_payload :: !errors
      ) dead_variables
  in

  iter_instr check_instr func.f_body ;
  !errors

let check_prog (_,funcs) (known_implicits : (string * string) list) =
  List.fold (
    fun acc fd ->
      let errors = check_func fd known_implicits in
      List.rev_append errors acc
  )
  []
  funcs
