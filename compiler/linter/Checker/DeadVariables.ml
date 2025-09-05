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
        fun fmt -> Format.fprintf fmt "Variable “%s” is affected but never used" err_payload.v_name
      );
  }

let create_dv_error_instr loc =
  let open CompileError in
  {
    location = loc;
    error_strategy = CompileError.Fail;
    code = "DV-E002";
    to_text =
      (
        fun fmt ->
        Format.fprintf fmt "Instruction only assigns dead variables"
      );
  }

let check_func func =
  let dv_errors = ref [] in

  let check_instr ({ i_desc; i_info; i_loc; _}:('info,'asm) Prog.instr) =
    let domain = Annotation.unwrap i_info in
    let assigns = Jasmin.Prog.assigns i_desc in
    if not (Sv.is_empty assigns) then begin
        if Sv.disjoint assigns domain && not (has_effect i_desc) then
          (* The instruction is dead: warn once *)
          dv_errors := create_dv_error_instr i_loc.base_loc :: !dv_errors
        else
          (* Some assigned variables are dead: warn for each dead variable *)
          Sv.iter (fun v ->
              dv_errors := create_dv_error v i_loc.base_loc :: !dv_errors
            ) (Sv.diff assigns domain)
      end
  in

  iter_instr check_instr func.f_body ;
  !dv_errors

let check_prog (_,funcs) =
  List.fold (
    fun (ev) fd ->
      let errors_var = check_func fd in
      (List.rev_append  errors_var ev)
  )
  ([])
  funcs
