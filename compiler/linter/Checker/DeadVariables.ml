open Jasmin
open Utils
open Prog
open Analyser

let create_dv_error err_payload loc =
  let open Error.CompileError in
  {
    location = loc;
    error_strategy = Error.CompileError.Fail;
    code = "DV-E001";
    to_text =
      (
        fun fmt -> Format.fprintf fmt "Variable '%s' is affected but never used" err_payload.v_name
      );
  }


let check_func func =
  let errors = ref [] in

  let check_vars lvs annotation (loc: Location.i_loc) =
    let domain = Annotation.unwrap annotation in
    let lvs_vars = List.fold_left (fun s lv -> Jasmin.Prog.vars_lv s lv) Sv.empty lvs in
    Sv.iter
      (
        fun var ->
          match Sv.find_opt var domain with
          | Some _ -> ()
          | _ ->
              let err = create_dv_error var loc.base_loc in
              errors := err :: !errors
      )
      lvs_vars
  in

  let check_instr { i_desc; i_info;i_loc; _ } =
    match i_desc with
    | Cassgn (x, _, _, _) ->
        check_vars [x] i_info i_loc
    | Copn (xs, _, _, _) | Csyscall (xs, _, _) | Ccall (xs, _, _) ->
        check_vars xs i_info i_loc
    | Cif _ -> ()
    | Cwhile _ -> ()
    | Cfor _ -> ()
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