open Jasmin
open Utils
open Prog
open Types
open Analyser.Annotation

let create_vi_error err_payload loc =
  let open Error.CompileError in
  {
    location = loc;
    error_strategy = Error.Recover.Fail;
    code = "VI-E001";
    to_text =
      (fun fmt ->
        Format.fprintf fmt "Variable %s (declared at : %s) not initialized"
          err_payload.v_name
          (Location.tostring err_payload.v_dloc));
  }

type check_mode = Strict | NotStrict

let check_func mode fd =
  let errors = ref [] in
  let check_var ~loc m x =
    let iset = Mv.find x (unwrap m) in
    if
      match mode with
      | Strict -> Iloc.SIloc.mem Default iset
      | NotStrict -> Iloc.SIloc.equal iset (Iloc.SIloc.singleton Default)
    then errors := create_vi_error x loc :: !errors
  in
  let check_var_i m x = check_var ~loc:(L.loc x) m (L.unloc x) in
  let check_ggvar m x = if x.gs = E.Slocal then check_var_i m x.gv in
  let rec check_e m = function
    | Pconst _ | Pbool _ | Parr_init _ -> ()
    | Pvar x -> check_ggvar m x
    | Pget (_, _, _, x, e) | Psub (_, _, _, x, e) ->
        check_ggvar m x;
        check_e m e
    | Pload (_, _, e) | Papp1 (_, e) -> check_e m e
    | Papp2 (_, e1, e2) -> check_es m [ e1; e2 ]
    | PappN (_, es) -> check_es m es
    | Pif (_, e1, e2, e3) -> check_es m [ e1; e2; e3 ]
  and check_es m = List.iter (check_e m) in
  let check_lv m = function
    | Lnone _ | Lvar _ -> ()
    | Lmem (_, _, _, e) | Laset (_, _, _, _, e) | Lasub (_, _, _, _, e) ->
        check_e m e
  in
  let check_lvs m = List.iter (check_lv m) in
  let check_instr { i_desc; i_info; _ } =
    match i_desc with
    | Cassgn (x, _, _, e) ->
        check_lv i_info x;
        check_e i_info e
    | Copn (xs, _, _, es) | Csyscall (xs, _, es) | Ccall (xs, _, es) ->
        check_lvs i_info xs;
        check_es i_info es
    | Cif (e, _, _) -> check_e i_info e
    | Cfor (_, (_, e1, e2), _) -> check_es i_info [ e1; e2 ]
    | Cwhile (_, _, e, (_, i), _) -> check_e i e
  in
  let check_body stmt = iter_instr check_instr stmt in
  check_body fd.f_body;
  List.iter (check_var_i fd.f_info) fd.f_ret;
  !errors

let check_prog ?(mode = NotStrict) (_, fds) =
  List.concat_map (check_func mode) fds
