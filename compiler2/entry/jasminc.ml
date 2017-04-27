(* -------------------------------------------------------------------- *)
module J = Jasmin

open Jasmin.Utils

(* -------------------------------------------------------------------- *)
exception UsageError

(*-------------------------------------------------------------------- *)
let usage ?status () =
  Printf.eprintf "Usage: jasminc [filename]\n%!";
  oiter (fun i -> exit i) status

(* -------------------------------------------------------------------- *)
let main () =
  try
    if Array.length Sys.argv - 1 <> 1 then
      raise UsageError;

    let fname = Sys.argv.(1) in
    let ast   = J.Parseio.parse_program ~name:fname in
    let ast   = BatFile.with_file_in fname ast in
    let _, pprog  = J.Typing.tt_program J.Typing.Env.empty ast in
    Printf.eprintf "parsed & typed\n%!";
    Format.eprintf "%a@." J.Printer.pp_pprog pprog;
    let prog = J.Subst.remove_params pprog in
    Printf.eprintf "params removed \n%!";
    Format.eprintf "%a@." (J.Printer.pp_prog ~debug:true) prog;
    Format.eprintf "EXTRACTED COQ PROGRAM@.";
    Format.eprintf "%a@." J.Coq_printer.pp_prog prog;

    (* Now call the coq compiler *)
    let tbl, cprog = J.Conv.cprog_of_prog prog in
    Printf.eprintf "translated to coq \n%!";

    let fdef_of_cfdef fn cfd = J.Conv.fdef_of_cfdef tbl (fn,cfd) in
    let cfdef_of_fdef fd = snd (J.Conv.cfdef_of_fdef tbl fd) in
    let apply trans fn cfd = 
      let fd = fdef_of_cfdef fn cfd in
      let fd = trans fd in
      cfdef_of_fdef fd in

    let rename_fd = apply J.Subst.clone_func in
    let expand_fd = apply J.Array_expand.arrexp_func in
    let alloc_fd  _fn cfd = cfd (* FIXME *) in
    let stk_alloc_fd _fn _cfd = assert false in
    let print_prog s cp = 
      let p = J.Conv.prog_of_cprog tbl cp in
      Format.eprintf "After %s@." (J.Conv.string_of_string0 s);
      Format.eprintf "%a@." (J.Printer.pp_prog ~debug:true) p;
      cp
    in
    
    let _ = 
      J.Compiler.compile_prog_to_x86 
        rename_fd expand_fd alloc_fd stk_alloc_fd print_prog
        cprog in
    ()

  with
  | UsageError ->
      usage ~status:1 ()

  | J.Syntax.ParseError (loc, None) ->
      Format.eprintf "%s: parse error\n%!"
        (J.Location.tostring loc)

  | J.Syntax.ParseError (loc, Some msg) ->
      Format.eprintf "%s: parse error: %s\n%!"
        (J.Location.tostring loc) msg

  | J.Typing.TyError (loc, code) ->
      Format.eprintf "%s: typing error: %a\n%!"
        (J.Location.tostring loc)
        J.Typing.pp_tyerror code

(* -------------------------------------------------------------------- *)
let () = main ()
