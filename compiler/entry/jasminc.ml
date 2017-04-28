(* -------------------------------------------------------------------- *)
module J = Jasmin

(* -------------------------------------------------------------------- *)
exception UsageError

(*--------------------------------------------------------------------- *)
let infile = ref ""
let outfile = ref ""
let typeonly = ref false
let debug = ref false
let coqfile = ref ""
let coqonly = ref false

let set_coqonly s =
  coqfile := s;
  coqonly := true

let options = [
    "-o"       , Arg.Set_string outfile, "[filename]: name of the output file";
    "-typeonly", Arg.Set typeonly      , ": stop after typechecking";
    "-debug"   , Arg.Set debug         , ": print debug information";
    "-coq"     , Arg.Set_string coqfile, "[filename]: generate the corresponding coq file";
    "-coqonly" , Arg.String set_coqonly, "[filename]: generate the corresponding coq file, and exit"
  ]

let usage_msg = "Usage : jasminc [option] filename"

let parse () =
  let error () = raise UsageError in
  let set_in s =
    if !infile <> "" then error();
    infile := s  in
  Arg.parse options set_in usage_msg;
  if !infile = "" then error()

(* -------------------------------------------------------------------- *)
let main () =
  try

    parse();

    let fname = !infile in
    let ast   = J.Parseio.parse_program ~name:fname in
    let ast   = BatFile.with_file_in fname ast in
    let _, pprog  = J.Typing.tt_program J.Typing.Env.empty ast in
    if !debug then begin
      Printf.eprintf "parsed & typed\n%!";
      Format.eprintf "%a@." J.Printer.pp_pprog pprog
    end;
    if !typeonly then exit 0;

    let prog = J.Subst.remove_params pprog in
    if !debug then begin
      Printf.eprintf "params removed \n%!";
      Format.eprintf "%a@." (J.Printer.pp_prog ~debug:true) prog
    end;

    (* Generate the coq program if needed *)
    if !coqfile <> "" then begin
      let out = open_out !coqfile in
      let fmt = Format.formatter_of_out_channel out in
      Format.fprintf fmt "%a@." J.Coq_printer.pp_prog prog;
      close_out out;
      if !debug then Format.eprintf "coq program extracted@."
    end;

    if !coqonly then exit 0;

    (* Now call the coq compiler *)
    let tbl, cprog = J.Conv.cprog_of_prog prog in
    if !debug then Printf.eprintf "translated to coq \n%!";

    let fdef_of_cfdef fn cfd = J.Conv.fdef_of_cfdef tbl (fn,cfd) in
    let cfdef_of_fdef fd = snd (J.Conv.cfdef_of_fdef tbl fd) in
    let apply trans fn cfd =
      let fd = fdef_of_cfdef fn cfd in
      let fd = trans fd in
      cfdef_of_fdef fd in

    let rename_fd = apply J.Subst.clone_func in
    let expand_fd = apply J.Array_expand.arrexp_func in
    let alloc_fd  = apply J.Regalloc.regalloc in
    let stk_alloc_fd _fn _cfd = assert false in
    let print_prog s cp =
      if !debug then begin
        let p = J.Conv.prog_of_cprog tbl cp in
        Format.eprintf "After %s@." (J.Conv.string_of_string0 s);
        Format.eprintf "%a@." (J.Printer.pp_prog ~debug:true) p
      end;
      cp
    in

    let _ =
      J.Compiler.compile_prog_to_x86
        rename_fd expand_fd alloc_fd stk_alloc_fd print_prog
        cprog in
    ()

  with
  | UsageError ->
     Arg.usage options usage_msg;
     exit 1;

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
