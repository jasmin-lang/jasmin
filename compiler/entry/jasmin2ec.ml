open Jasmin
open Cmdliner
open CommonCLI
open Utils

let extract_to_file prog pd asmOp model fnames array_dir outfile =
  let array_dir =
    if array_dir = None then Option.map Filename.dirname outfile else array_dir
  in
  let fmt, close =
    match outfile with
    | None -> Format.std_formatter, fun () -> ()
    | Some f ->
        let out = open_out f in
        let fmt = Format.formatter_of_out_channel out in
        fmt, fun () -> close_out out
  in
  begin try
    BatPervasives.finally
      (fun () -> close ())
      (fun () -> ToEC.extract prog pd asmOp model fnames array_dir fmt)
      ()
  with e ->
    BatPervasives.ignore_exceptions
      (fun() -> Option.map Unix.unlink outfile) ();
    raise e
  end

let parse_and_extract arch call_conv =
  let module A = (val get_arch_module arch call_conv) in
  let extract model functions array_dir output file =
    let _env, pprog, _ast =
      try Compile.parse_file A.arch_info file with
      | Annot.AnnotationError (loc, code) ->
          hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
      | Pretyping.TyError (loc, code) ->
          hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror
            code
      | Syntax.ParseError (loc, msg) ->
          hierror ~loc:(Lone loc) ~kind:"parse error" "%s"
            (Option.default "" msg)
    in
    let prog =
      try Compile.preprocess A.reg_size A.asmOp pprog
      with Typing.TyError (loc, code) ->
        hierror ~loc:(Lmore loc) ~kind:"typing error" "%s" code
    in
    extract_to_file prog A.reg_size A.asmOp model functions array_dir output
  in
  fun model functions array_dir output file ->
    match extract model functions array_dir output file with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let model = 
  let alts = [ ("normal", Normal) ; ("CT", ConstantTime) ] in
  let doc =
    Format.asprintf "Extraction model (determines added annotations (e.g. leakage) (%s)."
    (Arg.doc_alts_enum alts)
  in
  Arg.(value & opt (Arg.enum alts) Normal & info [ "m"; "model" ] ~doc)

let functions =
  let doc =
    "Only extract the given function (and its dependencies). This argument may \
     be extract to check many functions. If not given, all functions will be \
     extracted."
  in
  Arg.(value & opt_all string [] & info [ "f"; "function" ] ~doc)

let output =
  let doc = "Output file. If not given, output will be printed on stdout." in
  Arg.(value & opt (some string) None & info [ "o"; "output" ] ~docv:"OUTPUT FILE" ~doc)

let array_dir =
  let doc =
    "Directory for generation of easycrypt array theories. \
     If not given, the theories be in the same directory as the output \
     (they will not be generated if the output is stdout)."
  in
  Arg.(value & opt (some dir) None & info [ "oa"; "output-array" ] ~docv:"OUTPUT DIR" ~doc)

let file =
  let doc = "The Jasmin source file to extract" in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let () =
  let doc = "Extract Jasmin program to easycrypt" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jasmin2ec" ~version:Glob_options.version_string ~doc ~man
  in
  Cmd.v info
    Term.(
      const parse_and_extract $ arch $ call_conv $ model $ functions $ array_dir
      $ output $ file)
  |> Cmd.eval |> exit
