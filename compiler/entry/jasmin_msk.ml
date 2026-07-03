open Jasmin
open Cmdliner
open CommonCLI
open Utils

let parse_and_check arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let check pass file =
    let prog = parse_and_compile (module A) ~wi2i:false pass file idirs in

    try ignore (Masking_checker_forward.ty_prog prog)
    with Masking_checker_forward.MaskingTypeError (loc, pp) ->
      hierror ~loc:(Lone loc) ~kind:"masking" "%a" (fun fmt () -> pp fmt) ()
    | Masking_checker_forward.MaskingTypeErrorI (iloc, pp) ->
      hierror ~loc:(Lmore iloc) ~kind:"masking" "%a" (fun fmt () -> pp fmt) ()
  in

  fun compile file warn ->
    if not warn then (
      nowarning ();
      add_warning Deprecated ());
    let compile =
      if compile < Compiler.Unrolling then
        Compiler.Unrolling
      else compile
    in
    match check compile file with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1


let file =
  let doc = "The Jasmin source file to verify." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let () =
  let doc = "Check Constant-Time security of Jasmin programs" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jasmin-ct" ~version:Glob_options.version_string ~doc ~man
  in
  Cmd.v info
    Term.(
      const parse_and_check $ arch $ call_conv $ idirs $
      after_pass $ file $ warn)
  |> Cmd.eval |> exit
