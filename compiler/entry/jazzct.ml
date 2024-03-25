open Jasmin
open Cmdliner
open CommonCLI
open Utils

let parse_and_check arch call_conv =
  let module A = (val get_arch_module arch call_conv) in
  let check infer ct_list file =
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

    let sigs, errs =
      Ct_checker_forward.ty_prog A.is_ct_sopn ~infer prog ct_list
    in
    Format.printf "/* Security types:\n@[<v>%a@]*/@."
      (pp_list "@ " (Ct_checker_forward.pp_signature prog))
      sigs;
    let on_err (loc, msg) =
      hierror ~loc:(Lone loc) ~kind:"constant type checker" "%t" msg
    in
    Stdlib.Option.iter on_err errs
  in
  fun infer ct_list file ->
    match check infer ct_list file with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let infer =
  let doc = "Infer security contracts" in
  Arg.(value & flag & info [ "infer" ] ~doc)

let slice =
  let doc =
    "Only check the given function (and its dependencies). This argument may \
     be repeated to check many functions. If not given, all functions will be \
     checked."
  in
  Arg.(value & opt_all string [] & info [ "slice"; "only"; "on" ] ~doc)

let file =
  let doc = "The Jasmin source file to verify" in
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
    Cmd.info "jazzct" ~version:Glob_options.version_string ~doc ~man
  in
  Cmd.v info
    Term.(const parse_and_check $ arch $ call_conv $ infer $ slice $ file)
  |> Cmd.eval |> exit
