open Jasmin
open Cmdliner
open CommonCLI
open Utils

let parse_and_check arch call_conv idirs =
  let module A = (val get_arch_module arch call_conv) in
  let check ~doit infer ct_list speculative pass file =
    let prog = parse_and_compile (module A) ~wi2i:false pass file idirs in

    if speculative then
      let prog =
        (* Ensure there are no spill/unspill operations left *)
        if pass < Compiler.LowerSpill then
          match Compile.do_spill_unspill A.asmOp prog with
          | Ok p -> p
          | Error err -> raise (HiError err)
        else prog
      in
      match Sct_checker_forward.ty_prog (A.is_ct_sopn ~doit) prog ct_list with
      | exception Annot.AnnotationError (loc, code) ->
          hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
      | sigs ->
          Format.printf "/* Security types:\n@[<v>%a@]*/@."
            (pp_list "@ " Sct_checker_forward.pp_funty)
            sigs
    else
      let sigs, errs =
        Ct_checker_forward.ty_prog (A.is_ct_sopn ~doit) ~infer prog ct_list
      in
      Format.printf "/* Security types:\n@[<v>%a@]*/@."
        (pp_list "@ " (Ct_checker_forward.pp_signature prog))
        sigs;
      let on_err (loc, msg) =
        hierror ~loc:(Lone loc) ~kind:"constant type checker" "%t" msg
      in
      Stdlib.Option.iter on_err errs
  in
  fun infer ct_list speculative compile file doit warn ->
    if not warn then nowarning ();
    let compile =
      if doit && compile < Compiler.PropagateInline then
        Compiler.PropagateInline
      else compile
    in
    match check ~doit infer ct_list speculative compile file with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let infer =
  let doc = "Infer security contracts" in
  Arg.(value & flag & info [ "infer" ] ~doc)

let speculative =
  let doc = "Check for S-CT" in
  Arg.(value & flag & info [ "speculative"; "sct" ] ~doc)

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

let doit =
  let doc = "Allow only DOIT instructions on secrets" in
  Arg.(value & flag & info [ "doit" ] ~doc)

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
      const parse_and_check $ arch $ call_conv $ idirs $ infer $ slice $ speculative
      $ after_pass $ file $ doit $ warn)
  |> Cmd.eval |> exit
