open Jasmin
open Cmdliner
open CommonCLI
open Utils

let parse_and_check arch call_conv =
  let module A = (val get_arch_module arch call_conv) in
  let check infer ct_list speculative pass file =
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

    let prog =
      if pass <= Compiler.ParamsExpansion then prog
      else
        let module E = struct
          exception Found
        end in
        let res = ref prog in
        match
          Compile.compile
            (module A)
            (fun ~debug:_ step prog ->
              if step = pass then (
                res := prog;
                raise E.Found))
            prog (Conv.cuprog_of_prog prog)
        with
        | exception E.Found -> !res
        | _ -> assert false
    in

    if speculative then
      match Sct_checker_forward.ty_prog A.is_ct_sopn prog ct_list with
      | exception Annot.AnnotationError (loc, code) ->
          hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
      | sigs ->
          Format.printf "/* Security types:\n@[<v>%a@]*/@."
            (pp_list "@ " Sct_checker_forward.pp_funty)
            sigs
    else
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
  fun infer ct_list speculative compile file ->
    match check infer ct_list speculative compile file with
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

let compile =
  let alts =
    List.map
      (fun s -> (fst (Glob_options.print_strings s), s))
      Compiler.(List.filter (( > ) StackAllocation) compiler_step_list)
  in
  let doc =
    Format.asprintf "Check for security after the given compilation pass (%s)."
      (Arg.doc_alts_enum alts)
  in

  let passes = Arg.enum alts in
  Arg.(value & opt passes Typing & info [ "compile"; "after" ] ~doc)

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
  let info = Cmd.info "jazzct" ~version:Glob_options.version_string ~doc ~man in
  Cmd.v info
    Term.(
      const parse_and_check $ arch $ call_conv $ infer $ slice $ speculative
      $ compile $ file)
  |> Cmd.eval |> exit
