open Jasmin
open Cmdliner
open CommonCLI
open Utils

type printer =
  | NoPrint
  | PrintSelected
  | PrintAll

let parse_and_check arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let check ~doit infer ct_list speculative pass file print =
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
      let pp_signature fmt (fd, sig_) =
        Format.fprintf fmt "@[<v>#[ct = \"%a\"]@ %a@]@ "
          Ct_checker_forward.pp_signature sig_
          (Printer.pp_header ~debug:false)
          fd
      in
      let sigs =
        let open Prog in
        let select_export (fn, _) = FInfo.is_export fn.f_cc in
        let select_slice (fn, _) = List.mem fn.f_name.fn_name ct_list in
        let select_none _ = false in
        let select_all _ = true in
        let select =
          match print with
          | NoPrint ->
            if infer then select_export else select_none
          | PrintSelected ->
            if ct_list = [] then select_export else select_slice
          | PrintAll ->
            select_all
        in
        List.filter select sigs
      in
      Format.printf "@[<v>%a@]@."
        (pp_list "@ " pp_signature)
        sigs;
      let on_err (loc, msg) =
        hierror ~loc:(Lone loc) ~kind:"constant type checker" "%t" msg
      in
      Stdlib.Option.iter on_err errs
  in
  fun infer ct_list speculative compile file doit warn print ->
    if not warn then (
      nowarning ();
      add_warning Deprecated ());
    let compile =
      if doit && compile < Compiler.PropagateInline then
        Compiler.PropagateInline
      else compile
    in
    match check ~doit infer ct_list speculative compile file print with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let infer =
  let doc = "Infer security contracts. This can be used for development purpose but should not be used for production." in
  Arg.(value & flag & info [ "infer" ] ~doc)

let speculative =
  let doc = "Check for Speculative constant time" in
  Arg.(value & flag & info [ "speculative"; "sct" ] ~doc)

let slice =
  let doc =
    "Only check the given function (and its dependencies). This argument may \
     be repeated to check many functions. If not given, all functions will be \
     checked."
  in
  Arg.(value & opt_all string [] & info [ "slice"; "only"; "on" ] ~doc)

let file =
  let doc = "The Jasmin source file to verify." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let doit =
  let doc = "Allow only DOIT instructions on secrets." in
  Arg.(value & flag & info [ "doit" ] ~doc)

let print =
  let noeffect = "The option has no effect on the SCT checker." in
  let info_select =
    let doc = "Print security type of functions specified by the slice option. If no slice is provided print only the type of exported functions. " ^ noeffect in
    PrintSelected, Arg.info ["print"] ~doc in
  let info_all =
    let doc = "Print security type of all functions. " ^ noeffect in
    PrintAll, Arg.info ["print-all"] ~doc in
  Arg.(value & vflag NoPrint [info_select; info_all])

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
      const parse_and_check $ arch $ call_conv $ idirs $ infer $ slice
      $ speculative $ after_pass $ file $ doit $ warn $ print)
  |> Cmd.eval |> exit
