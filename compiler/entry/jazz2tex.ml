module J = Jasmin

type arch = Amd64 | CortexM

let parse_and_print arch call_conv =
  let module A =
    J.Arch_full.Arch_from_Core_arch
      ((val match arch with
            | Amd64 ->
                J.CoreArchFactory.core_arch_x86 ~use_lea:false ~use_set0:false
                  call_conv
            | CortexM -> (module J.CoreArchFactory.Core_arch_ARM))) in
  fun output file ->
    let _, _, ast = J.Compile.parse_file A.reg_size A.asmOp_sopn file in
    let out, close =
      match output with
      | None -> (stdout, ignore)
      | Some latexfile -> (open_out latexfile, close_out)
    in
    let fmt = Format.formatter_of_out_channel out in
    Format.fprintf fmt "%a@." J.Latex_printer.pp_prog ast;
    close out

open Cmdliner

let file =
  let doc = "The Jasmin source file to pretty-print" in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let output =
  let doc =
    "The file in which the result is written (instead of the standard output)"
  in
  Arg.(value & opt (some string) None & info [ "o"; "output" ] ~docv:"TEX" ~doc)

let arch =
  let alts = [ ("x86-64", Amd64); ("arm-m4", CortexM) ] in
  let doc =
    Format.asprintf "The target architecture (%s)" (Arg.doc_alts_enum alts)
  in
  let arch = Arg.enum alts in
  Arg.(value & opt arch Amd64 & info [ "arch" ] ~doc)

let call_conv =
  let alts =
    [ ("linux", J.Glob_options.Linux); ("windows", J.Glob_options.Windows) ]
  in
  let doc = Format.asprintf "Undocumented (%s)" (Arg.doc_alts_enum alts) in
  let call_conv = Arg.enum alts in
  Arg.(
    value
    & opt call_conv J.Glob_options.Linux
    & info [ "call-conv"; "cc" ] ~docv:"OS" ~doc)

let () =
  let doc = "Pretty-print Jasmin source programs into LATEX" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jazz2tex" ~version:J.Glob_options.version_string ~doc ~man
  in
  Cmd.v info Term.(const parse_and_print $ arch $ call_conv $ output $ file)
  |> Cmd.eval |> exit
