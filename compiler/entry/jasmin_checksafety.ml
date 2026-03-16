open Jasmin
open Utils
open Prog
open Jasmin_checksafety
open CommonCLI
open Cmdliner

(* -------------------------------------------------------------------- *)
let checksafety arch call_conv idirs slice safety_param no_check_alignment
    config file =
  Option.may SafetyConfig.load_config config;
  let () = if no_check_alignment then Glob_options.trust_aligned := true in
  let module P = (val SafetyMain.get_arch_with_analyze arch call_conv) in
  let module Arch = P.A in
  let after_pass = SafetyConfig.sc_comp_pass () in
  let prog, _ =
    parse_and_compile (module Arch) ~wi2i:false after_pass file idirs
  in
  let () =
    if SafetyConfig.sc_print_program () then
      let s1, s2 = Glob_options.print_strings after_pass in
      Format.eprintf "@[<v>At compilation pass: %s@;%s@;@;%a@;@]@." s1 s2
        (Printer.pp_prog ~debug:true Arch.pointer_data Arch.msf_size Arch.asmOp)
        prog
  in
  let () = SafetyConfig.pp_current_config_diff () in
  let fds = prog |> snd |> List.filter (fun fd -> FInfo.is_export fd.f_cc) in
  let fds =
    if slice <> [] then
      fds |> List.filter (fun fd -> List.mem fd.f_name.fn_name slice)
    else fds
  in
  let is_safe =
    List.fold_left
      (fun res f_decl ->
        let () =
          Format.eprintf "@[<v>Analyzing function %s@]@." f_decl.f_name.fn_name
        in

        P.analyze ~safety_param f_decl prog && res)
      true fds
  in
  exit (if is_safe then 0 else 2)

(* -------------------------------------------------------------------- *)
let docdir =
  let doc = "Make the safety checker configuration docs in $(i, DIR)" in
  Arg.(
    value & opt (some dir) None & info ~doc ~docv:"DIR" [ "make-config-doc" ])

let file =
  let doc = "The Jasmin source file to verify." in
  Arg.(value & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let slice =
  let doc =
    "Only check the given function (and its dependencies). This argument may \
     be repeated to check many functions. If not given, all export functions \
     will be checked."
  in
  Arg.(value & opt_all string [] & info [ "slice"; "only"; "on" ] ~doc)

let param =
  let doc =
    " Parameter for automatic safety verification:\n\
    \    format: \"f_1>param_1|f_2>param_2|...\" where each param_i is of the \
     form:\n\
    \    pt_1,...,pt_n;len_1,...,len_k\n\
    \    pt_1,...,pt_n: input pointers of f_i\n\
    \    len_1,...,len_k: input lengths of f_i"
  in
  Arg.(value & opt (some string) None & info [ "param" ] ~doc ~docv:"PARAM")

let config =
  let doc = "Use $(i,JSON) as configuration file" in
  Arg.(
    value & opt (some non_dir_file) None & info [ "config" ] ~docv:"JSON" ~doc)

let no_check_alignment =
  let doc = "Do not report alignment issue as safety violations" in
  Arg.(value & flag & info [ "no-check-alignment" ] ~doc)

let parse docdir arch call_conv idirs slice param no_check_alignment config file
    =
  match (docdir, file) with
  | None, None -> `Error (true, "Nothing to do…")
  | Some _, Some _ -> `Error (true, "Too many arguments")
  | Some dir, None -> `Ok (SafetyConfig.mk_config_doc dir)
  | None, Some file ->
      `Ok
        (checksafety arch call_conv idirs slice param no_check_alignment config
           file)

(* -------------------------------------------------------------------- *)
let () =
  let doc = "Check safety of Jasmin programs" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jasmin-checksafety" ~version:Glob_options.version_string ~doc ~man
  in
  Cmd.v info
    Term.(
      ret
        (const parse $ docdir $ arch $ call_conv $ idirs $ slice $ param
       $ no_check_alignment $ config $ file))
  |> Cmd.eval |> exit
