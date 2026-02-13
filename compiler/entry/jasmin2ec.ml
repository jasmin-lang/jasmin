open Jasmin
open Cmdliner
open CommonCLI
open Utils

let get_outfile_name outfile =
  match outfile with
  | None -> ""
  | Some f -> 
        let basename = Filename.basename f in
        let basename' =
          try Filename.chop_extension basename with Invalid_argument _ -> basename in
        String.capitalize_ascii basename'

let format_to_file outfile action =
  let fmt, close =
    match outfile with
    | None ->
        Format.std_formatter, (fun () -> ())
    | Some f ->
        let out = open_out f in
        let fmt = Format.formatter_of_out_channel out in
        fmt, (fun () -> close_out out)
  in
  try
    BatPervasives.finally
      (fun () -> close ())
      (fun () -> action fmt)
      ()
  with e ->
    BatPervasives.ignore_exceptions
      (fun () -> Option.map Unix.unlink outfile)
      ();
    raise e

let extract_to_file prog arch pd msfsz asmOp model amodel fnames array_dir outfile prooffile =
  let array_dir =
    if array_dir = None then Option.map Filename.dirname outfile else array_dir
  in
  let extract () =
    format_to_file outfile (fun fmt ->
      ToEC.extract prog arch pd msfsz asmOp model amodel fnames array_dir fmt) in
  let extract_proof () =
    format_to_file prooffile (fun fmt ->
      ToEC.generate_safety_lemmas (get_outfile_name outfile) prog arch pd msfsz asmOp model amodel fnames array_dir fmt) in
  match model, outfile, prooffile with
  | SafetyAnnotations, None, Some _ -> extract_proof ()
  | SafetyAnnotations, Some _, None -> extract ()
  | SafetyAnnotations, _, _         -> extract (); extract_proof ()
  | _ -> extract ()

let parse_and_extract arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let extract model amodel functions array_dir output output_proof pass file =
    let safety =
      match model with
       | SafetyAnnotations -> true
       | _ -> false
    in
    let prog = parse_and_compile (module A) ~wi2i:true ~safety:safety pass file idirs in
    extract_to_file prog arch A.reg_size  A.msf_size A.asmOp model amodel functions
      array_dir output output_proof
  in
  fun model amodel functions array_dir output output_proof pass file warn ->
    if not warn then nowarning ();
    match extract model amodel functions array_dir output output_proof pass file with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let model =
  let alts =
    [ ("normal", Normal); ("CT", ConstantTime); ("CTG", ConstantTimeGlobal); ("safety", SafetyAnnotations)]
  in
  (* TODO : fix the documentation *)
  let doc =
    "Extraction model.
    $(b,normal): plain extraction.
    $(b,CT): Functions additionally return timing-observable leakage for
    'cryptographic constant time' (if/while conditions, memory access
    addresses, array indices, for loop bounds).
    $(b,safety): extract for safety verification.
    (Deprecated) $(b,CTG): Cryptographic constant time leakage is added to a
    global variable."
  in
  Arg.(value & opt (Arg.enum alts) Normal & info [ "m"; "model" ] ~doc)

let array_model =
  let alts =
    [ ("old", ToEC.ArrayOld); ("warray", ToEC.WArray); ("barray", ToEC.BArray) ]
  in

  let doc =
    "Array model.
     $(b,warray): use polymorphic arrays and warrays (functions predefined in eclib).
     $(b,barray): use byte arrays (functions predefined in eclib).
     (Deprecated) $(b,old): old representation for array operations (anonymous functions instead of eclib functions)."
  in
  Arg.(value & opt (Arg.enum alts) ToEC.BArray & info [ "array-model" ] ~doc)

let functions =
  let doc =
    "Only extract the given function (and its dependencies). This argument may \
     be extract to check many functions. If not given, all functions will be \
     extracted."
  in
  Arg.(value & opt_all string [] & info [ "f"; "function" ] ~doc)

let output =
  let doc = "Output file. If not given, output will be printed on stdout." in
  Arg.(
    value
    & opt (some string) None
    & info [ "o"; "output" ] ~docv:"OUTPUT FILE" ~doc)

let output_proof =
 let doc = "Output proof file. If not given, output will be printed on stdout." in
  Arg.(
    value
    & opt (some string) None
    & info [ "output-proof" ] ~docv:"OUTPUT PROOF FILE" ~doc)

let array_dir =
  let doc =
    "Directory for generation of easycrypt array theories. \
     If not given, the theories be in the same directory as the output \
     (they will not be generated if the output is stdout)."
  in
  Arg.(
    value
    & opt (some dir) None
    & info [ "oa"; "output-array" ] ~docv:"OUTPUT DIR" ~doc)

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
      const parse_and_extract $ arch $ call_conv $ idirs $ model $ array_model
      $ functions $ array_dir $ output $ output_proof $ after_pass $ file $ warn)
  |> Cmd.eval |> exit
