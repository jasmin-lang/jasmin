open Jasmin
open Cmdliner
open CommonCLI
open Utils

let open_fmt = function
  | None -> (Format.std_formatter, fun () -> ())
  | Some f ->
      let out = open_out f in
      let fmt = Format.formatter_of_out_channel out in
      (fmt, fun () -> close_out out)

(* The EasyCrypt name of the theory of a file. *)
let theory_name f =
  f |> Filename.basename |> Filename.remove_extension |> String.capitalize_ascii

let extract_to_file prog arch pd msfsz asmOp model amodel global_options
    safety specs fnames array_dir outfile =
  let array_dir =
    if array_dir = None then Option.map Filename.dirname outfile else array_dir
  in
  let specs =
    match (specs, outfile) with
    | None, _ -> None
    | Some s, Some o -> Some (s, theory_name o)
    | Some _, None ->
        hierror ~loc:Lnone ~kind:"extraction error"
          "the specifications require an output file (-o)"
  in
  let fmt, close = open_fmt outfile in
  let sfmt, sclose = open_fmt (Option.map fst specs) in
  try
    BatPervasives.finally
      (fun () ->
        close ();
        if Option.is_some specs then sclose ())
      (fun () ->
        ToEC.extract prog arch pd msfsz asmOp model amodel global_options
          ~safety
          ?specs:(Option.map (fun (_, th) -> (th, sfmt)) specs)
          fnames array_dir fmt)
      ()
  with e ->
    BatPervasives.ignore_exceptions
      (fun () ->
        Option.may Unix.unlink outfile;
        Option.may (fun (s, _) -> Unix.unlink s) specs)
      ();
    raise e

let parse_and_extract arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let extract model amodel global_options safety specs functions array_dir
      output pass file =
    let prog = parse_and_compile (module A) ~wi2i:true pass file idirs in
    let prog =
      if safety then Compile.do_toec_safety (module A) prog
      else Compile.do_toec (module A) prog
    in
    try
      extract_to_file prog arch A.reg_size A.msf_size A.asmOp model amodel
        global_options safety specs functions array_dir output
    with Annot.AnnotationError (loc, code) ->
      hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
  in
  fun model amodel global_options safety specs functions array_dir output pass
      file warn ->
    if not warn then nowarning ();
    match
      extract model amodel global_options safety specs functions array_dir
        output pass file
    with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let model =
  let alts =
    [ ("normal", Normal); ("CT", ConstantTime); ("CTG", ConstantTimeGlobal) ]
  in
  let doc =
    "Extraction model.
    $(b,normal): plain extraction.
    $(b,CT): Functions additionally return timing-observable leakage for
    'cryptographic constant time' (if/while conditions, memory access
    addresses, array indices, for loop bounds).
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

(* The extraction of global variables is configured by the repeatable
   --global-model option, whose value selects either the kind of the EasyCrypt
   declaration (abbrev, op, op=OPTIONS) or how the machine words are printed
   (sign=signed, sign=unsigned). *)
let global_model =
  (* Each occurrence of the option is a “key” or a “key = value”; the spaces
     around the “=” are ignored. *)
  let alts = [ "abbrev"; "op"; "op=OPTIONS"; "sign=signed"; "sign=unsigned" ] in
  let sign =
    Arg.enum [ ("signed", ToEC.GlobSigned); ("unsigned", ToEC.GlobUnsigned) ]
  in
  (* the shell usually removes the quotes of “op="opaque smt_opaque"”, but they
     reach us when written as --global-model='op="opaque smt_opaque"' *)
  let unquote s =
    let n = String.length s in
    if n >= 2 && s.[0] = '"' && s.[n - 1] = '"' then
      String.trim (String.lchop (String.rchop s))
    else s
  in
  let parse s =
    let key, value =
      match String.split s ~by:"=" with
      | key, value -> (String.trim key, Some (String.trim value))
      | exception Not_found -> (String.trim s, None)
    in
    match (key, value) with
    | "abbrev", None -> Ok (`Model ToEC.GlobAbbrev)
    | "op", None -> Ok (`Model (ToEC.GlobOp ""))
    | "op", Some opts -> Ok (`Model (ToEC.GlobOp (unquote opts)))
    | "sign", Some v -> (
        match Arg.conv_parser sign v with
        | Ok s -> Ok (`Sign s)
        | Error (`Msg e) -> Error (`Msg e))
    | _ ->
        Error
          (`Msg
            (Format.sprintf "invalid value “%s”, must be %s" s
               (Arg.doc_alts ~quoted:true alts)))
  in
  let pp fmt = function
    | `Model g -> Format.pp_print_string fmt (ToEC.string_of_gmodel g)
    | `Sign g -> Format.fprintf fmt "sign=%s" (ToEC.string_of_gsign g)
  in
  let doc =
    "How global variables are extracted; this option may be repeated, the last
     value of each kind wins (the spaces around the '=' are optional).
     $(b,abbrev) (the default): as EasyCrypt abbreviations.
     $(b,op): as EasyCrypt operators.
     $(b,op)=$(i,OPTIONS): as EasyCrypt operators declared with the given
     options, e.g. $(b,op=\"opaque smt_opaque\"); the options are passed to
     EasyCrypt as such.
     These defaults can be overridden for each global variable using the
     $(b,#[abbrev]) and $(b,#[op]) annotations.
     $(b,sign=signed) (the default): the machine words are printed as integers
     in [-2^(n-1), 2^(n-1)), e.g. $(b,W64.of_int (-1)).
     $(b,sign=unsigned): they are printed as integers in [0, 2^n), e.g.
     $(b,W64.of_int 18446744073709551615).
     Both denote the same words, but the unsigned form avoids the unary minus,
     which is cheaper to handle in EasyCrypt."
  in
  let global_options =
    List.fold_left
      (fun (global_options : ToEC.global_options) -> function
        | `Sign gsign -> { global_options with gsign }
        | `Model gmodel -> { global_options with gmodel })
      ToEC.default_global_options
  in
  Term.(
    const global_options
    $ Arg.(
        value
        & opt_all (conv (parse, pp)) []
        & info [ "global-model" ] ~docv:"MODEL" ~doc))

let safety =
  let doc =
    "Extract for safety verification: the safety conditions of the program
     become assertions, and the initialisation state of the variables becomes
     explicit (each variable gets a mask). An assertion that does not hold
     raises the exception Assertion_failure: the program is safe when no
     execution raises it. Requires the $(b,barray) array model."
  in
  Arg.(value & flag & info [ "safety" ] ~doc)

let safety_specs =
  let doc =
    "With $(b,--safety), also write to $(docv) the specification of each
     extracted function with a contract, as an operator $(i,f)_spec of the
     values of its arguments: a hoare statement on the procedure, without
     proof, whose precondition is the requires clause and whose postcondition
     is the ensures clause, and which states that Assertion_failure is not
     raised. The file requires the extracted file, which must be given by
     $(b,-o)."
  in
  Arg.(
    value
    & opt (some string) None
    & info [ "safety-specs" ] ~docv:"FILE" ~doc)

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
      $ global_model $ safety $ safety_specs $ functions $ array_dir $ output $ after_pass
      $ file $ warn)
  |> Cmd.eval |> exit
