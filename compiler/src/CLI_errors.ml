open Glob_options
open Utils

(* -------------------------------------------------------------------- *)

type cli_error =
  | RedundantInputFile of string * string
  | FileNotFound of string
  | FileIsDirectory of string
  | FilePathNotFound of string
  | DOITPassEarly of string

let pp_cli_error ie =
  match ie with
  | RedundantInputFile (infile, s) ->
      Format.asprintf
        "Input file already set to %s, second input file %s is redundant"
        infile
        s
  | FileNotFound s -> Format.asprintf "File %s not found" s
  | FileIsDirectory s -> Format.asprintf "File %s is a directory" s
  | FilePathNotFound s -> Format.asprintf "Path for file %s doesn't exist" s
  | DOITPassEarly s -> Format.asprintf "DOIT mode enabled, %s checking needs to be done after lowering, use -check%safter option" s s

exception CLIerror of cli_error

(* -------------------------------------------------------------------- *)

let is_directory fname = BatSys.file_exists fname && BatSys.is_directory fname

let check_infile s =
  if not (BatSys.file_exists s) then raise (CLIerror (FileNotFound s));
  if is_directory s then raise (CLIerror (FileIsDirectory s))

let chk_is_not_dir fname =
  if is_directory fname then raise (CLIerror (FileIsDirectory fname))

let chk_path_exists fname =
  if not (is_directory (BatFilename.dirname fname)) then
    raise (CLIerror (FilePathNotFound fname))

let chk_doit_pass doit list pass checker =
  let lowering_index = oget (List.index_of Compiler.LowerInstruction Compiler.compiler_step_list) in
  let pass_index = oget (List.index_of pass Compiler.compiler_step_list) in
  if doit && list != None && pass_index < lowering_index then raise (CLIerror (DOITPassEarly checker))

let check_options () =
  let chk_out_file fref =
    let fname = !fref in
    if fname <> "" then begin
      chk_is_not_dir fname;
      chk_path_exists fname
    end
  in
  
  chk_doit_pass !doit !ct_list !ct_comp_pass "CT";
  chk_doit_pass !doit !sct_list !sct_comp_pass "SCT";

  if !call_conv = Windows
  then warning Experimental Location.i_dummy
      "support for windows calling-convention is experimental";

  if !target_arch = ARM_M4
    then warning Experimental Location.i_dummy
      "support of the ARMv7 architecture is experimental";

  if !latexfile <> ""
  then warning Deprecated Location.i_dummy
         "the [-latex] option has been deprecated since March 2023; use [jazz2tex] instead";
  List.iter chk_out_file [ outfile; latexfile; ecfile ]
