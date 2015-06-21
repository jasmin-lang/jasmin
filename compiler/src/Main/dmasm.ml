open Core.Std
open IL
open Util

module F  = Format
module AP = Asm_Parse

(* --------------------------------------------------------------------- *)
(* Command implementations *)

let parse_and_process ~parse ~ftype ~process file =
  let s = In_channel.read_all file in
  eprintf "Parsing %s as %s\n\n%!" file ftype;
  begin match parse s with
  | `ParseOk pres ->
    process pres
  | `ParseError(pinfo) ->
    let s = ParserUtil.error_string file pinfo in
    eprintf "%s%!" s
  end

let process_compiled_asm print_result out_file file st =
  let asm_code = ILC.to_asm_x64 st |> ILC.wrap_asm_function in
  let asm_string = fsprintf "%a" Asm_X64.pp_instrs asm_code in
  if print_result then (
    F.printf "%s%!" asm_string
  ) else (
    F.printf "Processed file %s@\n%!" file
  );
  if out_file<>"" then (
    Out_channel.write_all out_file ~data:asm_string;
  )

let process_mil trafo print_result out_file file st =
  let (trafo,mlang) = ILC.parse_trafo trafo in
  let st = ILC.apply_transform trafo st in
  match mlang with
  | Some ILC.X64 ->
    process_compiled_asm print_result out_file file st
  | None ->
    if print_result
    then F.eprintf "%a@\n%!" IL_Lang.pp_stmt st
    else F.eprintf "Processed file %s@\n%!" file

let dmasm trafo print_result out_file file =
  match Filename.split_extension file with
  | _, Some "mil" ->
    parse_and_process
      ~parse:ILP.stmt
      ~ftype:"MIL"
      ~process:(process_mil trafo print_result out_file file)
      file
  | _, Some "s" ->
    if trafo<>"" then (
      eprintf "no transformations for '.s' files.\n%!";
      exit 1
    );
    parse_and_process
      ~parse:AP.instrs
      ~ftype:"assembly file (AT&T syntax)"
      ~process:(fun st ->
        if print_result then
          F.eprintf "%a%!" Asm_X64.pp_instrs st
        else
          F.eprintf "File %s parsed successfully.\n\n%!" file)
      file
  | _, (None | Some _) ->
    eprintf "Unsupported file extension, expected 'mil' or 's'.\n\n%!"

(* --------------------------------------------------------------------- *)
(* Command line interface *)

let regular_file =
  Command.Spec.Arg_type.create
    (fun filename ->
       match Sys.is_file filename with
       | `Yes -> filename
       | `No | `Unknown ->
         eprintf "'%s' is not a regular file.\n%!" filename;
         exit 1
    )

let spec =
  let open Command.Spec in
  empty
  +> flag "-t" (optional_with_default "" string)
      ~doc:"transformations perform the given transformations"
  +> flag "-p" no_arg ~doc:"print result"
  +> flag "-o" (optional_with_default "" file)
      ~doc:"output_file output to given file"
  +> anon ("filename" %: regular_file)

let command =
  Command.basic
    ~summary:"Process the given file."
    ~readme:(fun () -> "The dmasm tool transforms the given (.mil|.s) file.")
    spec
    (fun trafo print_result out_file filename () ->
       dmasm trafo print_result out_file filename)

let () =
  Command.run ~version:"1.0" ~build_info:"none" command
