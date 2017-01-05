open Core.Std
open IL
open IL_Utils
open IL_Lang
open Util

module F  = Format
module AP = Asm_Parse
module P  = ParserUtil
module L  = ParserUtil.Lexing

(* --------------------------------------------------------------------- *)
(* Command implementations *)

let parse_and_process ~parse ~ftype:_ ~process file =
  let s = In_channel.read_all file in
  (* eprintf "Parsing %s as %s\n\n%!" file ftype; *)
  match parse file s with
  | `ParseOk res        -> process s res
  | `ParseError(pinfos) -> P.failloc_c s pinfos

let process_mil trafo print_result out_file file s (modul : 'info modul) =
  let res =
    try ILT.apply_transform_asm trafo modul
    with
      | TypeError(loc,msg) -> P.failloc s [loc,msg]
      | P.ParseError(errs) -> P.failloc s errs
  in
  match res with
  | `Asm_X64 afuns ->
    let asm_string = fsprintf "%a" (pp_list "@\n@\n" Asm_X64.pp_afun) afuns in
    if print_result then (
      F.printf "%s%!" asm_string
    ) else (
      F.printf "Processed file %s@\n%!" file
    );
    if out_file<>"" then (
      Out_channel.write_all out_file ~data:asm_string
    )
  | `IL modul ->
    if print_result
    then F.eprintf "%a@\n%!" (ILPP.pp_modul ?pp_info:None ~pp_types:false) modul
    else F.eprintf "Processed file %s@\n%!" file

let jasminc trafo print_result out_file file =
  match Filename.split_extension file with
  | _, Some "mil" ->
    parse_and_process
      ~parse:ILP.modul
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
      ~process:(fun _s ainstrs ->
        if print_result then
          F.eprintf "%a%!" Asm_X64.pp_instrs ainstrs
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
  +> flag "-p" no_arg ~doc:" print result"
  +> flag "-o" (optional_with_default "" file)
      ~doc:"output_file output to given file"
  +> anon ("filename" %: regular_file)

let command =
  Command.basic
    ~summary:"Compiler from MIL to assembly."
    ~readme:(fun () ->
      String.concat ~sep:"\n"
       [ "The jasmin compiler transforms the given (.mil|.s) file.";
         "";
         "Transformations are given as comma-separated lists of";
         "transformation passes from the following list:";
         "";
         "  expand[p1=i1,...,pk=ik]:";
         "    expand macros with given mapping from parameters to integers";
         "  ssa:";
         "    rename variables to obtain static single assignment form";
         "  register_alloc:";
         "    allocate registers";
         "  asm(X86-64):";
         "    compile to assembly";
         "";
         " Example: 'expand[n=5],ssa,register_alloc,asm(X86-64)'"
       ]
       )
    spec
    (fun trafo print_result out_file filename () ->
       jasminc trafo print_result out_file filename)

let () =
  Command.run ~version:"1.0" ~build_info:"none" command
