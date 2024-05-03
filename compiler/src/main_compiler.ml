open Jasmin
open Jasmin_checksafety
open Utils
open Prog
open Glob_options
open CLI_errors

(* -------------------------------------------------------------------- *)
exception UsageError

let parse () =
  let error () = raise UsageError in
  let infiles = ref [] in
  let set_in s = infiles := s :: !infiles in
  (* Set default option values *)
  if Sys.win32 then set_cc "windows";
  (* Parse command-line arguments *)
  Arg.parse (Arg.align options) set_in usage_msg;
  let c =
    match !color with
    | Auto -> Unix.isatty (Unix.descr_of_out_channel stderr)
    | Always -> true
    | Never -> false
  in
  if c then enable_colors ();
  match !infiles with
  | [] ->
    if !help_intrinsics || !safety_makeconfigdoc <> None || !help_version
    then ""
    else error()
  | [ infile ] ->
    check_options ();
    check_infile infile;
    infile
  | infile :: s :: _ -> raise CLI_errors.(CLIerror (RedundantInputFile (infile, s)))

(* -------------------------------------------------------------------- *)
let check_safety_p pd asmOp analyze s (p : (_, 'asm) Prog.prog) source_p =
  let () = if SafetyConfig.sc_print_program () then
      let s1,s2 = Glob_options.print_strings s in
      Format.eprintf "@[<v>At compilation pass: %s@;%s@;@;\
                      %a@;@]@."
        s1 s2
        (Printer.pp_prog ~debug:true pd asmOp) p
  in

  let () = SafetyConfig.pp_current_config_diff () in

  let () =
    List.iter (fun f_decl ->
        if FInfo.is_export f_decl.f_cc then
          let () = Format.eprintf "@[<v>Analyzing function %s@]@."
              f_decl.f_name.fn_name in

          let source_f_decl = List.find (fun source_f_decl ->
              f_decl.f_name.fn_name = source_f_decl.f_name.fn_name
            ) (snd source_p) in
          analyze source_f_decl f_decl p)
      (List.rev (snd p)) in
  ()

(* -------------------------------------------------------------------- *)
module type ArchCoreWithAnalyze = sig
  module C : Arch_full.Core_arch
  val analyze :
    Wsize.wsize ->
    (C.reg, C.regx, C.xreg, C.rflag, C.cond, C.asm_op, C.extra_op) Arch_extra.extended_op Sopn.asmOp ->
    (unit, (C.reg, C.regx, C.xreg, C.rflag, C.cond, C.asm_op, C.extra_op) Arch_extra.extended_op) func ->
    (unit, (C.reg, C.regx, C.xreg, C.rflag, C.cond, C.asm_op, C.extra_op) Arch_extra.extended_op) func ->
    (unit, (C.reg, C.regx, C.xreg, C.rflag, C.cond, C.asm_op, C.extra_op) Arch_extra.extended_op) prog -> unit
end


let main () =

  try
    let infile = parse() in

    let (module P : ArchCoreWithAnalyze) =
      match !target_arch with
      | X86_64 ->
         (module struct
            module C = (val CoreArchFactory.core_arch_x86 ~use_lea:!lea ~use_set0:!set0 !call_conv)
            let analyze = X86_safety.analyze
          end)
      | ARM_M4 ->
         (module struct
            module C = CoreArchFactory.Core_arch_ARM
            let analyze _ _ _ _ _ = failwith "TODO_ARM: analyze"
          end)
    in
    let module Arch = Arch_full.Arch_from_Core_arch (P.C) in

    if !safety_makeconfigdoc <> None
    then (
      let dir = oget !safety_makeconfigdoc in
      SafetyConfig.mk_config_doc dir;
      exit 0);

    if !help_intrinsics
    then (Help.show_intrinsics Arch.asmOp_sopn (); exit 0);

    if !help_version
    then (Format.printf "%s@." version_string; exit 0);

    let () = if !check_safety then
        match !safety_config with
        | Some conf -> SafetyConfig.load_config conf
        | None -> () in

    let env, pprog, ast =
      try Compile.parse_file Arch.arch_info infile
      with
      | Annot.AnnotationError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
      | Pretyping.TyError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror code
      | Syntax.ParseError (loc, msg) ->
          let msg =
            match msg with
            | None -> "unexpected token" (* default message *)
            | Some msg -> msg
          in
          hierror ~loc:(Lone loc) ~kind:"parse error" "%s" msg
    in

    if !print_dependencies then begin
      Format.printf "%a" 
        (pp_list " " (fun fmt p -> Format.fprintf fmt "%s" (BatPathGen.OfString.to_string p)))
        (List.tl (List.rev (Pretyping.Env.dependencies env)));
      exit 0
    end;
 
    if !latexfile <> "" then begin
      let out = open_out !latexfile in
      let fmt = Format.formatter_of_out_channel out in
      Format.fprintf fmt "%a@." Latex_printer.pp_prog ast;
      close_out out;
      if !debug then Format.eprintf "Pretty printed to LATEX@."
    end;
  
    eprint Compiler.Typing (Printer.pp_pprog Arch.reg_size Arch.asmOp) pprog;

    let prog =
      try Compile.preprocess Arch.reg_size Arch.asmOp pprog
      with Typing.TyError(loc, code) ->
        hierror ~loc:(Lmore loc) ~kind:"typing error" "%s" code
    in

    let prog =
      if !slice <> []
      then Slicing.slice !slice prog
      else prog
    in

    (* The source program, before any compilation pass. *)
    let source_prog = prog in

    (* This function is called after each compilation pass.
        - Check program safety (and exit) if the time has come
        - Pretty-print the program
        - Add your own checker here!
    *)
    let visit_prog_after_pass ~debug s p =
      if s = SafetyConfig.sc_comp_pass () && !check_safety then
        check_safety_p
          Arch.reg_size
          Arch.asmOp
          (P.analyze Arch.pointer_data Arch.asmOp)
          s
          p
          source_prog
        |> fun () -> exit 0
      else
      (
        if s == Unrolling then CheckAnnot.check_no_for_loop p;
        if s == Unrolling then CheckAnnot.check_no_inline_instr p;
        eprint s (Printer.pp_prog ~debug Arch.reg_size Arch.asmOp) p
      ) in

    visit_prog_after_pass ~debug:true Compiler.ParamsExpansion prog;

    if !ec_list <> [] || !ecfile <> "" then begin
      let fmt, close =
        if !ecfile = "" then Format.std_formatter, fun () -> ()
        else
          let out = open_out !ecfile in
          let fmt = Format.formatter_of_out_channel out in
          fmt, fun () -> close_out out in
      let fnames =
        match !ec_list with
        | [] -> List.map (fun { f_name ; _ } -> f_name.fn_name) (snd prog)
        | fnames -> fnames in
      begin try
        BatPervasives.finally
          (fun () -> close ())
          (fun () -> ToEC.extract Arch.reg_size Arch.asmOp fmt !model prog fnames)
          ()
      with e ->
        BatPervasives.ignore_exceptions
          (fun () -> if !ecfile <> "" then Unix.unlink !ecfile) ();
        raise e end;
      exit 0
    end;

    (* Now call the coq compiler *)
    let cprog = Conv.cuprog_of_prog prog in

    if !debug then Printf.eprintf "translated to coq \n%!";

    let to_exec = Pretyping.Env.Exec.get env in
    if to_exec <> [] then begin
        let exec { L.pl_loc = loc ; L.pl_desc = (f, m) } =
          let ii = L.i_loc0 loc, [] in
          try
            let pp_range fmt (ptr, sz) =
              Format.fprintf fmt "%a:%a" Z.pp_print ptr Z.pp_print sz in
            Format.printf "/* Evaluation of %s (@[<h>%a@]):@." f.fn_name
              (pp_list ",@ " pp_range) m;
            let _m, vs =
              (* TODO: allow to configure the initial stack pointer *)
              (match
                 Evaluator.initial_memory Arch.reg_size (Z.of_string "1024") m
               with
               | Utils0.Ok m -> m
               | Utils0.Error err -> raise (Evaluator.Eval_error (ii, err)))
              |> Evaluator.run
                   (module Arch)
                   (Expr.to_uprog Arch.asmOp cprog)
                   ii f []
            in

            Format.printf "@[<v>%a@]@."
              (pp_list "@ " Evaluator.pp_val) vs;
            Format.printf "*/@."
          with Evaluator.Eval_error (ii,err) ->
            let i_loc, _ = ii in
            hierror ~loc:(Lmore i_loc) ~kind:"evaluation error" "%a" Evaluator.pp_error err
        in
        List.iter exec to_exec
      end;

    begin match Compile.compile (module Arch) visit_prog_after_pass prog cprog with
    | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:!debug) e in
      raise (HiError e)
    | Utils0.Ok asm ->
      if !outfile <> "" then begin
        BatFile.with_file_out !outfile (fun out ->
          let fmt = BatFormat.formatter_of_out_channel out in
          Format.fprintf fmt "%a%!" Arch.pp_asm asm);
          if !debug then Format.eprintf "assembly listing written@."
      end else if List.mem Compiler.Assembly !print_list then
          Format.printf "%a%!" Arch.pp_asm asm
    end
  with
  | Utils.HiError e ->
    Format.eprintf "%a@." pp_hierror e;
    exit 1

  | UsageError ->
    Arg.usage (Arg.align options) usage_msg;
    exit 1

  | CLIerror e ->
    Format.eprintf "%a: %s.\n"
      (pp_print_bold_red Format.pp_print_string) "Error"
      (pp_cli_error e);
    exit 1
