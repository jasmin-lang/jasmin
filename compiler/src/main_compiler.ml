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
  if Arch.os = Some `Windows then set_cc "windows";
  (* Parse command-line arguments *)
  Arg.parse options set_in usage_msg;
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
let check_safety_p asmOp analyze s (p : (_, 'asm) Prog.prog) source_p =
  let () = if SafetyConfig.sc_print_program () then
      let s1,s2 = Glob_options.print_strings s in
      Format.eprintf "@[<v>At compilation pass: %s@;%s@;@;\
                      %a@;@]@."
        s1 s2
        (Printer.pp_prog ~debug:true asmOp) p
  in

  let () = SafetyConfig.pp_current_config_diff () in

  let () =
    List.iter (fun f_decl ->
        if f_decl.f_cc = Export then
          let () = Format.eprintf "@[<v>Analyzing function %s@]@."
              f_decl.f_name.fn_name in

          let source_f_decl = List.find (fun source_f_decl ->
              f_decl.f_name.fn_name = source_f_decl.f_name.fn_name
            ) (snd source_p) in
          analyze source_f_decl f_decl p)
      (List.rev (snd p)) in
  ()

(* -------------------------------------------------------------------- *)
let main () =

  try
    let infile = parse() in

    let (module Ocaml_params : Arch_full.Core_arch) =
      match !target_arch with
      | X86_64 -> CoreArchFactory.core_arch_x86 ~use_lea:!lea ~use_set0:!set0 !call_conv
      | ARM_M4 -> (module CoreArchFactory.Core_arch_ARM)
    in
    let module Arch = Arch_full.Arch_from_Core_arch (Ocaml_params) in
    let ep =
      Sem_params_of_arch_extra.ep_of_asm_e Arch.asm_e Syscall_ocaml.sc_sem
    in
    let spp = Sem_params_of_arch_extra.spp_of_asm_e Arch.asm_e in
    let sip =
      Sem_params_of_arch_extra.sip_of_asm_e Arch.asm_e Syscall_ocaml.sc_sem
    in

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
      try Compile.parse_file Arch.reg_size Arch.asmOp_sopn infile
      with
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
  
    eprint Compiler.Typing (Printer.pp_pprog Arch.asmOp) pprog;

    let prog =
      try Compile.preprocess Arch.reg_size Arch.asmOp pprog
      with Typing.TyError(loc, code) ->
        hierror ~loc:(Lmore loc) ~kind:"typing error" "%s" code
    in

    (* The source program, before any compilation pass. *)
    let source_prog = prog in

    let do_compile = ref true in
    let donotcompile () = do_compile := false in

    (* This function is called after each compilation pass.
        - Check program safety (and exit) if the time has come
        - Pretty-print the program
        - Add your own checker here!
    *)
    let visit_prog_after_pass ~debug s p =
      if s = SafetyConfig.sc_comp_pass () && !check_safety then
        check_safety_p Arch.asmOp Arch.analyze s p source_prog
        |> donotcompile
      else (
        if s == Unrolling then CheckAnnot.check_no_for_loop p;
        if s == Unrolling then CheckAnnot.check_no_inline_instr p;
        eprint s (Printer.pp_prog ~debug Arch.asmOp) p
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
      donotcompile()
    end;

    if !ct_list <> None then begin
        let sigs, status = Ct_checker_forward.ty_prog ~infer:!infer source_prog (oget !ct_list) in
           Format.printf "/* Security types:\n@[<v>%a@]*/@."
              (pp_list "@ " (Ct_checker_forward.pp_signature source_prog)) sigs;
           Stdlib.Option.iter (fun (loc, code) ->
               hierror ~loc:(Lone loc) ~kind:"constant type checker" "%a" Pretyping.pp_tyerror code)
             status;
        donotcompile()
    end;

    if !do_compile then begin
  
    (* Now call the coq compiler *)
    let tbl, cprog =
      let all_vars = Arch.rip :: Arch.all_registers in
       Conv.cuprog_of_prog all_vars prog in

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
              (** TODO: allow to configure the initial stack pointer *)

              let ptr_of_z z = Word0.wrepr Arch.reg_size (Conv.cz_of_z z) in
              let live =
                List.map
                  (fun (ptr, sz) -> ptr_of_z ptr, Conv.cz_of_z sz)
                  m
              in
              let m_init =
                (Low_memory.Memory.coq_M Arch.reg_size).init
                  live
                  (ptr_of_z (Z.of_string "1024"))
              in
              (match m_init with
                 | Utils0.Ok m -> m
                 | Utils0.Error err -> raise (Evaluator.Eval_error (ii, err)))
              |>
              Evaluator.exec
                ep
                spp
                sip
                (Syscall_ocaml.initial_state ())
                (Expr.to_uprog Arch.asmOp cprog)
                ii
                (Conv.cfun_of_fun tbl f)
                []
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

    begin match Compile.compile (module Arch) visit_prog_after_pass prog tbl cprog with
    | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:!debug tbl) tbl e in
      raise (HiError e)
    | Utils0.Ok asm ->
      if !outfile <> "" then begin
        BatFile.with_file_out !outfile (fun out ->
          let fmt = BatFormat.formatter_of_out_channel out in
          Format.fprintf fmt "%a%!" (Arch.pp_asm tbl) asm);
          if !debug then Format.eprintf "assembly listing written@."
      end else if List.mem Compiler.Assembly !print_list then
          Format.printf "%a%!" (Arch.pp_asm tbl) asm
    end
    end
  with
  | Utils.HiError e ->
    Format.eprintf "%a@." pp_hierror e;
    exit 1

  | UsageError ->
    Arg.usage options usage_msg;
    exit 1

  | CLIerror e ->
    Format.eprintf "%a: %s.\n"
      (pp_print_bold_red Format.pp_print_string) "Error"
      (pp_cli_error e);
    exit 1
