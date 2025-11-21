(** Architecture-specific safety checker test runner.
    
    This test runner verifies the safety checker's ability to detect memory safety
    violations across multiple target architectures (x86-64, ARMv7-M, and RISC-V).
    
    The runner automatically detects the target architecture from the directory structure
    and dispatches to the appropriate architecture-specific processor module. This design
    avoids OCaml's module type escaping issues while maintaining clean separation of
    architecture-specific concerns.
    
    Directory structure:
    - success/{x86-64,arm-m4,risc-v}/ : Tests that should pass safety checking
    - fail/{x86-64,arm-m4,risc-v}/    : Tests that should fail safety checking
    
    Test execution:
    1. Recursively traverse test directories
    2. Detect architecture from path (e.g., "fail/arm-m4/test.jazz" → ARM-M4)
    3. Load and preprocess the test file with architecture-specific settings
    4. Run safety analysis using the appropriate SafetyArch module
    5. Assert that the result matches expectations (pass vs. fail)
    
    Usage:
      dune exec safety/run.exe                  # Normal mode: only failing tests show output
      dune exec safety/run.exe -- -v            # Verbose: show all test outputs
      dune exec safety/run.exe -- -q            # Quiet: suppress all output except errors
      dune exec safety/run.exe -- --help        # Show usage information
*)

open Jasmin
open Jasmin_checksafety

(** Verbosity level for test output.
    - Quiet (0): Only show errors and assertion failures
    - Normal (1): Show failing test outputs (default)
    - Verbose (2): Show all test outputs including successful ones
*)
let verbosity = ref 1

(** Architecture-specific safety analysis parameters.
    
    Maps test file paths to function-specific safety parameters. These parameters
    control specific aspects of the safety analysis, such as which functions or
    variables to focus on during pointer analysis.
    
    Format: (file_path, "function_name>variable;")
    Example: ("success/x86-64/loop2.jazz", "poly1305>in;") means analyze the 'in'
    parameter of the 'poly1305' function in that file.
*)
let params =
  [
    ("success/x86-64/loop2.jazz", "poly1305>in;");
    ("success/x86-64/loop3.jazz", "poly1305>in;");
    ("fail/x86-64/popcnt.jazz", "off_by_one>;");
  ]



(** X86-64 architecture processor *)
module X86Processor = struct
  module Arch =
    (val let use_set0 = !Glob_options.set0 and use_lea = !Glob_options.lea in
         let call_conv = !Glob_options.call_conv in
         let module C =
           (val CoreArchFactory.core_arch_x86 ~use_lea ~use_set0 call_conv)
         in
         (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch
           with type reg = X86_decl.register
            and type regx = X86_decl.register_ext
            and type xreg = X86_decl.xmm_register
            and type rflag = X86_decl.rflag
            and type cond = X86_decl.condt
            and type asm_op = X86_instr_decl.x86_op
            and type extra_op = X86_extra.x86_extra_op))

  module Safety = SafetyMain.Make (X86_safety.X86_safety (Arch))

  let load_file name =
    let open Pretyping in
    name
    |> tt_file Arch.arch_info Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp

  let load_and_analyze ~fmt expect path name =
    let name = Filename.concat path name in
    Format.fprintf fmt "File %s:@." name;
    Glob_options.safety_param := List.assoc_opt name params;
    try
      let ((_, fds) as p) = load_file name in
      List.iter
        (fun fd ->
          if FInfo.is_export fd.Prog.f_cc then
            let () =
              Format.fprintf fmt "@[<v>Analyzing function %s@]" fd.f_name.fn_name
            in
            let safe = Safety.analyze ~fmt fd fd p in
            if safe <> expect then begin
              Format.eprintf "@[<v>Assertion failed for file %s, function %s:@," name fd.f_name.fn_name;
              Format.eprintf "Expected: %s, Got: %s@]@." 
                (if expect then "safe" else "unsafe")
                (if safe then "safe" else "unsafe")
            end;
            assert (safe = expect))
        fds
    with
    | Pretyping.TyError (loc, code) ->
        Format.eprintf "@[<v>Type error in file %s:@," name;
        Format.eprintf "Location: %a@," Location.pp_loc loc;
        Format.eprintf "Error code: %a@]@." Pretyping.pp_tyerror code;
        raise (Pretyping.TyError (loc, code))
    | exn ->
        Format.eprintf "@[<v>Exception while processing file %s:@,%s@]@." 
          name (Printexc.to_string exn);
        raise exn
end

(** ARM Cortex-M4 architecture processor *)
module ARMProcessor = struct
  module Arch =
    (val let module C = CoreArchFactory.Core_arch_ARM in
         (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch
           with type reg = Arm_decl.register
            and type regx = Arch_utils.empty
            and type xreg = Arch_utils.empty
            and type rflag = Arm_decl.rflag
            and type cond = Arm_decl.condt
            and type asm_op = Arm_instr_decl.arm_op
            and type extra_op = Arm_extra.arm_extra_op))

  module Safety = SafetyMain.Make (Arm_safety.Arm_safety (Arch))

  let load_file name =
    let open Pretyping in
    name
    |> tt_file Arch.arch_info Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp

  let load_and_analyze ~fmt expect path name =
    let name = Filename.concat path name in
    Format.fprintf fmt "File %s:@." name;
    Glob_options.safety_param := List.assoc_opt name params;
    try
      let ((_, fds) as p) = load_file name in
      List.iter
        (fun fd ->
          if FInfo.is_export fd.Prog.f_cc then
            let () =
              Format.fprintf fmt "@[<v>Analyzing function %s@]" fd.f_name.fn_name
            in
            let safe = Safety.analyze ~fmt fd fd p in
            if safe <> expect then begin
              Format.eprintf "@[<v>Assertion failed for file %s, function %s:@," name fd.f_name.fn_name;
              Format.eprintf "Expected: %s, Got: %s@]@." 
                (if expect then "safe" else "unsafe")
                (if safe then "safe" else "unsafe");
              Format.eprintf "@.Re-running analysis with full output:@.";
              let _ = Safety.analyze ~fmt:Format.err_formatter fd fd p in
              ()
            end;
            assert (safe = expect))
        fds
    with
    | Pretyping.TyError (loc, code) ->
        Format.eprintf "@[<v>Type error in file %s:@," name;
        Format.eprintf "Location: %a@," Location.pp_loc loc;
        Format.eprintf "Error code: %a@]@." Pretyping.pp_tyerror code;
        raise (Pretyping.TyError (loc, code))
    | exn ->
        Format.eprintf "@[<v>Exception while processing file %s:@,%s@]@." 
          name (Printexc.to_string exn);
        raise exn
end

(** RISC-V architecture processor *)
module RISCVProcessor = struct
  module Arch =
    (val let module C = CoreArchFactory.Core_arch_RISCV in
         (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch
           with type reg = Riscv_decl.register
            and type regx = Arch_utils.empty
            and type xreg = Arch_utils.empty
            and type rflag = Arch_utils.empty
            and type cond = Riscv_decl.condt
            and type asm_op = Riscv_instr_decl.riscv_op
            and type extra_op = Riscv_extra.riscv_extra_op))

  module Safety = SafetyMain.Make (Riscv_safety.Riscv_safety (Arch))

  let load_file name =
    let open Pretyping in
    name
    |> tt_file Arch.arch_info Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp

  let load_and_analyze ~fmt expect path name =
    let name = Filename.concat path name in
    Format.fprintf fmt "File %s:@." name;
    Glob_options.safety_param := List.assoc_opt name params;
    try
      let ((_, fds) as p) = load_file name in
      List.iter
        (fun fd ->
          if FInfo.is_export fd.Prog.f_cc then
            let () =
              Format.fprintf fmt "@[<v>Analyzing function %s@]" fd.f_name.fn_name
            in
            let safe = Safety.analyze ~fmt fd fd p in
            if safe <> expect then begin
              Format.eprintf "@[<v>Assertion failed for file %s, function %s:@," name fd.f_name.fn_name;
              Format.eprintf "Expected: %s, Got: %s@]@." 
                (if expect then "safe" else "unsafe")
                (if safe then "safe" else "unsafe");
              Format.eprintf "@.Re-running analysis with full output:@.";
              let _ = Safety.analyze ~fmt:Format.err_formatter fd fd p in
              ()
            end;
            assert (safe = expect))
        fds
    with
    | Pretyping.TyError (loc, code) ->
        Format.eprintf "@[<v>Type error in file %s:@," name;
        Format.eprintf "Location: %a@," Location.pp_loc loc;
        Format.eprintf "Error code: %a@]@." Pretyping.pp_tyerror code;
        raise (Pretyping.TyError (loc, code))
    | exn ->
        Format.eprintf "@[<v>Exception while processing file %s:@,%s@]@." 
          name (Printexc.to_string exn);
        raise exn
end


(** Detect target architecture from file path.
    
    Uses pattern matching on the directory structure to determine which architecture
    a test file targets. This allows a single unified test runner to handle all
    architectures without needing separate executables.
    
    Recognition patterns:
    - Contains "arm-m4" → ARM Cortex-M4
    - Contains "riscv" → RISC-V
    - Everything else → x86-64 (default)
    
    The path is normalized to lowercase before matching to handle case variations.
    
    @param path File path to analyze (e.g., "fail/arm-m4/test.jazz")
    @return Architecture tag (`X86, `ARM, or `RISCV)
*)
let detect_arch path =
  let normalized = String.lowercase_ascii path in
  if Str.string_match (Str.regexp ".*arm-m4.*") normalized 0 then `ARM
  else if Str.string_match (Str.regexp ".*riscv.*") normalized 0 then `RISCV
  else `X86

(** Process a single test file by dispatching to the appropriate architecture processor.
    
    This is the key dispatch function that:
    1. Detects the architecture from the file path
    2. Calls the appropriate processor's load_and_analyze function
    
    Each architecture processor handles all the architecture-specific details
    (types, modules, analysis logic), keeping the dispatch logic clean and simple.
    
    @param fmt Output formatter for test results
    @param expect Expected safety result (true = safe, false = unsafe)
    @param path Directory containing the test file
    @param name Name of the test file
*)
let process_file ~fmt expect path name =
  let full_path = Filename.concat path name in
  match detect_arch full_path with
  | `X86 -> X86Processor.load_and_analyze ~fmt expect path name
  | `ARM -> ARMProcessor.load_and_analyze ~fmt expect path name
  | `RISCV -> RISCVProcessor.load_and_analyze ~fmt expect path name

(** Recursively process all test files in a directory tree.
    
    Traverses the directory structure looking for .jazz files to test:
    - Directories are processed recursively
    - .jazz files are passed to process_file for architecture-specific handling
    - Other files are ignored
    
    The recursive traversal allows organizing tests in subdirectories by architecture
    (e.g., fail/x86-64/, fail/arm-m4/) while using a single test runner.
    
    @param fmt Output formatter for test results
    @param expect Expected safety result for files in this directory
    @param path Directory to process
*)
let rec doit ~fmt expect path =
  if Sys.file_exists path && Sys.is_directory path then
    let cases = Sys.readdir path in
    Array.sort String.compare cases;  (* Sort for deterministic test ordering *)
    Array.iter
      (fun case ->
        let full_path = Filename.concat path case in
        if Sys.is_directory full_path then
          (* Recursively process subdirectories *)
          doit ~fmt expect full_path
        else if Filename.check_suffix case ".jazz" then
          process_file ~fmt expect path case)
      cases
  else if Sys.file_exists path then
    Format.fprintf fmt "Path %s is not a directory, skipping@." path
  else
    Format.fprintf fmt "Directory %s does not exist, skipping@." path

(** Main test runner entry point.
    
    Executes the test suite in two phases:
    
    1. Failing tests (fail/ directory):
       - Should detect safety violations
       - Output controlled by verbosity level
       - Assertions verify that safety analysis correctly reports "unsafe"
    
    2. Successful tests (success/ directory):
       - Should pass safety checking
       - Output controlled by verbosity level
       - Assertions verify that safety analysis correctly reports "safe"
    
    The test suite recursively processes all .jazz files in the directory tree,
    automatically detecting the target architecture from the path and dispatching
    to the appropriate processor.
    
    Verbosity levels:
    - 0 (quiet): No output except assertion failures
    - 1 (normal): Show failing test outputs only (default)
    - 2 (verbose): Show all test outputs
    
    Exit behavior:
    - Success: All assertions pass (exit code 0)
    - Failure: Any assertion fails, dune reports the test failure
*)
let () =
  (* Parse command-line arguments *)
  let usage_msg = "Usage: run.exe [OPTIONS]\nRun safety checker tests for all architectures." in
  let show_help = ref false in
  let specs = [
    ("-v", Arg.Unit (fun () -> verbosity := 2), " Verbose mode: show all test outputs");
    ("--verbose", Arg.Unit (fun () -> verbosity := 2), " Verbose mode: show all test outputs");
    ("-q", Arg.Unit (fun () -> verbosity := 0), " Quiet mode: suppress all output except errors");
    ("--quiet", Arg.Unit (fun () -> verbosity := 0), " Quiet mode: suppress all output except errors");
    ("--help", Arg.Set show_help, " Display this help message");
    ("-help", Arg.Set show_help, " Display this help message");
  ] in
  Arg.parse specs (fun _ -> ()) usage_msg;
  
  if !show_help then begin
    Arg.usage specs usage_msg;
    exit 0
  end;
  
  (* Determine the directory where test files are located.
     When run via 'dune runtest', cwd is compiler/tests/safety.
     When run via 'dune exec tests/safety/run.exe', cwd is compiler.
     Detect location and construct paths accordingly. *)
  let fail_path, success_path =
    if Sys.file_exists "fail" && Sys.file_exists "success" then
      (* Already in tests/safety directory *)
      ("fail", "success")
    else if Sys.file_exists "tests/safety/fail" && Sys.file_exists "tests/safety/success" then
      (* In compiler directory - need to prefix with tests/safety/ *)
      ("tests/safety/fail", "tests/safety/success")
    else
      (* Fallback to current directory paths, will show skip messages if not found *)
      ("fail", "success")
  in
  
  (* Determine formatter based on verbosity *)
  let make_formatter level =
    if !verbosity >= level then
      Format.std_formatter
    else
      (* Suppress output by creating a dummy formatter *)
      Format.make_formatter (fun _ _ _ -> ()) (fun () -> ())
  in
  
  (* Process failing tests - show output based on verbosity (default: show) *)
  let fail_fmt = make_formatter 1 in
  doit ~fmt:fail_fmt false fail_path;
  
  (* Process successful tests - show output only in verbose mode *)
  let success_fmt = make_formatter 2 in
  doit ~fmt:success_fmt true success_path

