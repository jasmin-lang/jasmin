(** Safety checker test runner.

    The runner automatically detects the target architecture from the directory structure.

    Directory structure:
    - success/{x86-64,arm-m4,risc-v,common}/ : Tests that should pass safety checking
    - fail/{x86-64,arm-m4,risc-v,common}/    : Tests that should fail safety checking
*)

open Jasmin
open Prog
open Utils
open Jasmin_checksafety

(** Specific configuration for some example programs. *)
let config path =
  Glob_options.safety_param :=
    List.assoc_opt path
      [
        ("fail/x86-64/loop2.jazz", "poly1305>in;");
        ("fail/arm-m4/loop2.jazz", "poly1305>in;");
        ("fail/risc-v/loop2.jazz", "poly1305>in;");
        ("success/x86-64/loop3.jazz", "poly1305>in;");
        ("success/arm-m4/loop3.jazz", "poly1305>in;");
        ("success/risc-v/loop3.jazz", "poly1305>in;");
        ("fail/x86-64/popcnt.jazz", "off_by_one>;");
      ]

(* taken from main_compiler.ml *)
module type ArchWithAnalyze = sig
  module A : Arch_full.Arch
  val analyze :
    ?fmt:Format.formatter ->
    (unit, (A.reg, A.regx, A.xreg, A.rflag, A.cond, A.asm_op, A.extra_op) Arch_extra.extended_op) func ->
    (unit, (A.reg, A.regx, A.xreg, A.rflag, A.cond, A.asm_op, A.extra_op) Arch_extra.extended_op) func ->
    (unit, (A.reg, A.regx, A.xreg, A.rflag, A.cond, A.asm_op, A.extra_op) Arch_extra.extended_op) prog ->
    bool
end

let load_file arch_info pointer_data msf_size asmOp name =
  let open Pretyping in
  name
  |> tt_file arch_info Env.empty None None
  |> fst |> Env.decls
  |> Compile.preprocess pointer_data msf_size asmOp

let load_and_analyze ~fmt expect path arch =
  let (module P : ArchWithAnalyze) =
    match arch with
    | X86_64 ->
       (module struct
          module C = (val CoreArchFactory.core_arch_x86 ~use_lea:!Glob_options.lea ~use_set0:!Glob_options.set0 Linux)
          module A = Arch_full.Arch_from_Core_arch (C)
          module Safety = SafetyMain.Make (Jasmin_checksafety.X86_safety.X86_safety (A))
          let analyze = Safety.analyze
        end)
    | ARM_M4 ->
       (module struct
          module C = CoreArchFactory.Core_arch_ARM
          module A = Arch_full.Arch_from_Core_arch (C)
          open Jasmin_checksafety
          module Safety = SafetyMain.Make (Jasmin_checksafety.Arm_safety.Arm_safety (A))
          let analyze = Safety.analyze
        end)
    | RISCV ->
       (module struct
          module C = CoreArchFactory.Core_arch_RISCV
          module A = Arch_full.Arch_from_Core_arch (C)
          open Jasmin_checksafety
          module Safety = SafetyMain.Make (Jasmin_checksafety.Riscv_safety.Riscv_safety (A))
          let analyze = Safety.analyze
        end)
  in
  let module Arch = P.A in
  Format.fprintf fmt "File %s (on arch %s):@." path (architecture_to_string arch);
  let ((_, fds) as p) = load_file Arch.arch_info Arch.pointer_data Arch.msf_size Arch.asmOp path in
  List.iter
    (fun fd ->
      if FInfo.is_export fd.Prog.f_cc then
        let () =
          Format.fprintf fmt "@[<v>Analyzing function %s@]" fd.f_name.fn_name
        in
        let safe = P.analyze ~fmt fd fd p in
        if (safe <> expect) then begin
          Format.eprintf "File %s: the program is %s, while it was expected to be %s@."
            path
            (if expect then "unsafe" else "safe")
            (if expect then "safe" else "unsafe");
          assert false
        end)
    fds

let doit ~fmt expect archs path () =
  config path;
  List.iter (load_and_analyze ~fmt expect path) archs

let () =
  let fmt = Format.std_formatter in
  Common.check_dir (doit ~fmt false) [] "fail" ();
  (* Discard messages from successful tests *)
  let fmt = Format.make_formatter (fun _ _ _ -> ()) (fun () -> ()) in
  Common.check_dir (doit ~fmt true) [] "success" ()
