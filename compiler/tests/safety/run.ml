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

let load_file arch_info pointer_data msf_size asmOp name =
  try
    let open Pretyping in
    name
    |> tt_file arch_info Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess pointer_data msf_size asmOp
  with Syntax.ParseError (loc, msg) ->
    Format.eprintf "%a: %s@." Location.pp_loc loc
      (Option.default "parse error" msg);
    assert false

let load_and_analyze ~fmt ~safety_param expect path arch =
  let (module P) = SafetyMain.get_arch_with_analyze arch Linux in
  let module Arch = P.A in
  Format.fprintf fmt "File %s (on arch %s):@." path (architecture_to_string arch);
  let ((_, fds) as p) = load_file Arch.arch_info Arch.pointer_data Arch.msf_size Arch.asmOp path in
  List.iter
    (fun fd ->
      if FInfo.is_export fd.Prog.f_cc then
        let () =
          Format.fprintf fmt "@[<v>Analyzing function %s@]" fd.f_name.fn_name
        in
        let safe = P.analyze ~fmt ~safety_param fd p in
        if safe <> expect then begin
          Format.eprintf
            "File %s: the program is %s, while it was expected to be %s@." path
            (if expect then "unsafe" else "safe")
            (if expect then "safe" else "unsafe");
          assert false
        end)
    fds

let doit ~fmt expect archs path () =
  let safety_param = config path in
  List.iter (load_and_analyze ~fmt ~safety_param expect path) archs

let () =
  let fmt = Format.std_formatter in
  Common.check_dir (doit ~fmt false) [] "fail" ();
  (* Discard messages from successful tests *)
  let fmt = Format.make_formatter (fun _ _ _ -> ()) (fun () -> ()) in
  Common.check_dir (doit ~fmt true) [] "success" ()
