open Jasmin
open Utils
open Jasmin_checksafety

let params =
  [
    ("success/loop2.jazz", "poly1305>in;");
    ("success/loop3.jazz", "poly1305>in;");
    ("fail/popcnt.jazz", "off_by_one>;");
  ]

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
  try
    let open Pretyping in
    name
    |> tt_file Arch.arch_info Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp
  with Syntax.ParseError (loc, msg) ->
    Format.eprintf "%a: %s@." Location.pp_loc loc
      (Option.default "parse error" msg);
    assert false

let load_and_analyze ~fmt expect path name =
  let name = Filename.concat path name in
  Format.fprintf fmt "File %s:@." name;
  Glob_options.safety_param := List.assoc_opt name params;
  let ((_, fds) as p) = load_file name in
  List.iter
    (fun fd ->
      if FInfo.is_export fd.Prog.f_cc then
        let () =
          Format.fprintf fmt "@[<v>Analyzing function %s@]" fd.f_name.fn_name
        in
        let safe = Safety.analyze ~fmt fd fd p in
        assert (safe = expect))
    fds

let doit ~fmt expect path =
  let cases = Sys.readdir path in
  Array.sort String.compare cases;
  Array.iter (load_and_analyze ~fmt expect path) cases

let () =
  let fmt = Format.std_formatter in
  doit ~fmt false "fail";
  (* Discard messages from successful tests *)
  let fmt = Format.make_formatter (fun _ _ _ -> ()) (fun () -> ()) in
  doit ~fmt true "success"
