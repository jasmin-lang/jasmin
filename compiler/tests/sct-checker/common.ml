open Jasmin

module Arch =
  (val let use_set0 = true and use_lea = true in
       let call_conv = Glob_options.Linux in
       let module C : Arch_full.Core_arch =
         (val CoreArchFactory.core_arch_x86 ~use_lea ~use_set0 call_conv)
       in
       (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch))

let load_file name =
  let open Pretyping in
  match
    name
    |> tt_file Arch.arch_info Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp
    |> Compile.do_spill_unspill Arch.asmOp
  with
  | exception TyError (loc, e) ->
      Format.eprintf "%a: %a@." Location.pp_loc loc pp_tyerror e;
      assert false
  | exception Syntax.ParseError (loc, None) ->
      Format.eprintf "Parse error: %a@." Location.pp_loc loc;
      assert false
  | Error msg ->
      Format.eprintf "%a@." Utils.pp_hierror msg;
      assert false
  | Ok p -> p
