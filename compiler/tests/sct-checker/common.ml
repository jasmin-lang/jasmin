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
  try
    name
    |> tt_file Arch.arch_info Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp
  with
  | TyError (loc, e) ->
      Format.eprintf "%a: %a@." Location.pp_loc loc pp_tyerror e;
      assert false
  | Syntax.ParseError (loc, None) ->
      Format.eprintf "Parse error: %a@." Location.pp_loc loc;
      assert false

let ty_prog p fl =
  let sigs, status = Sct_checker_forward.ty_prog ~infer:true p fl in
  match status with
  | None ->
      List.iter (Format.printf "%a@." (Sct_checker_forward.pp_signature p)) sigs
  | Some (loc, msg) ->
      Utils.hierror ~loc:(Lone loc) ~kind:"SCT checker" "%t" msg
