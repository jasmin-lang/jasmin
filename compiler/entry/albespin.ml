open Jasmin

module Arch =
  (val let use_set0 = true and use_lea = false in
       let call_conv = Glob_options.Linux in
       let module C : Arch_full.Core_arch =
         (val CoreArchFactory.core_arch_x86 ~use_lea ~use_set0 call_conv)
       in
       (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch))

let check ~debug:_ pass prog =
  if pass = Compiler.PropagateInline then
    let open Sct_checker_forward in
    match ty_prog Arch.is_ct_sopn prog [] with
    | exception Utils.HiError e ->
        Format.eprintf "%a@." Utils.pp_hierror e;
        exit 1
    | r ->
        List.iter (Format.printf "%a@." pp_funty) r;
        exit 0

let () =
  try
    Sys.argv.(1)
    |> Pretyping.tt_file Arch.arch_info Pretyping.Env.empty None None
    |> fst |> Pretyping.Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp
    |> fun prog ->
    let cprog = Conv.cuprog_of_prog prog in
    Compile.compile (module Arch) check prog cprog |> ignore
  with
  | Pretyping.TyError (loc, e) ->
      Format.eprintf "%a: %a@." Location.pp_loc loc Pretyping.pp_tyerror e;
      exit 2
  | Syntax.ParseError (loc, None) ->
      Format.eprintf "Parse error: %a@." Location.pp_loc loc;
      exit 3
  | Invalid_argument _ ->
      Format.eprintf "usage: %s FILE" Sys.argv.(0);
      exit 4
