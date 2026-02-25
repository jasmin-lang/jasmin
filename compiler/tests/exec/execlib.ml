open Jasmin

module Arch : Arch_full.Arch =
  (val let use_set0 = true and use_lea = true in
       let call_conv = Glob_options.Linux in
       let module C : Arch_full.Core_arch =
         (val CoreArchFactory.core_arch_x86 ~use_lea ~use_set0 call_conv)
       in
       (module Arch_full.Arch_from_Core_arch (C) : Arch_full.Arch))

let funnames prog =
  let tbl = Hashtbl.create 17 in
  List.iter
    (fun { Prog.f_name; _ } -> Hashtbl.add tbl f_name.fn_name f_name)
    (snd prog);
  tbl

let load_file name =
  let prog =
    let open Pretyping in
    try
      name
      |> tt_file Arch.arch_info Compile.syscall_length_ident Env.empty None None
      |> fst |> Env.decls
      |> Compile.preprocess Arch.pointer_data Arch.msf_size Arch.asmOp
    with TyError (loc, e) ->
      Format.eprintf "%a: %a@." Location.pp_loc loc pp_tyerror e;
      assert false
  in
  (funnames prog, Conv.cuprog_of_prog prog)

let init_memory ms =
  match Evaluator.initial_memory Arch.reg_size (Z.of_int 1024) ms with
  | Utils0.Error _err -> assert false
  | Utils0.Ok m -> m

let exec (fs, prog) ms f args =
  let f = Hashtbl.find fs f in
  let m = init_memory ms in
  let res =
    match
      Evaluator.run
        (module Arch)
        (Expr.to_uprog Arch.asmOp prog)
        IInfo.dummy f args m
    with
    | _m, res -> Ok res
    | exception Evaluator.Eval_error (_, err) -> Error err
  in
  let pp_vals = Utils.pp_list "; " Evaluator.pp_val in
  let pp_res fmt = function
    | Ok res ->
        Format.fprintf fmt "=%s%a" (if res <> [] then " " else "") pp_vals res
    | Error err -> Format.fprintf fmt "failed with %a" Evaluator.pp_error err
  in
  Format.printf "%s(%a) %a@." f.fn_name pp_vals args pp_res res
