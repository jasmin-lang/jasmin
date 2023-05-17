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
    name
    |> tt_file Arch.reg_size Arch.asmOp_sopn Env.empty None None
    |> fst |> Env.decls
    |> Compile.preprocess Arch.reg_size Arch.asmOp
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
    | Ok res -> Format.fprintf fmt "= %a" pp_vals res
    | Error err -> Format.fprintf fmt "failed with %a" Evaluator.pp_error err
  in
  Format.printf "%s(%a) %a@." f.fn_name pp_vals args pp_res res

let () =
  let prog = load_file "basic.jazz" in
  exec prog [] "f" [];
  exec prog [] "ft" [];
  exec prog [ (Z.of_string "0x1000", Z.of_int 8) ] "mem" [];
  exec prog [ (Z.of_string "0x1000", Z.of_int 16) ] "mem1" []

let () =
  let prog = load_file "../success/x86-64/clc-stc.jazz" in
  exec prog [] "test_stc" [];
  exec prog [] "test_clc" []

let () =
  let prog = load_file "poly1305.jazz" in
  exec prog
    [
      (Z.of_int 0x1200, Z.of_int 16);
      (Z.of_int 0x1100, Z.of_int 32);
      (Z.of_int 0x1000, Z.of_int 34);
    ]
    "test_poly1305" []

let () =
  let prog = load_file "return-undef.jazz" in
  exec prog [] "f" []

let () =
  let prog = load_file "cmoveptr.jazz" in
  exec prog [] "zero" [];
  exec prog [] "one" []

let () =
  let prog = load_file "../success/subroutines/x86-64/literal-argument.jazz" in
  exec prog [] "one" []

let () =
  let prog = load_file "for.jazz" in
  exec prog [] "test_for" [];
  exec prog [] "test_param" []

let () =
  let prog = load_file "inline-call.jazz" in
  exec prog [] "test" []

let () =
  let prog = load_file "../success/x86-64/lzcnt.jazz" in
  exec prog [] "foo" []

let () =
  let prog = load_file "../success/x86-64/test_parity.jazz" in
  exec prog [] "test_parity" []

let () =
  let prog = load_file "../success/x86-64/test_ptr_fn_inline.jazz" in
  exec prog [] "foo" []

let () =
  let prog = load_file "vpsxldq.jazz" in
  exec prog [ (Z.of_int 0x480, Z.of_int 64) ] "etest" []
