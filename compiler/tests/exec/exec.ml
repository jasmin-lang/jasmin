open Execlib

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

let () =
  let prog = load_file "../success/x86-64/test_global_string_literal.jazz" in
  exec prog [] "main" []
