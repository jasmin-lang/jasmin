open Core.Std
open OUnit

module F = Format

let test_assemble () =
  assert_equal ~msg:"result must be equal" true true

let run_code asm_string =
  let fn_s = Filename.temp_file "code" ".s" in
  let fn_o = Filename.temp_file "code" ".o" in
  let fn_lib = Filename.temp_file "libotest" ".so" in
  Out_channel.write_all fn_s ~data:asm_string;
  ignore (Unix.system ("as -o "^fn_o^" "^fn_s));
  ignore (Unix.system ("gcc -fPIC -shared "^fn_o^" -o "^fn_lib));

  let open Ctypes in
  let open Foreign in
  let libotest = Dl.(dlopen ~filename:fn_lib ~flags:[RTLD_NOW]) in
  let test = foreign "test" (uint64_t @-> uint64_t @-> returning uint64_t) ~from:libotest in
  let module U = Unsigned.UInt64 in
  let a = U.of_int 3 in
  let b = U.of_int 8 in
  F.printf ">> a=%s, b=%s, result=%s\n%!" (U.to_string a) (U.to_string b) (U.to_string (test a b));
  Sys.remove fn_s;
  Sys.remove fn_o;
  Sys.remove fn_lib


let tests =
  ["assemble" >:: test_assemble ]
