open Core.Std
open OUnit
open IL
open Util

module F  = Format
module PU = ParserUtil
module C  = Ctypes
module CF = Foreign

(* --------------------------------------------------------------------- *)
(* Utility functions *)

let il_to_asm_string trafos il_string =
  let st = PU.parse ~parse:ILP.stmt "<none>" il_string in
  let asm_code = match ILC.apply_transform_asm (trafos^"asm[x86-64]") st with
    | `IL _        -> assert false
    | `Asm_X64 a -> a
  in
  fsprintf "%a" Asm_X64.pp_instrs asm_code

let il_to_il_string trafos il_string =
  let st = PU.parse ~parse:ILP.stmt "<none>" il_string in
  let st = match ILC.apply_transform_asm trafos st with
    | `IL st      -> st
    | `Asm_X64 _ -> assert false
  in
  fsprintf "%a" ILL.pp_stmt st

let create_library asm_string =
  let fn_s = Filename.temp_file "code" ".s" in
  let fn_o = Filename.temp_file "code" ".o" in
  let fn_lib = Filename.temp_file "libotest" ".so" in
  
  Out_channel.write_all fn_s ~data:asm_string;
  ignore (Unix.system ("as -o "^fn_o^" "^fn_s));
  ignore (Unix.system ("gcc -fPIC -shared "^fn_o^" -o "^fn_lib));
  Sys.remove fn_s;
  Sys.remove fn_o;
  let lib = Dl.(dlopen ~filename:fn_lib ~flags:[RTLD_NOW]) in
  (lib, fn_lib)

(* --------------------------------------------------------------------- *)
(* Simple test for checking that compiled code is callable *)

let add_il = String.concat ~sep:"\n"
  [ "%rdi += %rsi;";
    "%rax = %rdi;"
  ]

let test_assemble_run () =
  let asm_code = il_to_asm_string "" add_il in
  let (lib,fn_lib) = create_library asm_code in
  let test = CF.foreign "test" C.(uint64_t @-> uint64_t @-> returning uint64_t) ~from:lib in
  let module U = Unsigned.UInt64 in
  let a = U.of_int 3 in
  let b = U.of_int 8 in
  let res = test a b in
  (* F.printf ">> a=%s, b=%s, result=%s\n%!" (U.to_string a) (U.to_string b) (U.to_string res); *)
  Sys.remove fn_lib;
  assert_equal ~msg:"result returned by add_il" res (U.of_int 11)


(* --------------------------------------------------------------------- *)
(* Tests for register allocation *)

let add_il3 = In_channel.read_all "examples/test-register-alloc2.mil"

let test_reg_assemble_run trafo il_string () =
  try
    let asm_code = il_to_asm_string trafo il_string in
    print_endline asm_code;
    let (lib,fn_lib) = create_library asm_code in
    let test = CF.foreign "test" C.(uint64_t @-> uint64_t @-> returning uint64_t) ~from:lib in
    let module U = Unsigned.UInt64 in
    let a = U.of_int 3 in
    let b = U.of_int 8 in
    let res = test a b in
    (* F.printf ">> a=%s, b=%s, result=%s\n%!" (U.to_string a) (U.to_string b) (U.to_string res); *)
    Sys.remove fn_lib;
    assert_equal ~msg:"result returned by add_il" res (U.of_int 11)
  with
    e ->
      F.printf "unknown error: %s,\n%s" (Exn.to_string e) (Exn.backtrace ());
      raise e

let t_reg1 =
  test_reg_assemble_run "expand[],ssa,register_allocate,"
    (In_channel.read_all "examples/test-register-alloc.mil")

let t_reg2 =
  test_reg_assemble_run "expand[n=5],ssa,register_allocate,"
    (In_channel.read_all "examples/test-register-alloc2.mil")

let t_reg3 () =
  let trafo = "ssa,equal_dest_src" in
  let il_string = In_channel.read_all "examples/test-register-alloc3.mil" in
  let il_code = il_to_il_string trafo il_string in
  print_endline il_code

let t_reg4 =
  test_reg_assemble_run "expand[n=5],ssa,register_allocate,"
    (In_channel.read_all "examples/test-register-alloc3.mil")



(* --------------------------------------------------------------------- *)
(* Test suite *)

let tests =
  [ (* "assemble and run" >:: test_assemble_run;
    "allocate registers, assemble and run" >:: t_reg1;
    "allocate registers, assemble and run" >:: t_reg2; 
    "allocate registers, assemble and run" >:: t_reg3; *)
    "allocate registers, assemble and run" >:: t_reg4
  ]
