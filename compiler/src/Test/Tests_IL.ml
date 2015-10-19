open Core_kernel.Std
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
  let efuns = PU.parse ~parse:ILP.efuns "<none>" il_string in
  let efun = match efuns with
    | [f] -> f
    | _ -> assert false
  in
  let acode = match ILT.apply_transform_asm (trafos^"asm[x86-64]") efun with
    | `IL _      -> assert false
    | `Asm_X64 a -> ILC.wrap_asm_function a
  in
  (* F.printf "%a" Asm_X64.pp_instrs acode; *)
  fsprintf "%a" Asm_X64.pp_instrs acode

let il_to_il_string trafos il_string =
  let efuns = PU.parse ~parse:ILP.efuns "<none>" il_string in
  let efun = match efuns with
    | [f] -> f
    | _ -> assert false
  in
  let efun = match ILT.apply_transform_asm trafos efun with
    | `IL st     -> st
    | `Asm_X64 _ -> assert false
  in
  fsprintf ">> test result:@\n%a" ILU.pp_efun efun

let create_library asm_string =
  let fn_s   = Filename.temp_file "code" ".s" in
  let fn_o   = Filename.temp_file "code" ".o" in
  let fn_lib = Filename.temp_file "libotest" ".so" in
  
  Out_channel.write_all fn_s ~data:asm_string;
  ignore (Unix.system ("as -o "^fn_o^" "^fn_s));
  ignore (Unix.system ("gcc -fPIC -shared "^fn_o^" -o "^fn_lib));
  Sys.remove fn_s;
  Sys.remove fn_o;
  let lib = Dl.(dlopen ~filename:fn_lib ~flags:[RTLD_NOW]) in
  (lib, fn_lib)

(* --------------------------------------------------------------------- *)
(* Tests for register allocation *)

let add_il3 = In_channel.read_all "examples/test-register-alloc2.mil"

let test_reg_assemble_run trafo il_string () =
  try
    let asm_code = il_to_asm_string trafo il_string in
    print_endline asm_code;
    let (lib,fn_lib) = create_library asm_code in
    let test =
      CF.foreign "test" C.(uint64_t @-> uint64_t @-> returning uint64_t) ~from:lib
    in
    let module U = Unsigned.UInt64 in
    let a = U.of_int 3 in
    let b = U.of_int 8 in
    let res = test a b in
    (* F.printf ">> a=%s, b=%s, result=%s\n%!"
         (U.to_string a) (U.to_string b) (U.to_string res); *)
    Sys.remove fn_lib;
    assert_equal ~msg:"result returned by add_il" res (U.of_int 11)
  with
    e ->
      F.printf "unknown error: %s,\n%s" (Exn.to_string e) (Exn.backtrace ());
      raise e

let usable_regs = String.concat ~sep:","
  [ "rdi"; "rsi"; "rdx"; "rcx"; "r8"; "r9"; "rax"
  ; "r10"; "r11"; "r12"; "r13"; "r14"; "r15"
    (* no rbx and rsp *) ]

let t_reg3 () =
  let trafo =
    "print[orig],expand[n=4],print[expand],"
    ^"ssa,print[ssa],"
    ^"equal_dest_src,print[equal_dest_src],strip_comments,"
    ^"register_liveness,print[liveness],strip_comments,"
    ^"register_allocate[15]"
   (* ^"register_allocate["^usable_regs^"]" *)
  in
  let il_string = In_channel.read_all "examples/add-4limb.mil" in
  let il_code = il_to_il_string trafo il_string in  
  print_endline il_code

let t_reg4 =
  test_reg_assemble_run "expand[n=5],ssa,register_allocate,"
    (In_channel.read_all "examples/test-register-alloc3.mil")

let pval = Big_int_Infix.((2 ^! 255) -! (big_int_of_int 19))

let t_arithm_4limb file fun_name desc expected xval yval () =
  let trafo =
    "expand[n=3],"
    ^"ssa,strip_comments,"
    ^"register_allocate[15]," in
  let il_string = In_channel.read_all file in
  let asm_code = il_to_asm_string trafo il_string in
  let (lib,fn_lib) = create_library asm_code in
  let open Ctypes in
  let module U64 = Unsigned.UInt64 in
  let add =
    try
      CF.(foreign ~from:lib fun_name
            (ptr uint64_t @-> ptr uint64_t @-> ptr uint64_t @-> (returning void)))
    with
      _ -> (* try with prepended underscore, for Linux *)
        CF.(foreign ~from:lib ("_"^fun_name)
              (ptr uint64_t @-> ptr uint64_t @-> ptr uint64_t @-> (returning void)))
      
  in
  let z = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let x = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let y = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let (x0,x1,x2,x3) = Limb4.of_big_int xval in
  let (y0,y1,y2,y3) = Limb4.of_big_int yval in
  CArray.set x 0 x0; CArray.set x 1 x1; CArray.set x 2 x2; CArray.set x 3 x3;
  CArray.set y 0 y0; CArray.set y 1 y1; CArray.set y 2 y2; CArray.set y 3 y3;
  let () = add (CArray.start z) (CArray.start x) (CArray.start y) in
  
  let get a i = CArray.get a i in
  let (z0,z1,z2,z3) = (get z 0, get z 1, get z 2, get z 3) in
  let zval = Limb4.to_big_int (z0,z1,z2,z3) in
  (*
  F.printf "z=[%s,%s,%s,%s] = %s\nx=%a\ny=%a\np=%a\nz=%a\n%!"
    (U64.to_string z0) (U64.to_string z1) (U64.to_string z2) (U64.to_string z3)
    (Big_int.string_of_big_int zval)
    (pph 16) xval (pph 16) yval (pph 16) pval (pph 16) zval;
  *)
  Sys.remove fn_lib;
  assert_equal ~printer:Big_int.string_of_big_int ~cmp:Big_int.eq_big_int
    ~msg:desc
    Big_int_Infix.(mod_big_int expected pval)
    Big_int_Infix.(mod_big_int zval pval)

let t_add_4limb xval yval () =
  t_arithm_4limb
    "examples/add-4limb.mil"
    "add"
    "add-4-limb"
    Big_int_Infix.(xval +! yval)
    xval
    yval
    ()

let t_mul_4limb xval yval () =
  t_arithm_4limb
    "examples/mul-4limb.mil"
    "mul"
    "mul-4-limb"
    Big_int_Infix.(xval *! yval)
    xval yval ()

let t_sub_4limb xval yval () =
  t_arithm_4limb
    "examples/sub-4limb.mil"
    "sub"
    "sub-4-limb"
    Big_int_Infix.(xval -! yval)
    xval yval ()

let t_square_4limb xval () =
  let trafo =
    "expand[n=3],"
    ^"ssa,strip_comments,"
    ^"register_allocate[15]," in
  let il_string = In_channel.read_all "examples/square-4limb.mil" in
  let asm_code = il_to_asm_string trafo il_string in
  let (lib,fn_lib) = create_library asm_code in
  let open Ctypes in
  let module U64 = Unsigned.UInt64 in
  let add =
    CF.(foreign ~from:lib "square"
          (ptr uint64_t @-> ptr uint64_t @-> (returning void)))
  in
  let z = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let x = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let (x0,x1,x2,x3) = Limb4.of_big_int xval in
  CArray.set x 0 x0; CArray.set x 1 x1; CArray.set x 2 x2; CArray.set x 3 x3;
  let () = add (CArray.start z) (CArray.start x) in
  
  let get a i = CArray.get a i in
  let (z0,z1,z2,z3) = (get z 0, get z 1, get z 2, get z 3) in
  let zval = Limb4.to_big_int (z0,z1,z2,z3) in
  (*
  F.printf "z=[%s,%s,%s,%s] = %s\nx=%a\ny=%a\np=%a\nz=%a\n%!"
    (U64.to_string z0) (U64.to_string z1) (U64.to_string z2) (U64.to_string z3)
    (Big_int.string_of_big_int zval)
    (pph 16) xval (pph 16) yval (pph 16) pval (pph 16) zval;
  *)
  Sys.remove fn_lib;
  assert_equal ~printer:Big_int.string_of_big_int ~cmp:Big_int.eq_big_int
    ~msg:"square-4-limb"
    Big_int_Infix.(mod_big_int (xval *! xval) pval)
    Big_int_Infix.(mod_big_int zval pval)

(* --------------------------------------------------------------------- *)
(* Test suite *)
let tests =
  let open Big_int in
  let m = Big_int_Infix.((2^! 256) -! (big_int_of_int 1)) in
  let one = big_int_of_int 1 in
  [ (* addition *)
    "add 4-limb: 1 + 1" >:: t_add_4limb one one;
    "add 4-limb: p + p" >:: t_add_4limb pval pval;
    "add 4-limb: m + 1" >:: t_add_4limb m one;
    "add 4-limb: m + p" >:: t_add_4limb m pval;
    "add 4-limb: m + m" >:: t_add_4limb m m;

    (* multiplication *)
    "mul 4-limb: 1 * 1" >:: t_mul_4limb one one;
    "mul 4-limb: p * p" >:: t_mul_4limb pval pval;
    "mul 4-limb: m * 1" >:: t_mul_4limb m one;
    "mul 4-limb: m * p" >:: t_mul_4limb m pval;
    "mul 4-limb: m + m" >:: t_mul_4limb m m;

    (* subtraction *)
    "sub 4-limb: 1 - 1" >:: t_sub_4limb one one;
    "sub 4-limb: p - p" >:: t_sub_4limb pval pval;
    "sub 4-limb: m - 1" >:: t_sub_4limb m one;
    "sub 4-limb: m - 1" >:: t_sub_4limb one m;
    "sub 4-limb: m - p" >:: t_sub_4limb m pval;
    "sub 4-limb: p - m" >:: t_sub_4limb pval m;
    "sub 4-limb: m - m" >:: t_sub_4limb m m;

    (* squaring *)
    (* subtraction *)
    "square 4-limb: 1" >:: t_square_4limb one;
    "square 4-limb: p" >:: t_square_4limb pval;
    "square 4-limb: m" >:: t_square_4limb m;
  ]
