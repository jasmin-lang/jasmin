(* * Functional tests for input files *)

(* ** Imports and Abbreviations*)
open Core_kernel.Std
open OUnit
open IL
open Arith
open Util

module F  = Format
module PU = ParserUtil
module C  = Ctypes
module CF = Foreign

(* * Utility functions
 * --------------------------------------------------------------------- *)

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

let get_fun lib fun_name ty =
  try
    CF.(foreign ~from:lib fun_name ty)
  with
    _ -> (* try with prepended underscore, for Linux *)
    CF.(foreign ~from:lib ("_"^fun_name) ty)

(* * Tests for register allocation
 * --------------------------------------------------------------------- *)

let add_il3 = In_channel.read_all "examples/test/register-alloc2.mil"

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
    (In_channel.read_all "examples/test/register-alloc3.mil")

(* * Tests for arithmetic functions: 4 limbs via ASM
 * --------------------------------------------------------------------- *)

let pval = Big_int_Infix.((2 ^! 255) -! (big_int_of_int 19))

let t_via_asm_4limb_binop file fun_name desc expected xval yval () =
  let trafo =
    "expand[n=3],"
    ^"ssa,strip_comments,"
    ^"register_allocate[15],"
  in
  let il_string = In_channel.read_all file in
  let asm_code = il_to_asm_string trafo il_string in
  let (lib,fn_lib) = create_library asm_code in
  let open Ctypes in
  let module U64 = Unsigned.UInt64 in
  let cfun =
    get_fun lib fun_name
      (ptr uint64_t @-> ptr uint64_t @-> ptr uint64_t @-> (returning void))
  in
  let z = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let x = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let y = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let (x0,x1,x2,x3) = Limb4.of_big_int xval in
  let (y0,y1,y2,y3) = Limb4.of_big_int yval in
  CArray.set x 0 x0; CArray.set x 1 x1; CArray.set x 2 x2; CArray.set x 3 x3;
  CArray.set y 0 y0; CArray.set y 1 y1; CArray.set y 2 y2; CArray.set y 3 y3;
  let () = cfun (CArray.start z) (CArray.start x) (CArray.start y) in
  
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

let t_via_asm_4limb_unop file fun_name desc expected xval () =
  let trafo =
    "expand[n=3],"
    ^"ssa,strip_comments,"
    ^"register_allocate[15],"
  in
  let il_string = In_channel.read_all file in
  let asm_code = il_to_asm_string trafo il_string in
  let (lib,fn_lib) = create_library asm_code in
  let open Ctypes in
  let module U64 = Unsigned.UInt64 in
  let cfun =
    get_fun lib fun_name
      (ptr uint64_t @-> ptr uint64_t @-> (returning void))
  in
  let z = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let x = CArray.make uint64_t ~initial:(U64.of_int 0) 4 in
  let (x0,x1,x2,x3) = Limb4.of_big_int xval in
  CArray.set x 0 x0; CArray.set x 1 x1; CArray.set x 2 x2; CArray.set x 3 x3;
  let () = cfun (CArray.start z) (CArray.start x) in
  
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

(* * Tests for arithmetic functions: 4 limbs interpreted
 * --------------------------------------------------------------------- *)

let t_interp_4limb_binop file _fun_name desc expected xval yval () =
  let (x0,x1,x2,x3) = Limb4.of_big_int xval in
  let (y0,y1,y2,y3) = Limb4.of_big_int yval in
  let mem =
    U64.Map.of_alist_exn
      [ (* xp *)
        (U64.of_int  0, x0)
      ; (U64.of_int  8, x1)
      ; (U64.of_int 16, x2)
      ; (U64.of_int 24, x3)
      (* yp *)
      ; (U64.of_int 32, y0)
      ; (U64.of_int 40, y1)
      ; (U64.of_int 48, y2)
      ; (U64.of_int 56, y3)
      ]
  in
  let args = [ U64.of_int 64; U64.of_int 0 ; U64.of_int 32 ] in
  let inp = In_channel.read_all file in
  let open ILL in
  let open ILI in
  let ms = interp_string mem args inp in
  let offset i = Cconst (Int64.of_int i) in
  let mem i = Smem(("zp",[]),offset i) in
  let z0 = read_src ms (mem 0) in
  let z1 = read_src ms (mem 8) in
  let z2 = read_src ms (mem 16) in
  let z3 = read_src ms (mem 24) in
  let zval = Limb4.to_big_int (z0,z1,z2,z3) in
  (*
  F.printf "got: %a = (%a, %a, %a, %a)\n"
    pp_big_int zval pp_uint64 z0 pp_uint64 z1 pp_uint64 z2 pp_uint64 z3;
  *)
  assert_equal ~printer:Big_int.string_of_big_int ~cmp:Big_int.eq_big_int
    ~msg:desc
    Big_int_Infix.(mod_big_int expected pval)
    Big_int_Infix.(mod_big_int zval pval)  


let t_interp_4limb_unop file _fun_name desc expected xval () =
  let (x0,x1,x2,x3) = Limb4.of_big_int xval in
  let mem =
    U64.Map.of_alist_exn
      [ (* xp *)
        (U64.of_int  0, x0)
      ; (U64.of_int  8, x1)
      ; (U64.of_int 16, x2)
      ; (U64.of_int 24, x3)
      ]
  in
  let args = [ U64.of_int 32; U64.of_int 0 ] in
  let inp = In_channel.read_all file in
  let open ILL in
  let open ILI in
  let ms = interp_string mem args inp in
  let offset i = Cconst (Int64.of_int i) in
  let mem i = Smem(("zp",[]),offset i) in
  let z0 = read_src ms (mem 0) in
  let z1 = read_src ms (mem 8) in
  let z2 = read_src ms (mem 16) in
  let z3 = read_src ms (mem 24) in
  let zval = Limb4.to_big_int (z0,z1,z2,z3) in
  (*
  F.printf "got: %a = (%a, %a, %a, %a)\n"
    pp_big_int zval pp_uint64 z0 pp_uint64 z1 pp_uint64 z2 pp_uint64 z3;
  *)
  assert_equal ~printer:Big_int.string_of_big_int ~cmp:Big_int.eq_big_int
    ~msg:desc
    Big_int_Infix.(mod_big_int expected pval)
    Big_int_Infix.(mod_big_int zval pval)  

(* * Generic tests 4 limbs
 * --------------------------------------------------------------------- *)

let t_add_4limb t_asm_or_interp xval yval () =
  t_asm_or_interp
    "examples/25519-4limb/add.mil"
    "add"
    "add-4-limb"
    Big_int_Infix.(xval +! yval)
    xval
    yval
    ()

let t_mul_4limb t_asm_or_interp xval yval () =
  t_asm_or_interp
    "examples/25519-4limb/mul.mil"
    "mul"
    "mul-4-limb"
    Big_int_Infix.(xval *! yval)
    xval yval ()

let t_sub_4limb t_asm_or_interp xval yval () =
  t_asm_or_interp
    "examples/25519-4limb/sub.mil"
    "sub"
    "sub-4-limb"
    Big_int_Infix.(xval -! yval)
    xval yval ()


let t_square_4limb t_asm_or_interp xval () =
  t_asm_or_interp
    "examples/25519-4limb/square.mil"
    "square"
    "square-4-limb"
    Big_int_Infix.(xval *! xval)
    xval ()


(* * Test suite
 * --------------------------------------------------------------------- *)

let tests =
  let open Big_int in
  let m = Big_int_Infix.((2^! 256) -! (big_int_of_int 1)) in
  let one = big_int_of_int 1 in
  let tests s t_binop t_unop =
    [ (* addition *)
      "add 4-limb: 1 + 1 "^s >:: t_add_4limb t_binop one one;
      "add 4-limb: p + p "^s >:: t_add_4limb t_binop pval pval;
      "add 4-limb: m + 1 "^s >:: t_add_4limb t_binop m one;
      "add 4-limb: m + p "^s >:: t_add_4limb t_binop m pval;
      "add 4-limb: m + m "^s >:: t_add_4limb t_binop m m;
      
      (* multiplication *)
      "mul 4-limb: 1 * 1 "^s >:: t_mul_4limb t_binop one one;
      "mul 4-limb: p * p "^s >:: t_mul_4limb t_binop pval pval;
      "mul 4-limb: m * 1 "^s >:: t_mul_4limb t_binop m one;
      "mul 4-limb: m * p "^s >:: t_mul_4limb t_binop m pval;
      "mul 4-limb: m * m "^s >:: t_mul_4limb t_binop m m;

      (* subtraction *)
      "sub 4-limb: 1 - 1 "^s >:: t_sub_4limb t_binop one one;
      "sub 4-limb: p - p "^s >:: t_sub_4limb t_binop pval pval;
      "sub 4-limb: m - 1 "^s >:: t_sub_4limb t_binop m one;
      "sub 4-limb: m - 1 "^s >:: t_sub_4limb t_binop one m;
      "sub 4-limb: m - p "^s >:: t_sub_4limb t_binop m pval;
      "sub 4-limb: p - m "^s >:: t_sub_4limb t_binop pval m;
      "sub 4-limb: m - m "^s >:: t_sub_4limb t_binop m m;
      
      (* squaring *)
      "square 4-limb: 1" >:: t_square_4limb t_unop one;
      "square 4-limb: p" >:: t_square_4limb t_unop pval;
      "square 4-limb: p" >:: t_square_4limb t_unop (Big_int.pred_big_int pval);
      "square 4-limb: m" >:: t_square_4limb t_unop m;
    ]
  in
  (* (tests "(via asm)"     t_via_asm_4limb_binop t_via_asm_4limb_unop) @ *)
  (tests "(interpreter)" t_interp_4limb_binop t_interp_4limb_unop)
