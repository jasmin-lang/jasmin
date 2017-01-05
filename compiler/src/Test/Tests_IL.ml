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
    | [f] -> ILTy.typecheck_efun String.Map.empty f; f
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
    | [f] -> ILTy.typecheck_efun String.Map.empty f; f
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

let t_reg3 () =
  let trafo =
    "print[orig],expand[n=4],print[expand],"
    ^"ssa,print[ssa],"
    ^"equal_dest_src,print[equal_dest_src],strip_comments,"
    ^"register_liveness,print[liveness],strip_comments,"
    ^"register_allocate[15]"
  in
  let il_string = In_channel.read_all "examples/add-4limb.mil" in
  let il_code = il_to_il_string trafo il_string in  
  print_endline il_code

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

let t_interp_4limb_binop file fun_name desc expected xval yval () =
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
  let cvar_map = String.Map.of_alist_exn [("n",U64.of_int 4)] in
  let ms = interp_string file mem cvar_map args fun_name inp in
  let offset i = Pconst (U64.of_int i) in
  let mem i =
    Src({ d_pr = mk_preg_name "zp"; d_aidxs = [offset i]})
  in
  let z0 = read_src ms (mem 0) in
  let z1 = read_src ms (mem 1) in
  let z2 = read_src ms (mem 2) in
  let z3 = read_src ms (mem 3) in
  let zval = Limb4.to_big_int (z0,z1,z2,z3) in
  (*
  F.printf "got: %a = (%a, %a, %a, %a)\n"
    pp_big_int zval pp_uint64 z0 pp_uint64 z1 pp_uint64 z2 pp_uint64 z3;
  *)
  assert_equal ~printer:Big_int.string_of_big_int ~cmp:Big_int.eq_big_int
    ~msg:desc
    Big_int_Infix.(mod_big_int expected pval)
    Big_int_Infix.(mod_big_int zval pval)  

let t_interp_4limb_unop file fun_name desc expected xval () =
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
  let cvar_map = String.Map.of_alist_exn [("n",U64.of_int 4)] in
  let ms = interp_string file mem cvar_map args fun_name inp in
  let offset i = Pconst (U64.of_int i) in
  let mem i =
    Src({d_pr = mk_preg_name "zp"; d_aidxs = [offset i]})
  in
  let z0 = read_src ms (mem 0) in
  let z1 = read_src ms (mem 1) in
  let z2 = read_src ms (mem 2) in
  let z3 = read_src ms (mem 3) in
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

let t_add_call_4limb t_asm_or_interp xval yval () =
  t_asm_or_interp
    "examples/test/add_call.mil"
    "add_call"
    "add_call-4-limb"
    Big_int_Infix.(xval +! yval)
    xval yval ()

let t_interp_4limb_ladder file fun_name desc expected m w0 w1 w2 w3 w4 () =
  let (w0_0,w0_1,w0_2,w0_3) = Limb4.of_big_int w0 in
  let (w1_0,w1_1,w1_2,w1_3) = Limb4.of_big_int w1 in
  let (w2_0,w2_1,w2_2,w2_3) = Limb4.of_big_int w2 in
  let (w3_0,w3_1,w3_2,w3_3) = Limb4.of_big_int w3 in
  let (w4_0,w4_1,w4_2,w4_3) = Limb4.of_big_int w4 in
  let mem =
    U64.Map.of_alist_exn
      [ (* workp0 *)
        (U64.of_int (0*8), w0_0)
      ; (U64.of_int (1*8), w0_1)
      ; (U64.of_int (2*8), w0_2)
      ; (U64.of_int (3*8), w0_3)
      (* workp2 *)
      ; (U64.of_int (32 + 0*8), w1_0)
      ; (U64.of_int (32 + 1*8), w1_1)
      ; (U64.of_int (32 + 2*8), w1_2)
      ; (U64.of_int (32 + 3*8), w1_3)
      (* workp3 *)
      ; (U64.of_int (64 + 0*8), w2_0)
      ; (U64.of_int (64 + 1*8), w2_1)
      ; (U64.of_int (64 + 2*8), w2_2)
      ; (U64.of_int (64 + 3*8), w2_3)
      (* workp4 *)
      ; (U64.of_int (96 + 0*8), w3_0)
      ; (U64.of_int (96 + 1*8), w3_1)
      ; (U64.of_int (96 + 2*8), w3_2)
      ; (U64.of_int (96 + 3*8), w3_3)
      (* workp4 *)
      ; (U64.of_int (128 + 0*8), w4_0)
      ; (U64.of_int (128 + 1*8), w4_1)
      ; (U64.of_int (128 + 2*8), w4_2)
      ; (U64.of_int (128 + 3*8), w4_3)
      ]
  in
  let args = [ U64.of_int 0 ] in
  let inp = In_channel.read_all file in
  let open ILL in
  let open ILI in
  let cvar_map =
    String.Map.of_alist_exn [("n",U64.of_int 4); ("m",U64.of_int m)]
  in
  let ms = interp_string file mem cvar_map args fun_name inp in
  let offset i = Pconst (U64.of_int i) in
  let mem p xs = Src({d_pr = mk_preg_name p; d_aidxs = List.map ~f:offset xs}) in
  let ws =
    List.map
      ~f:(fun p ->
            let w0 = read_src ms (mem "workp" [p;0]) in
            let w1 = read_src ms (mem "workp" [p;1]) in
            let w2 = read_src ms (mem "workp" [p;2]) in
            let w3 = read_src ms (mem "workp" [p;3]) in
            Big_int.mod_big_int (Limb4.to_big_int (w0,w1,w2,w3)) pval)
      [ 0; 1; 2; 3; 4 ]
  in
  (*
  F.printf "got: %a = (%a, %a, %a, %a)\n"
    pp_big_int zval pp_uint64 z0 pp_uint64 z1 pp_uint64 z2 pp_uint64 z3;
  *)
  assert_equal
    ~printer:(fun xs ->
                fsprintf "%a" (pp_list "\n" pp_string) (List.map ~f:Big_int.string_of_big_int xs))
    ~cmp:(equal_list (fun x y -> Big_int_Infix.(x === y)))
    ~msg:desc
    (List.map ~f:(fun i -> Big_int_Infix.(mod_big_int i pval))
       expected)
    ws

let ladderstep x1 x2 z2 x3 z3 =
  let (+&)   x y = Big_int_Infix.(mod_big_int (x +! y) pval) in
  let (-&)   x y = Big_int_Infix.(mod_big_int (x -! y) pval) in
  let ( *& ) x y = Big_int_Infix.(mod_big_int (x *! y) pval) in
  let c121666 = Big_int.big_int_of_string "121666" in
  let t1 = x2 +& z2 in
  let t2 = x2 -& z2 in
  let t7 = t2 *& t2 in
  let t6 = t1 *& t1 in
  let t5 = t6 -& t7 in
  let t3 = x3 +& z3 in
  let t4 = x3 -& z3 in
  let t9 = t3 *& t2 in
  let t8 = t4 *& t1 in
  let x3 = t8 +& t9 in
  let z3 = t8 -& t9 in
  let x3 = x3 *& x3 in
  let z3 = z3 *& z3 in
  let z3 = z3 *& x1 in
  let x2 = t6 *& t7 in
  let z2 = c121666 *& t5 in
  let z2 = z2 +& t7 in
  let z2 = z2 *& t5 in
  [x1;x2;z2;x3;z3]

let ladderstep_n n =
  let rec go i x1 x2 z2 x3 z3 =
    if i < n then (
      match ladderstep x1 x2 z2 x3 z3 with
      | [x1;x2;z2;x3;z3] -> go (i + 1) x1 x2 z2 x3 z3
      | _ -> assert false
    ) else (
      [x1;x2;z2;x3;z3]
    )
  in
  go 0
    

(* * Test suite
 * --------------------------------------------------------------------- *)

let tests =
  let open Big_int in
  let m = Big_int_Infix.((2^! 256) -! (big_int_of_int 1)) in
  let one = big_int_of_int 1 in
  let tests s _t_binop t_unop =
    [ (* addition *)
      (* "add 4-limb: 1 + 1 "^s >:: t_add_4limb t_binop one one; *)
      (* "add 4-limb: p + p "^s >:: t_add_4limb t_binop pval pval; *)
      (* "add 4-limb: m + 1 "^s >:: t_add_4limb t_binop m one; *)
      (* "add 4-limb: m + p "^s >:: t_add_4limb t_binop m pval; *)
      (* "add 4-limb: m + m "^s >:: t_add_4limb t_binop m m; *)
      
      (* (\* multiplication *\) *)
      (* "mul 4-limb: 1 * 1 "^s >:: t_mul_4limb t_binop one one; *)
      (* "mul 4-limb: p * p "^s >:: t_mul_4limb t_binop pval pval; *)
      (* "mul 4-limb: m * 1 "^s >:: t_mul_4limb t_binop m one; *)
      (* "mul 4-limb: m * p "^s >:: t_mul_4limb t_binop m pval; *)
      (* "mul 4-limb: m * m "^s >:: t_mul_4limb t_binop m m; *)

      (* (\* subtraction *\) *)
      (* "sub 4-limb: 1 - 1 "^s >:: t_sub_4limb t_binop one one; *)
      (* "sub 4-limb: p - p "^s >:: t_sub_4limb t_binop pval pval; *)
      (* "sub 4-limb: m - 1 "^s >:: t_sub_4limb t_binop m one; *)
      (* "sub 4-limb: m - 1 "^s >:: t_sub_4limb t_binop one m; *)
      (* "sub 4-limb: m - p "^s >:: t_sub_4limb t_binop m pval; *)
      (* "sub 4-limb: p - m "^s >:: t_sub_4limb t_binop pval m; *)
      (* "sub 4-limb: m - m "^s >:: t_sub_4limb t_binop m m; *)
      
      (* squaring *)
      "square 4-limb: 1" >:: t_square_4limb t_unop one;
      "square 4-limb: p" >:: t_square_4limb t_unop pval;
      "square 4-limb: p" >:: t_square_4limb t_unop (Big_int.pred_big_int pval);
      "square 4-limb: m" >:: t_square_4limb t_unop m;
    ] @
    if s = "(interpreter)" then
      [
        (* addition *)
        (* "add call 4-limb: 1 + 1 "^s >:: t_add_call_4limb t_binop one one; *)
        (* "add call 4-limb: p + p "^s >:: t_add_call_4limb t_binop pval pval; *)
        (* "add call 4-limb: m + 1 "^s >:: t_add_call_4limb t_binop m one; *)
        (* "add call 4-limb: m + p "^s >:: t_add_call_4limb t_binop m pval; *)
        (* "add call 4-limb: m + m "^s >:: t_add_call_4limb t_binop m m; *)
      ]
    else []
  in
  let _t_ladder =
    t_interp_4limb_ladder
      "examples/25519-4limb/ladderstep.mil"
      "ladderstep128"
      "ladderstep128-4-limb"
  in
  let _t0 = Big_int.big_int_of_int 42 in
  let _t1 = Big_int.big_int_of_int 9999  in
  let _t2 = Big_int.big_int_of_int 555 in
  let _t3 = Big_int.big_int_of_int 77777 in
  let _t4 = Big_int.big_int_of_int 666666 in
  (* (tests "(via asm)"     t_via_asm_4limb_binop t_via_asm_4limb_unop) @ *)  
  (tests "(interpreter)" t_interp_4limb_binop t_interp_4limb_unop)
  (* @  *)
  (* [ "ladderstep: 1 (interpreter)" >:: *)
  (*   fun () -> *)
  (*     try *)
  (*       let m = 2 in *)
  (*       t_ladder (ladderstep_n m t0 t1 t2 t3 t4) m t0 t1 t2 t3 t4 () *)
  (*     with  *)
  (*     | OUnitTest.OUnit_failure _ as e -> raise e *)
  (*     | e -> *)
  (*       failwith *)
  (*         (F.sprintf "Unexpected error in ladderstep: 1 test: %s,\n%s" *)
  (*            (Exn.to_string e) *)
  (*            (Exn.backtrace ()))  *)
  (* ] *)
