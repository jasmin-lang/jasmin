(* * License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Tests for arithmetic functions *)

open Util
open Arith
open OUnit
open Ctypes
open Foreign

(* * Assembler routines
 * ---------------------------------------------------------------------- *)

let alloc_u64 () =
  allocate uint64_t U64.zero

let u64_of_bool = function true -> U64.one | false -> U64.zero

let bool_of_u64 u =
  if U64.is_one u then true
  else if U64.is_zero u then false
  else failwith ("bool_of_u64: expected 0 or 1, got "^(U64.to_string u))

let op_carry fname (x : u64) (y : u64) (cf : bool) =
  let f_op_carry = 
    foreign fname
      (ptr uint64_t @-> ptr uint64_t @-> uint64_t @-> uint64_t @-> uint64_t
       @-> (returning void))
  in
  let cf_out_ptr = alloc_u64 () in
  let z_out_ptr = alloc_u64 () in
  f_op_carry cf_out_ptr z_out_ptr x y (u64_of_bool cf);
  (!@ z_out_ptr, bool_of_u64 (!@ cf_out_ptr))

module Asm_ref = struct
  let add_carry = op_carry "add_carry"
      
  let sub_carry = op_carry "sub_carry"

  let mul_128 (x : u64) (y : u64) =
    let f_mul_128 = 
      foreign "mul_128"
        (ptr uint64_t @-> ptr uint64_t @-> uint64_t @-> uint64_t @-> (returning void))
    in
    let h_out_ptr = alloc_u64 () in
    let l_out_ptr = alloc_u64 () in
    f_mul_128 h_out_ptr l_out_ptr x y;
    (!@ h_out_ptr, !@ l_out_ptr)

  let imul_trunc (x : u64) (y : u64) =
    let f_imul_trunc = 
      foreign "imul_trunc"
        (ptr uint64_t @-> ptr uint64_t @-> uint64_t @-> uint64_t @-> (returning void))
    in
    let cf_out_ptr = alloc_u64 () in
    let l_out_ptr  = alloc_u64 () in
    f_imul_trunc cf_out_ptr l_out_ptr x y;
    (!@ l_out_ptr, bool_of_u64 (!@ cf_out_ptr))
end

(* * Tests
 * ---------------------------------------------------------------------- *)

let test_u64_binop_cf op1 op2 msg a b cf () =
  assert_equal
    ~printer:(fun (i,cf) -> U64.to_string i^(if cf then " true" else " false"))
    ~cmp:(equal_pair U64.equal (=))
    ~msg
    (op1 a b cf)
    (op2 a b cf)

let test_mul_128 a b () =
  assert_equal
    ~printer:(fun (h,l) -> U64.to_string h^":"^U64.to_string l)
    ~cmp:(equal_pair U64.equal U64.equal)
    ~msg:"mul_128"
    (Asm_ref.mul_128 a b)
    (U64.umul a b)

let test_imul_trunc a b () =
  assert_equal
    ~printer:(fun (l,cf) -> U64.to_string l^(if cf then " true" else " false"))
    ~cmp:(equal_pair U64.equal (=))
    ~msg:"mul_128"
    (Asm_ref.imul_trunc a b)
    (U64.imul_trunc a b)

let tests_U64 =
  let test_sub = test_u64_binop_cf Asm_ref.sub_carry U64.sub_carry "sub-u64" in
  let sub_tests =
    [ "sub-u64[01]" >:: test_sub U64.one     U64.one     true
    ; "sub-u64[02]" >:: test_sub U64.zero    U64.one     true
    ; "sub-u64[03]" >:: test_sub U64.one     U64.one     true
    ; "sub-u64[04]" >:: test_sub U64.zero    U64.max_val false
    ; "sub-u64[05]" >:: test_sub U64.max_val U64.max_val false
    ; "sub-u64[06]" >:: test_sub U64.max_val U64.max_val true
    ; "sub-u64[07]" >:: test_sub U64.one     U64.max_val false
    ; "sub-u64[08]" >:: test_sub U64.one     U64.max_val true
    ; "sub-u64[09]" >:: test_sub U64.max_val U64.one     false
    ; "sub-u64[10]" >:: test_sub U64.max_val U64.one     true
    ; "sub-u64[11]" >:: test_sub (U64.sub U64.max_val U64.one) U64.max_val false
    ; "sub-u64[12]" >:: test_sub (U64.sub U64.max_val U64.one) U64.max_val true
    ]
  in
  let test_add = test_u64_binop_cf Asm_ref.add_carry U64.add_carry "add-u64" in
  let add_tests =
    [ "add-u64[01]" >:: test_add U64.one     U64.one     true
    ; "add-u64[02]" >:: test_add U64.zero    U64.one     true
    ; "add-u64[03]" >:: test_add U64.one     U64.one     true
    ; "add-u64[04]" >:: test_add U64.zero    U64.max_val false
    ; "add-u64[05]" >:: test_add U64.max_val U64.max_val false
    ; "add-u64[06]" >:: test_add U64.max_val U64.max_val true
    ; "add-u64[07]" >:: test_add U64.one     U64.max_val false
    ; "add-u64[08]" >:: test_add U64.one     U64.max_val true
    ; "add-u64[09]" >:: test_add U64.max_val U64.one     false
    ; "add-u64[10]" >:: test_add U64.max_val U64.one     true
    ; "add-u64[11]" >:: test_add (U64.sub U64.max_val U64.one) U64.max_val false
    ; "add-u64[12]" >:: test_add (U64.sub U64.max_val U64.one) U64.max_val true
    ; "add-u64[13]" >:: test_add (U64.sub U64.max_val U64.one) U64.one false
    ; "add-u64[14]" >:: test_add (U64.sub U64.max_val U64.one) U64.one true
    ]
  in
  let mul_128_tests =
    [ "mul-128[01]" >:: test_mul_128 U64.one     U64.one
    ; "mul-128[02]" >:: test_mul_128 U64.zero    U64.one
    ; "mul-128[03]" >:: test_mul_128 U64.one     U64.one
    ; "mul-128[04]" >:: test_mul_128 U64.zero    U64.max_val
    ; "mul-128[05]" >:: test_mul_128 U64.max_val U64.max_val
    ; "mul-128[06]" >:: test_mul_128 U64.max_val U64.max_val
    ; "mul-128[07]" >:: test_mul_128 U64.one     U64.max_val
    ; "mul-128[08]" >:: test_mul_128 U64.one     U64.max_val
    ; "mul-128[09]" >:: test_mul_128 U64.max_val U64.one
    ; "mul-128[10]" >:: test_mul_128 U64.max_val U64.one
    ; "mul-128[11]" >:: test_mul_128 (U64.sub U64.max_val U64.one) U64.max_val
    ; "mul-128[12]" >:: test_mul_128 (U64.sub U64.max_val U64.one) U64.max_val
    ; "mul-128[13]" >:: test_mul_128 (U64.sub U64.max_val U64.one) U64.one
    ; "mul-128[14]" >:: test_mul_128 (U64.sub U64.max_val U64.one) U64.one
    ; "mul-128[15]" >:: test_mul_128 U64.zero U64.zero
    ; "mul-128[16]" >:: test_mul_128 U64.one U64.zero
    ; "mul-128[17]" >:: test_mul_128 U64.one U64.one
    ; "mul-128[18]" >:: test_mul_128 (U64.of_int 2) (U64.of_int 2)
    ; "mul-128[19]" >:: test_mul_128 U64.max_val (U64.of_int 2)
    ]
  in
  let imul_trunc_tests =
    [ "imul-trunc[01]" >:: test_imul_trunc U64.one     U64.one
    ; "imul-trunc[02]" >:: test_imul_trunc U64.zero    U64.one
    ; "imul-trunc[03]" >:: test_imul_trunc U64.one     U64.one
    ; "imul-trunc[04]" >:: test_imul_trunc U64.zero    U64.max_val
    ; "imul-trunc[05]" >:: test_imul_trunc U64.max_val U64.max_val
    ; "imul-trunc[06]" >:: test_imul_trunc U64.max_val U64.max_val
    ; "imul-trunc[07]" >:: test_imul_trunc U64.one     U64.max_val
    ; "imul-trunc[08]" >:: test_imul_trunc U64.one     U64.max_val
    ; "imul-trunc[09]" >:: test_imul_trunc U64.max_val U64.one
    ; "imul-trunc[10]" >:: test_imul_trunc U64.max_val U64.one
    ; "imul-trunc[11]" >:: test_imul_trunc (U64.sub U64.max_val U64.one) U64.max_val
    ; "imul-trunc[12]" >:: test_imul_trunc (U64.sub U64.max_val U64.one) U64.max_val
    ; "imul-trunc[13]" >:: test_imul_trunc (U64.sub U64.max_val U64.one) U64.one
    ; "imul-trunc[14]" >:: test_imul_trunc (U64.sub U64.max_val U64.one) U64.one
    ; "imul-trunc[15]" >:: test_imul_trunc U64.zero U64.zero
    ; "imul-trunc[16]" >:: test_imul_trunc U64.one U64.zero
    ; "imul-trunc[17]" >:: test_imul_trunc U64.one U64.one
    ; "imul-trunc[18]" >:: test_imul_trunc (U64.of_int 2) (U64.of_int 2)
    ; "imul-trunc[19]" >:: test_imul_trunc U64.max_val (U64.of_int 2)
    ; "imul-trunc[20]" >:: test_imul_trunc U64.zero (U64.of_int 38)
    ; "imul-trunc[21]" >:: test_imul_trunc U64.one (U64.of_int 38)
    ; "imul-trunc[22]" >:: test_imul_trunc U64.max_val (U64.of_int 38)
    ; "imul-trunc[23]" >:: test_imul_trunc (U64.of_string "0x7fffffffffffffff") (U64.of_int 2)
    ; "imul-trunc[24]" >:: test_imul_trunc (U64.of_string "0x8000000000000000") (U64.of_int 2)
    ; "imul-trunc[25]" >:: test_imul_trunc (U64.of_string "0x8000000000000001") (U64.of_int 2)
    ]
  in
  sub_tests @ add_tests @ mul_128_tests @ imul_trunc_tests
