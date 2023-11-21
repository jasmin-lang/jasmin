(* -------------------------------------------------------------------- *)
module J = Jasmin

(* We want to print isolated instructions *)
module type Core_arch' = sig
  include J.Arch_full.Core_arch
  val pp_instr :
    Format.formatter ->
    (reg, regx, xreg, rflag, cond, asm_op) J.Arch_decl.asm_i ->
    unit
end

module type Arch' = sig
  include J.Arch_full.Arch
  val pp_instr :
    Format.formatter ->
    (reg, regx, xreg, rflag, cond, asm_op) J.Arch_decl.asm_i ->
    unit
end

module Arch_from_Core_arch' (A : Core_arch') :
  Arch'
    with type reg = A.reg
     and type regx = A.regx
     and type xreg = A.xreg
     and type rflag = A.rflag
     and type cond = A.cond
     and type asm_op = A.asm_op
     and type extra_op = A.extra_op = struct
  include A
  include J.Arch_full.Arch_from_Core_arch (A)
end

module Impl (A : Arch') = struct

  open Jasmin

  type int256 = int64 * int64 * int64 * int64;;
  let int256_to_z = fun (v : int256) ->
    let (a, b, c, d) = v in
    let p = Z.of_int64_unsigned(d) in
    let q = Z.of_int64_unsigned(c) in
    let r = Z.of_int64_unsigned(b) in
    let s = Z.of_int64_unsigned(a) in
    let result = Z.add (Z.add (Z.shift_left p 192) (Z.shift_left q 128)) (Z.add (Z.shift_left r 64) (Z.shift_left s 0)) in
    result

  let z_to_int256 = fun  (v : Z.t) ->
    let bitmask64 = 0xFFFFFFFFFFFFFFFFL in
    let a = Z.to_int64_unsigned (Z.logand (Z.shift_right v 192) (Z.of_int64_unsigned bitmask64)) in
    let b = Z.to_int64_unsigned (Z.logand (Z.shift_right v 128) (Z.of_int64_unsigned bitmask64)) in
    let c = Z.to_int64_unsigned (Z.logand (Z.shift_right v 64) (Z.of_int64_unsigned bitmask64)) in
    let d = Z.to_int64_unsigned (Z.logand (Z.shift_right v 0) (Z.of_int64_unsigned bitmask64)) in
    ( d, c, b, a)

  let init_memory =
    match Evaluator.initial_memory A.reg_size (Z.of_int 1024) [] with
    | Utils0.Error _err -> assert false
    | Utils0.Ok m -> m

  let init_state ip reg_pairs flag_pairs fn i =
    Exec.mk_asm_state Syscall_ocaml.sc_sem A.asm_e._asm (Syscall_ocaml.initial_state ()) init_memory
      ip reg_pairs flag_pairs fn i

  let exec_instr call_conv asm_state i =
    let dummy_asmscsem = fun _ _ -> assert false in
    match Exec.exec_i Syscall_ocaml.sc_sem A.asm_e._asm call_conv dummy_asmscsem asm_state i with
    | Utils0.Ok state -> state
    | Utils0.Error _ -> failwith "execution failed!"

  let parse_op (op:string) =
    let id = Location.mk_loc Location._dummy op in
    let op = Pretyping.tt_prim (Arch_extra.asm_opI A.asm_e) id in
    match op with
    | BaseOp (_, op) -> op
    | ExtOp _ -> failwith "extop"

  let arch_decl = A.asm_e._asm._arch_decl

  let parse_arg =
    let reg_names =
      List.map
        (fun r -> (Conv.string_of_cstring (arch_decl.toS_r.to_string r), r))
        arch_decl.toS_r._finC.cenum
    in
    let regx_names =
      List.map
        (fun r -> (Conv.string_of_cstring (arch_decl.toS_rx.to_string r), r))
        arch_decl.toS_rx._finC.cenum
    in
    let xreg_names =
      List.map
        (fun r -> (Conv.string_of_cstring (arch_decl.toS_x.to_string r), r))
        arch_decl.toS_x._finC.cenum
    in
    let cond_names =
      List.map
        (fun c -> (Conv.string_of_cstring (arch_decl.toS_c.to_string c), c))
        arch_decl.toS_c._finC.cenum
    in
    fun arg ->
      try
        Arch_decl.Reg (List.assoc arg reg_names)
      with Not_found ->
      try
        Arch_decl.Regx (List.assoc arg regx_names)
      with Not_found ->
      try
        Arch_decl.XReg (List.assoc arg xreg_names)
      with Not_found ->
        try
          Arch_decl.Condt (List.assoc arg cond_names)
      with Not_found ->
        try
          Arch_decl.Imm (U8, Word0.wrepr U8 (Conv.cz_of_z (Z.of_string arg)))
      with Not_found -> Format.eprintf "\"%s\" is not a valid asm_arg.@." arg; exit 1

  let pp_rflagv fmt r =
    let open Arch_decl in
    match r with
    | Def b -> Format.fprintf fmt "%b" b
    | Undef -> Format.fprintf fmt "undef"

  let pp_ip fmt asm_state =
    Format.fprintf fmt "ip: %d" (Conv.int_of_nat (Exec.read_ip Syscall_ocaml.sc_sem A.asm_e._asm asm_state))

  let pp_regs fmt asm_state =
    List.iter (fun r ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (arch_decl.toS_r.to_string r)
        Z.pp_print (Conv.z_of_cz (Exec.read_reg Syscall_ocaml.sc_sem A.asm_e._asm asm_state r)))
      arch_decl.toS_r._finC.cenum

  let pp_regxs fmt asm_state =
    List.iter (fun rx ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (arch_decl.toS_rx.to_string rx)
        Z.pp_print (Conv.z_of_cz (Exec.read_regx Syscall_ocaml.sc_sem A.asm_e._asm asm_state rx)))
      arch_decl.toS_rx._finC.cenum

  let pp_xregs fmt asm_state =
    List.iter (fun rx ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (arch_decl.toS_x.to_string rx)
        Z.pp_print (Conv.z_of_cz (Exec.read_xreg Syscall_ocaml.sc_sem A.asm_e._asm asm_state rx)))
      arch_decl.toS_x._finC.cenum

  let pp_flags fmt asm_state =
    List.iter (fun f ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (arch_decl.toS_f.to_string f)
        pp_rflagv (Exec.read_flag Syscall_ocaml.sc_sem A.asm_e._asm asm_state f))
      arch_decl.toS_f._finC.cenum

  let pp_asm_state fmt asm_state =
    Format.fprintf fmt "@[<v>%a@;%a%a%a%a@]"
      pp_ip asm_state
      pp_regs asm_state
      pp_regxs asm_state
      pp_xregs asm_state
      pp_flags asm_state

  let regs_of_val l =
    List.map2 (fun r v -> (arch_decl.toS_r.to_string r, J.Conv.cz_of_z (Z.of_int32_unsigned v))) arch_decl.toS_r._finC.cenum l
  let regxs_of_val l =
    List.map2 (fun r v -> (arch_decl.toS_rx.to_string r, J.Conv.cz_of_z (Z.of_int32_unsigned v))) arch_decl.toS_rx._finC.cenum l
  let xregs_of_val l =
    List.map2 (fun r v -> (arch_decl.toS_x.to_string r, J.Conv.cz_of_z (Z.of_int64_unsigned v))) arch_decl.toS_x._finC.cenum l
  let flags_of_val l =
    List.map2 (fun f v -> (arch_decl.toS_f.to_string f, v)) arch_decl.toS_f._finC.cenum l

let parse_and_exec op args regs regxs xregs flags =
(*  let module A =
    Arch_from_Core_arch'
      ((val match arch with
            | Amd64 ->
                (module (struct include (val J.CoreArchFactory.core_arch_x86 ~use_lea:false
                               ~use_set0:false call_conv) let pp_instr = J.Ppasm.pp_instr "name" end)
                : Core_arch')
            | CortexM ->
                (module struct include J.CoreArchFactory.Core_arch_ARM let pp_instr = J.Pp_arm_m4.print_instr "name" end : Core_arch'))) in
  let module Impl = Impl(A) in
  (* we need to sync with glob_options for [tt_prim] to work, this is ugly *)
  begin match arch with
  | CortexM -> J.Glob_options.target_arch := ARM_M4
  | _ -> ()
  end; *)

  let reg_values =
      try
        let l1 = regs_of_val regs in
        let l2 = regxs_of_val regxs in
        let l3 = xregs_of_val xregs in
        l1 @ l2 @ l3
      with Invalid_argument _ -> Format.eprintf "Not the right number of regs/regxs/xregs.@."; exit 1
  in

  let flag_values =
      try
        flags_of_val flags
      with Invalid_argument _ -> Format.eprintf "Not the right number of flags.@."; exit 1
  in

  let ip = J.Conv.nat_of_int 0 in
  let op = parse_op op in
  let args = List.map parse_arg args in
  let i = J.Arch_decl.AsmOp (op, args) in
  let fn = J.Prog.F.mk "f" in

  let asm_state = init_state ip reg_values flag_values fn i in
  Format.printf "Initial state:@;%a@." pp_asm_state asm_state;
  Format.printf "@[<v>Running instruction:@;%a@;@]@." A.pp_instr i;
  let asm_state' = exec_instr A.call_conv asm_state i in
  Format.printf "New state:@;%a@." pp_asm_state asm_state';
  asm_state'
end

type arch = Amd64 | CortexM

module A =
  Arch_from_Core_arch'
    (struct
      include J.CoreArchFactory.Core_arch_ARM
      let pp_instr = J.Pp_arm_m4.print_instr "name"
    end)
module ImplA = Impl(A)

let parse_and_exec arch call_conv op args regs regxs xregs flags =
  (* we need to sync with glob_options for [tt_prim] to work, this is ugly *)
  begin match arch with
  | CortexM -> J.Glob_options.target_arch := ARM_M4
  | _ -> ()
  end;
  ImplA.parse_and_exec op args regs regxs xregs flags

open Ctypes
open Foreign

type asm_state
let asm_state : asm_state structure typ = structure "asm_state"
let r0     = field asm_state "r0" int32_t
let r1     = field asm_state "r1" int32_t
let r2     = field asm_state "r2" int32_t
let r3     = field asm_state "r3" int32_t
let r4     = field asm_state "r4" int32_t
let r5     = field asm_state "r5" int32_t
let r6     = field asm_state "r6" int32_t
let r7     = field asm_state "r7" int32_t
let r8      = field asm_state "r8" int32_t
let r9      = field asm_state "r9" int32_t
let r10     = field asm_state "r10" int32_t
let r11     = field asm_state "r11" int32_t
let r12     = field asm_state "r12" int32_t
let lr     = field asm_state "lr" int32_t
let sp     = field asm_state "sp" int32_t

let rflags  = field asm_state "rflags" int32_t

let ()      = seal asm_state

(* let increment_rax = foreign "increment_rax" (ptr asm_state @-> returning void) *)
let set_execute_get = foreign "set_execute_get_wrapper" (ptr asm_state @-> returning void)
(* let set_execute_get_emulator = foreign "set_execute_get_emulator" (ptr asm_state @-> returning void) *)

let op_ref = ref ""
let args_ref = ref []

let is_correct asm_arr =
  let state = make asm_state in
    setf state r0 asm_arr.(0);
    setf state r1 asm_arr.(1);
    setf state r2 asm_arr.(2);
    setf state r3 asm_arr.(3);
    setf state r4 asm_arr.(4);
    setf state r5 asm_arr.(5);
    setf state r6 asm_arr.(6);
    setf state r7 asm_arr.(7);
    setf state r8 asm_arr.(8);
    setf state r9 asm_arr.(9);
    setf state r10 asm_arr.(10);
    setf state r11 asm_arr.(11);
    setf state r12 asm_arr.(12);
    setf state lr asm_arr.(13);
    setf state sp asm_arr.(14);

    setf state rflags asm_arr.(15);

  let check state asm_arr  =
    let arch = CortexM in
    let call_conv = !(J.Glob_options.call_conv) in
    let regs = [asm_arr.(0); asm_arr.(1); asm_arr.(2); asm_arr.(3); asm_arr.(4); asm_arr.(5); asm_arr.(6); asm_arr.(7);
                asm_arr.(8); asm_arr.(9); asm_arr.(10); asm_arr.(11); asm_arr.(12); asm_arr.(13); asm_arr.(14)] in
    let regxs = [] in
    let xregs = [] in
    let flags_ref =
      let open A in
      let num = Z.of_int32_unsigned(asm_arr.(15)) in
      let my_list = ref [] in
      (* NF; ZF; CF; VF *)
      (* the choice of the bits to read comes from hardware constraints, we read in a 32-bit register called APSR
         cf. https://developer.arm.com/documentation/ddi0406/c/Application-Level-Architecture/Application-Level-Programmers--Model/The-Application-Program-Status-Register--APSR-?lang=en *)
      if Z.testbit num 31 then my_list := !my_list @ [J.Arch_decl.Def true] else my_list := !my_list @ [J.Arch_decl.Def false] ;
      if Z.testbit num 30 then my_list := !my_list @ [J.Arch_decl.Def true] else my_list := !my_list @ [J.Arch_decl.Def false] ;
      if Z.testbit num 29 then my_list := !my_list @ [J.Arch_decl.Def true] else my_list := !my_list @ [J.Arch_decl.Def false] ;
      if Z.testbit num 28 then my_list := !my_list @ [J.Arch_decl.Def true] else my_list := !my_list @ [J.Arch_decl.Def false] ;
      my_list
    in
    let flags = !flags_ref in

    set_execute_get (addr state);
    (* set_execute_get_emulator (addr state); *)
    let new_state = parse_and_exec arch call_conv !op_ref !args_ref regs regxs xregs flags in
    (* TODO: do we need jregs? *)
    let jregs: A.reg array = [|R00; R01; R02; R03; R04; R05; R06; R07; R08; R09; R10; R11; R12; LR; SP|] in
    let jasm =
      let jarr = Array.make 15 Z.zero in
      for i = 0 to 14 do
        jarr.(i) <- (J.Conv.z_of_cz (J.Exec.read_reg J.Syscall_ocaml.sc_sem A.asm_e._asm new_state jregs.(i)))
      done;
      jarr
    in
    let cregs = [|r0; r1; r2; r3; r4; r5; r6; r7; r8; r9; r10; r11; r12; lr; sp|] in
    let casm =
      let carr = Array.make 15 Z.zero in
      for i = 0 to 14 do
        carr.(i) <- Z.of_int32_unsigned (getf state cregs.(i))
      done;
      carr
    in

    let result = ref true in
    for i = 0 to 14 do
      (* FIXME: the condition was copied from x86, change it to ignore the right registers *)
      (* Skip checking rsp and rbp values *)
      if i <> 4 && i <> 5 then
      result := !result && (jasm.(i) = casm.(i))
    done;

    (* check xmm registers  *)

    (* Checking the 4 flags  *)
    let j_rflagv_encoding r =
      let open A in
      match r with
      | J.Arch_decl.Def b -> if b = true then 1 else 0
      | J.Arch_decl.Undef -> 2
    in
    let jflags : A.rflag array = [|NF; ZF; CF; VF|] in
    let jflags_vals =
      let temp = Array.make 4 2 in
      for i = 0 to 3 do
        temp.(i) <- j_rflagv_encoding (J.Exec.read_flag J.Syscall_ocaml.sc_sem A.asm_e._asm new_state jflags.(i))
      done;
      temp
    in
    let cflags_vals = Z.of_int32_unsigned(getf state rflags) in

    (* checking NF flag  *)
    if jflags_vals.(0) <> 2 then
      result := !result && (Z.testbit cflags_vals 31 = (jflags_vals.(0) = 1));

    (* checking ZF flag  *)
    if jflags_vals.(1) <> 2 then
      result := !result && (Z.testbit cflags_vals 30 = (jflags_vals.(1) = 1));

    (* checking CF flag  *)
    if jflags_vals.(2) <> 2 then
      result := !result && (Z.testbit cflags_vals 29 = (jflags_vals.(2) = 1));

    (* checking VF flag  *)
    if jflags_vals.(3) <> 2 then
      result := !result && (Z.testbit cflags_vals 28 = (jflags_vals.(3) = 1));

    !result
  in
  Crowbar.check(check state asm_arr)

let () =
  let op_args_file = "op_args.txt" in
  let my_arg_array = Stdlib.Arg.read_arg op_args_file in
  op_ref := my_arg_array.(0);                               (* ADD *)
  if Array.length my_arg_array > 1 then
    args_ref := String.split_on_char ' ' my_arg_array.(1);    (* RAX RBX *)

  let asm_arr =
    let cr0    = Crowbar.int32 in
    let cr1    = Crowbar.int32 in
    let cr2    = Crowbar.int32 in
    let cr3    = Crowbar.int32 in
    let cr4    = Crowbar.int32 in
    let cr5    = Crowbar.int32 in
    let cr6    = Crowbar.int32 in
    let cr7    = Crowbar.int32 in
    let cr8     = Crowbar.int32 in
    let cr9     = Crowbar.int32 in
    let cr10    = Crowbar.int32 in
    let cr11    = Crowbar.int32 in
    let cr12    = Crowbar.int32 in
    let clr    = Crowbar.int32 in
    let csp    = Crowbar.int32 in

    (* let cxmm0_0 = Crowbar.int64 in
    let cxmm0_1 = Crowbar.int64 in
    let cxmm0_2 = Crowbar.int64 in
    let cxmm0_3 = Crowbar.int64 in

    let cxmm1_0 = Crowbar.int64 in
    let cxmm1_1 = Crowbar.int64 in
    let cxmm1_2 = Crowbar.int64 in
    let cxmm1_3 = Crowbar.int64 in

    let cxmm2_0 = Crowbar.int64 in
    let cxmm2_1 = Crowbar.int64 in
    let cxmm2_2 = Crowbar.int64 in
    let cxmm2_3 = Crowbar.int64 in

    let cxmm3_0 = Crowbar.int64 in
    let cxmm3_1 = Crowbar.int64 in
    let cxmm3_2 = Crowbar.int64 in
    let cxmm3_3 = Crowbar.int64 in

    let cxmm4_0 = Crowbar.int64 in
    let cxmm4_1 = Crowbar.int64 in
    let cxmm4_2 = Crowbar.int64 in
    let cxmm4_3 = Crowbar.int64 in

    let cxmm5_0 = Crowbar.int64 in
    let cxmm5_1 = Crowbar.int64 in
    let cxmm5_2 = Crowbar.int64 in
    let cxmm5_3 = Crowbar.int64 in

    let cxmm6_0 = Crowbar.int64 in
    let cxmm6_1 = Crowbar.int64 in
    let cxmm6_2 = Crowbar.int64 in
    let cxmm6_3 = Crowbar.int64 in

    let cxmm7_0 = Crowbar.int64 in
    let cxmm7_1 = Crowbar.int64 in
    let cxmm7_2 = Crowbar.int64 in
    let cxmm7_3 = Crowbar.int64 in

    let cxmm8_0 = Crowbar.int64 in
    let cxmm8_1 = Crowbar.int64 in
    let cxmm8_2 = Crowbar.int64 in
    let cxmm8_3 = Crowbar.int64 in

    let cxmm9_0 = Crowbar.int64 in
    let cxmm9_1 = Crowbar.int64 in
    let cxmm9_2 = Crowbar.int64 in
    let cxmm9_3 = Crowbar.int64 in

    let cxmm10_0 = Crowbar.int64 in
    let cxmm10_1 = Crowbar.int64 in
    let cxmm10_2 = Crowbar.int64 in
    let cxmm10_3 = Crowbar.int64 in

    let cxmm11_0 = Crowbar.int64 in
    let cxmm11_1 = Crowbar.int64 in
    let cxmm11_2 = Crowbar.int64 in
    let cxmm11_3 = Crowbar.int64 in

    let cxmm12_0 = Crowbar.int64 in
    let cxmm12_1 = Crowbar.int64 in
    let cxmm12_2 = Crowbar.int64 in
    let cxmm12_3 = Crowbar.int64 in

    let cxmm13_0 = Crowbar.int64 in
    let cxmm13_1 = Crowbar.int64 in
    let cxmm13_2 = Crowbar.int64 in
    let cxmm13_3 = Crowbar.int64 in

    let cxmm14_0 = Crowbar.int64 in
    let cxmm14_1 = Crowbar.int64 in
    let cxmm14_2 = Crowbar.int64 in
    let cxmm14_3 = Crowbar.int64 in

    let cxmm15_0 = Crowbar.int64 in
    let cxmm15_1 = Crowbar.int64 in
    let cxmm15_2 = Crowbar.int64 in
    let cxmm15_3 = Crowbar.int64 in *)

    (* shifting rflags to last to maintain the struct packing *)
    let crflags = Crowbar.int32 in

    Crowbar.map [
                  cr0;     cr1;     cr2;     cr3;     cr4;     cr5;     cr6;     cr7;
                  cr8;      cr9;      cr10;     cr11;     cr12;     clr;     csp;
                  (* cxmm0_0;  cxmm0_1;  cxmm0_2;  cxmm0_3;  cxmm1_0;  cxmm1_1;  cxmm1_2;  cxmm1_3;
                  cxmm2_0;  cxmm2_1;  cxmm2_2;  cxmm2_3;  cxmm3_0;  cxmm3_1;  cxmm3_2;  cxmm3_3;
                  cxmm4_0;  cxmm4_1;  cxmm4_2;  cxmm4_3;  cxmm5_0;  cxmm5_1;  cxmm5_2;  cxmm5_3;
                  cxmm6_0;  cxmm6_1;  cxmm6_2;  cxmm6_3;  cxmm7_0;  cxmm7_1;  cxmm7_2;  cxmm7_3;
                  cxmm8_0;  cxmm8_1;  cxmm8_2;  cxmm8_3;  cxmm9_0;  cxmm9_1;  cxmm9_2;  cxmm9_3;
                  cxmm10_0; cxmm10_1; cxmm10_2; cxmm10_3; cxmm11_0; cxmm11_1; cxmm11_2; cxmm11_3;
                  cxmm12_0; cxmm12_1; cxmm12_2; cxmm12_3; cxmm13_0; cxmm13_1; cxmm13_2; cxmm13_3;
                  cxmm14_0; cxmm14_1; cxmm14_2; cxmm14_3; cxmm15_0; cxmm15_1; cxmm15_2; cxmm15_3; *)
                  crflags;
                ] (
      fun r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 lr sp
          (* xmm0_0 xmm0_1 xmm0_2 xmm0_3 xmm1_0 xmm1_1 xmm1_2 xmm1_3
          xmm2_0 xmm2_1 xmm2_2 xmm2_3 xmm3_0 xmm3_1 xmm3_2 xmm3_3
          xmm4_0 xmm4_1 xmm4_2 xmm4_3 xmm5_0 xmm5_1 xmm5_2 xmm5_3
          xmm6_0 xmm6_1 xmm6_2 xmm6_3 xmm7_0 xmm7_1 xmm7_2 xmm7_3
          xmm8_0 xmm8_1 xmm8_2 xmm8_3 xmm9_0 xmm9_1 xmm9_2 xmm9_3
          xmm10_0 xmm10_1 xmm10_2 xmm10_3 xmm11_0 xmm11_1 xmm11_2 xmm11_3
          xmm12_0 xmm12_1 xmm12_2 xmm12_3 xmm13_0 xmm13_1 xmm13_2 xmm13_3
          xmm14_0 xmm14_1 xmm14_2 xmm14_3 xmm15_0 xmm15_1 xmm15_2 xmm15_3 *)
          rflags ->
          let my_array = [|r0; r1; r2; r3; r4; r5; r6; r7;
                          r8; r9; r10; r11; r12; lr; sp;
                          r0; r1; r2; r3; r4; r5; r6; r7;
                          r8; r9; r10; r11; r12; lr; sp;
                          r0; r1; r2; r3; r4; r5; r6; r7;
                          r8; r9; r10; r11; r12; lr; sp;
                          r0; r1; r2; r3; r4; r5; r6; r7;
                          r8; r9; r10; r11; r12; lr; sp;
                          r0; r1; r2; r3; r4; r5; r6; r7;
                          r8; r9; r10; r11; r12; lr; sp;
                          (* xmm0_0; xmm0_1; xmm0_2; xmm0_3; xmm1_0; xmm1_1; xmm1_2; xmm1_3;
                          xmm2_0; xmm2_1; xmm2_2; xmm2_3; xmm3_0; xmm3_1; xmm3_2; xmm3_3;
                          xmm4_0; xmm4_1; xmm4_2; xmm4_3; xmm5_0; xmm5_1; xmm5_2; xmm5_3;
                          xmm6_0; xmm6_1; xmm6_2; xmm6_3; xmm7_0; xmm7_1; xmm7_2; xmm7_3;
                          xmm8_0; xmm8_1; xmm8_2; xmm8_3; xmm9_0; xmm9_1; xmm9_2; xmm9_3;
                          xmm10_0; xmm10_1; xmm10_2; xmm10_3; xmm11_0; xmm11_1; xmm11_2; xmm11_3;
                          xmm12_0; xmm12_1; xmm12_2; xmm12_3; xmm13_0; xmm13_1; xmm13_2; xmm13_3;
                          xmm14_0; xmm14_1; xmm14_2; xmm14_3; xmm15_0; xmm15_1; xmm15_2; xmm15_3; *)
                          rflags|] in
        my_array
    )
  in

  Crowbar.add_test ~name:"Differential Testing " [ asm_arr]  (fun asm_arr -> is_correct asm_arr)
