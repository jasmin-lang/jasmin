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
    List.map2 (fun r v -> (arch_decl.toS_r.to_string r, J.Conv.cz_of_z (Z.of_int64_unsigned v))) arch_decl.toS_r._finC.cenum l
  let regxs_of_val l =
    List.map2 (fun r v -> (arch_decl.toS_rx.to_string r, J.Conv.cz_of_z (Z.of_int64_unsigned v))) arch_decl.toS_rx._finC.cenum l
  let xregs_of_val l =
    List.map2 (fun r v -> (arch_decl.toS_x.to_string r, J.Conv.cz_of_z (int256_to_z v))) arch_decl.toS_x._finC.cenum l
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
      (struct include (val J.CoreArchFactory.core_arch_x86 ~use_lea:false
        ~use_set0:false J.Glob_options.Linux) let pp_instr = J.Ppasm.pp_instr "name" end)
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
let rax     = field asm_state "rax" int64_t
let rcx     = field asm_state "rcx" int64_t
let rdx     = field asm_state "rdx" int64_t
let rbx     = field asm_state "rbx" int64_t
let rsp     = field asm_state "rsp" int64_t
let rbp     = field asm_state "rbp" int64_t
let rsi     = field asm_state "rsi" int64_t
let rdi     = field asm_state "rdi" int64_t
let r8      = field asm_state "r8" int64_t
let r9      = field asm_state "r9" int64_t
let r10     = field asm_state "r10" int64_t
let r11     = field asm_state "r11" int64_t
let r12     = field asm_state "r12" int64_t
let r13     = field asm_state "r13" int64_t
let r14     = field asm_state "r14" int64_t
let r15     = field asm_state "r15" int64_t

(* XMM registers.. bad way just looking at 64 bit values *)
let xmm0_0    = field asm_state "xmm0_0" int64_t
let xmm0_1    = field asm_state "xmm0_1" int64_t
let xmm0_2    = field asm_state "xmm0_2" int64_t
let xmm0_3    = field asm_state "xmm0_3" int64_t

let xmm1_0    = field asm_state "xmm1_0" int64_t
let xmm1_1    = field asm_state "xmm1_1" int64_t
let xmm1_2    = field asm_state "xmm1_2" int64_t
let xmm1_3    = field asm_state "xmm1_3" int64_t

let xmm2_0    = field asm_state "xmm2_0" int64_t
let xmm2_1   = field asm_state "xmm2_1" int64_t
let xmm2_2    = field asm_state "xmm2_2" int64_t
let xmm2_3    = field asm_state "xmm2_3" int64_t


let xmm3_0    = field asm_state "xmm3_0" int64_t
let xmm3_1    = field asm_state "xmm3_1" int64_t
let xmm3_2    = field asm_state "xmm3_2" int64_t
let xmm3_3    = field asm_state "xmm3_3" int64_t


let xmm4_0     = field asm_state "xmm4_0" int64_t
let xmm4_1    = field asm_state "xmm4_1" int64_t
let xmm4_2    = field asm_state "xmm4_2" int64_t
let xmm4_3    = field asm_state "xmm4_3" int64_t


let xmm5_0    = field asm_state "xmm5_0" int64_t
let xmm5_1   = field asm_state "xmm5_1" int64_t
let xmm5_2    = field asm_state "xmm5_2" int64_t
let xmm5_3    = field asm_state "xmm5_3" int64_t

let xmm6_0    = field asm_state "xmm6_0" int64_t
let xmm6_1    = field asm_state "xmm6_1" int64_t
let xmm6_2    = field asm_state "xmm6_2" int64_t
let xmm6_3    = field asm_state "xmm6_3" int64_t

let xmm7_0    = field asm_state "xmm7_0" int64_t
let xmm7_1    = field asm_state "xmm7_1" int64_t
let xmm7_2    = field asm_state "xmm7_2" int64_t
let xmm7_3    = field asm_state "xmm7_3" int64_t

let xmm8_0    = field asm_state "xmm8_0" int64_t
let xmm8_1    = field asm_state "xmm8_1" int64_t
let xmm8_2    = field asm_state "xmm8_2" int64_t
let xmm8_3    = field asm_state "xmm8_3" int64_t

let xmm9_0    = field asm_state "xmm9_0" int64_t
let xmm9_1    = field asm_state "xmm9_1" int64_t
let xmm9_2    = field asm_state "xmm9_2" int64_t
let xmm9_3    = field asm_state "xmm9_3" int64_t

let xmm10_0   = field asm_state "xmm10_0" int64_t
let xmm10_1   = field asm_state "xmm10_1" int64_t
let xmm10_2   = field asm_state "xmm10_2" int64_t
let xmm10_3   = field asm_state "xmm10_3" int64_t

let xmm11_0   = field asm_state "xmm11_0" int64_t
let xmm11_1   = field asm_state "xmm11_1" int64_t
let xmm11_2   = field asm_state "xmm11_2" int64_t
let xmm11_3   = field asm_state "xmm11_3" int64_t

let xmm12_0   = field asm_state "xmm12_0" int64_t
let xmm12_1   = field asm_state "xmm12_1" int64_t
let xmm12_2   = field asm_state "xmm12_2" int64_t
let xmm12_3   = field asm_state "xmm12_3" int64_t

let xmm13_0   = field asm_state "xmm13_0" int64_t
let xmm13_1   = field asm_state "xmm13_1" int64_t
let xmm13_2   = field asm_state "xmm13_2" int64_t
let xmm13_3   = field asm_state "xmm13_3" int64_t

let xmm14_0   = field asm_state "xmm14_0" int64_t
let xmm14_1   = field asm_state "xmm14_1" int64_t
let xmm14_2   = field asm_state "xmm14_2" int64_t
let xmm14_3   = field asm_state "xmm14_3" int64_t

let xmm15_0   = field asm_state "xmm15_0" int64_t
let xmm15_1   = field asm_state "xmm15_1" int64_t
let xmm15_2   = field asm_state "xmm15_2" int64_t
let xmm15_3   = field asm_state "xmm15_3" int64_t

let rflags  = field asm_state "rflags" int64_t

let ()      = seal asm_state

(* let increment_rax = foreign "increment_rax" (ptr asm_state @-> returning void) *)
let set_execute_get = foreign "set_execute_get_wrapper" (ptr asm_state @-> returning void)
(* let set_execute_get_emulator = foreign "set_execute_get_emulator" (ptr asm_state @-> returning void) *)

let op_ref = ref ""
let args_ref = ref []

let is_correct asm_arr =
  let state = make asm_state in
    setf state rax asm_arr.(0);
    setf state rcx asm_arr.(1);
    setf state rdx asm_arr.(2);
    setf state rbx asm_arr.(3);
    setf state rsp asm_arr.(4);
    setf state rbp asm_arr.(5);
    setf state rsi asm_arr.(6);
    setf state rdi asm_arr.(7);
    setf state r8 asm_arr.(8);
    setf state r9 asm_arr.(9);
    setf state r10 asm_arr.(10);
    setf state r11 asm_arr.(11);
    setf state r12 asm_arr.(12);
    setf state r13 asm_arr.(13);
    setf state r14 asm_arr.(14);
    setf state r15 asm_arr.(15);

    (* XMM0  *)
    setf state xmm0_0 asm_arr.(16);
    setf state xmm0_1 asm_arr.(17);
    setf state xmm0_2 asm_arr.(18);
    setf state xmm0_3 asm_arr.(19);

    (* XMM1  *)
    setf state xmm1_0 asm_arr.(20);
    setf state xmm1_1 asm_arr.(21);
    setf state xmm1_2 asm_arr.(22);
    setf state xmm1_3 asm_arr.(23);

    (* XMM2  *)
    setf state xmm2_0 asm_arr.(24);
    setf state xmm2_1 asm_arr.(25);
    setf state xmm2_2 asm_arr.(26);
    setf state xmm2_3 asm_arr.(27);

    (* XMM3  *)
    setf state xmm3_0 asm_arr.(28);
    setf state xmm3_1 asm_arr.(29);
    setf state xmm3_2 asm_arr.(30);
    setf state xmm3_3 asm_arr.(31);

    (* XMM4  *)
    setf state xmm4_0 asm_arr.(32);
    setf state xmm4_1 asm_arr.(33);
    setf state xmm4_2 asm_arr.(34);
    setf state xmm4_3 asm_arr.(35);

    (* XMM5  *)
    setf state xmm5_0 asm_arr.(36);
    setf state xmm5_1 asm_arr.(37);
    setf state xmm5_2 asm_arr.(38);
    setf state xmm5_3 asm_arr.(39);

    (* XMM6  *)
    setf state xmm6_0 asm_arr.(40);
    setf state xmm6_1 asm_arr.(41);
    setf state xmm6_2 asm_arr.(42);
    setf state xmm6_3 asm_arr.(43);

    (* XMM7  *)
    setf state xmm7_0 asm_arr.(44);
    setf state xmm7_1 asm_arr.(45);
    setf state xmm7_2 asm_arr.(46);
    setf state xmm7_3 asm_arr.(47);

    (* XMM8  *)
    setf state xmm8_0 asm_arr.(48);
    setf state xmm8_1 asm_arr.(49);
    setf state xmm8_2 asm_arr.(50);
    setf state xmm8_3 asm_arr.(51);

    (* XMM9  *)
    setf state xmm9_0 asm_arr.(52);
    setf state xmm9_1 asm_arr.(53);
    setf state xmm9_2 asm_arr.(54);
    setf state xmm9_3 asm_arr.(55);

    (* XMM10  *)
    setf state xmm10_0 asm_arr.(56);
    setf state xmm10_1 asm_arr.(57);
    setf state xmm10_2 asm_arr.(58);
    setf state xmm10_3 asm_arr.(59);

    (* XMM11  *)
    setf state xmm11_0 asm_arr.(60);
    setf state xmm11_1 asm_arr.(61);
    setf state xmm11_2 asm_arr.(62);
    setf state xmm11_3 asm_arr.(63);

    (* XMM12  *)
    setf state xmm12_0 asm_arr.(64);
    setf state xmm12_1 asm_arr.(65);
    setf state xmm12_2 asm_arr.(66);
    setf state xmm12_3 asm_arr.(67);

    (* XMM13  *)
    setf state xmm13_0 asm_arr.(68);
    setf state xmm13_1 asm_arr.(69);
    setf state xmm13_2 asm_arr.(70);
    setf state xmm13_3 asm_arr.(71);

    (* XMM14  *)
    setf state xmm14_0 asm_arr.(72);
    setf state xmm14_1 asm_arr.(73);
    setf state xmm14_2 asm_arr.(74);
    setf state xmm14_3 asm_arr.(75);

    (* XMM15  *)
    setf state xmm15_0 asm_arr.(76);
    setf state xmm15_1 asm_arr.(77);
    setf state xmm15_2 asm_arr.(78);
    setf state xmm15_3 asm_arr.(79);

    setf state rflags asm_arr.(80);

  let check state asm_arr  =
    let arch = Amd64 in
    let call_conv = !(J.Glob_options.call_conv) in
    let regs = [asm_arr.(0); asm_arr.(1); asm_arr.(2); asm_arr.(3); asm_arr.(4); asm_arr.(5); asm_arr.(6); asm_arr.(7);
                asm_arr.(8); asm_arr.(9); asm_arr.(10); asm_arr.(11); asm_arr.(12); asm_arr.(13); asm_arr.(14); asm_arr.(15)] in
    let regxs = [0L;0L;0L;0L;0L;0L;0L;0L] in
    let xregs = [
                    (asm_arr.(16), asm_arr.(17), asm_arr.(18), asm_arr.(19));
                    (asm_arr.(20), asm_arr.(21), asm_arr.(22), asm_arr.(23));
                    (asm_arr.(24), asm_arr.(25), asm_arr.(26), asm_arr.(27));
                    (asm_arr.(28), asm_arr.(29), asm_arr.(30), asm_arr.(31));
                    (asm_arr.(32), asm_arr.(33), asm_arr.(34), asm_arr.(35));
                    (asm_arr.(36), asm_arr.(37), asm_arr.(38), asm_arr.(39));
                    (asm_arr.(40), asm_arr.(41), asm_arr.(42), asm_arr.(43));
                    (asm_arr.(44), asm_arr.(45), asm_arr.(46), asm_arr.(47));
                    (asm_arr.(48), asm_arr.(49), asm_arr.(50), asm_arr.(51));
                    (asm_arr.(52), asm_arr.(53), asm_arr.(54), asm_arr.(55));
                    (asm_arr.(56), asm_arr.(57), asm_arr.(58), asm_arr.(59));
                    (asm_arr.(60), asm_arr.(61), asm_arr.(62), asm_arr.(63));
                    (asm_arr.(64), asm_arr.(65), asm_arr.(66), asm_arr.(67));
                    (asm_arr.(68), asm_arr.(69), asm_arr.(70), asm_arr.(71));
                    (asm_arr.(72), asm_arr.(73), asm_arr.(74), asm_arr.(75));
                    (asm_arr.(76), asm_arr.(77), asm_arr.(78), asm_arr.(79));
                ] in
    let flags_ref =
      let open A in
      let num = Z.of_int64_unsigned(asm_arr.(80)) in
      let my_list = ref [] in
      (* CF; PF; ZF; SF; OF *)
      if Z.testbit num 0 then my_list := !my_list @ [J.Arch_decl.Def true] else my_list := !my_list @ [J.Arch_decl.Def false] ;
      if Z.testbit num 2 then my_list := !my_list @ [J.Arch_decl.Def true] else my_list := !my_list @ [J.Arch_decl.Def false] ;
      if Z.testbit num 6 then my_list := !my_list @ [J.Arch_decl.Def true] else my_list := !my_list @ [J.Arch_decl.Def false] ;
      if Z.testbit num 7 then my_list := !my_list @ [J.Arch_decl.Def true] else my_list := !my_list @ [J.Arch_decl.Def false] ;
      if Z.testbit num 11 then my_list := !my_list @ [J.Arch_decl.Def true] else my_list := !my_list @ [J.Arch_decl.Def false] ;
      my_list
    in
    let flags = !flags_ref in

    set_execute_get (addr state);
    (* set_execute_get_emulator (addr state); *)
    let new_state = parse_and_exec arch call_conv !op_ref !args_ref regs regxs xregs flags in
    (* TODO: do we need jregs? *)
    let jregs: A.reg array = [|RAX; RCX; RDX; RBX; RSP; RBP; RSI; RDI; R8; R9; R10; R11; R12; R13; R14; R15|] in
    let jasm =
      let jarr = Array.make 16 Z.zero in
      for i = 0 to 15 do
        jarr.(i) <- (J.Conv.z_of_cz (J.Exec.read_reg J.Syscall_ocaml.sc_sem A.asm_e._asm new_state jregs.(i)))
      done;
      jarr
    in
    let cregs = [|rax; rcx; rdx; rbx; rsp; rbp; rsi; rdi; r8; r9; r10; r11; r12; r13; r14; r15|] in
    let casm =
      let carr = Array.make 16 Z.zero in
      for i = 0 to 15 do
        carr.(i) <- Z.of_int64_unsigned (getf state cregs.(i))
      done;
      carr
    in
    (* compare xmm registers  *)
    let jxregs: A.xreg array = [|XMM0; XMM1; XMM2; XMM3; XMM4; XMM5; XMM6; XMM7; XMM8; XMM9; XMM10; XMM11; XMM12; XMM13; XMM14; XMM15|] in
    let jxasm =
      let jxarr = Array.make 16 Z.zero in
      for i = 0 to 15 do
        let temp = J.Conv.z_of_cz (J.Exec.read_xreg J.Syscall_ocaml.sc_sem A.asm_e._asm new_state jxregs.(i)) in
        (* jxarr.(i) <- (J.Conv.z_of_cz (J.Exec.read_xreg J.Syscall_ocaml.sc_sem A.asm_e._asm new_state jxregs.(i))); *)
        jxarr.(i) <- temp;
        (* Printf.printf "The JXasm is %s\n" (Z.to_string jxarr.(i)); *)
      done;
      jxarr
    in
    let cxregs = [|
                    xmm0_0; xmm0_1; xmm0_2; xmm0_3;
                    xmm1_0; xmm1_1; xmm1_2; xmm1_3;
                    xmm2_0; xmm2_1; xmm2_2; xmm2_3;
                    xmm3_0; xmm3_1; xmm3_2; xmm3_3;
                    xmm4_0; xmm4_1; xmm4_2; xmm4_3;
                    xmm5_0; xmm5_1; xmm5_2; xmm5_3;
                    xmm6_0; xmm6_1; xmm6_2; xmm6_3;
                    xmm7_0; xmm7_1; xmm7_2; xmm7_3;
                    xmm8_0; xmm8_1; xmm8_2; xmm8_3;
                    xmm9_0; xmm9_1; xmm9_2; xmm9_3;
                    xmm10_0; xmm10_1; xmm10_2; xmm10_3;
                    xmm11_0; xmm11_1; xmm11_2; xmm11_3;
                    xmm12_0; xmm12_1; xmm12_2; xmm12_3;
                    xmm13_0; xmm13_1; xmm13_2; xmm13_3;
                    xmm14_0; xmm14_1; xmm14_2; xmm14_3;
                    xmm15_0; xmm15_1; xmm15_2; xmm15_3;
                  |] in
    let cxasm =
      let cxarr = Array.make 16 Z.zero in
      for i = 0 to 15 do
        let a = getf state cxregs.(i * 4 + 0) in
        let b = getf state cxregs.(i * 4 + 1) in
        let c = getf state cxregs.(i * 4 + 2) in
        let d = getf state cxregs.(i * 4 + 3) in

        cxarr.(i) <- ImplA.int256_to_z (a, b, c, d);
        (* Printf.printf "The CXasm is %s\n" (Z.to_string cxarr.(i)); *)
      done;
      cxarr
    in
    let result = ref true in
    for i = 0 to 15 do
      (* Skip checking rsp and rbp values *)
      if i <> 4 && i <> 5 then
      result := !result && (jasm.(i) = casm.(i))
    done;

    (* check xmm registers  *)
    for i = 0 to 15 do
      result := !result && (jxasm.(i) = cxasm.(i))
    done;

    (* Checking the 5 flags  *)
    let j_rflagv_encoding r =
      let open A in
      match r with
      | J.Arch_decl.Def b -> if b = true then 1 else 0
      | J.Arch_decl.Undef -> 2
    in
    let jflags : A.rflag array = [|CF; PF; ZF; SF; OF|] in
    let jflags_vals =
      let temp = Array.make 5 2 in
      for i = 0 to 4 do
        temp.(i) <- j_rflagv_encoding (J.Exec.read_flag J.Syscall_ocaml.sc_sem A.asm_e._asm new_state jflags.(i))
      done;
      temp
    in
    let cflags_vals = Z.of_int64_unsigned(getf state rflags) in

    (* checking CF flag  *)
    if jflags_vals.(0) <> 2 then
      result := !result && (Z.testbit cflags_vals 0 = (jflags_vals.(0) = 1));

    (* checking PF flag  *)
    if jflags_vals.(1) <> 2 then
      result := !result && (Z.testbit cflags_vals 2 = (jflags_vals.(1) = 1));

    (* checking ZF flag  *)
    if jflags_vals.(2) <> 2 then
      result := !result && (Z.testbit cflags_vals 6 = (jflags_vals.(2) = 1));

    (* checking SF flag  *)
    if jflags_vals.(3) <> 2 then
      result := !result && (Z.testbit cflags_vals 7 = (jflags_vals.(3) = 1));

    (* checking OF flag  *)
    if jflags_vals.(4) <> 2 then
      result := !result && (Z.testbit cflags_vals 11 = (jflags_vals.(4) = 1));

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
    let crax    = Crowbar.int64 in
    let crcx    = Crowbar.int64 in
    let crdx    = Crowbar.int64 in
    let crbx    = Crowbar.int64 in
    let crsp    = Crowbar.int64 in
    let crbp    = Crowbar.int64 in
    let crsi    = Crowbar.int64 in
    let crdi    = Crowbar.int64 in
    let cr8     = Crowbar.int64 in
    let cr9     = Crowbar.int64 in
    let cr10    = Crowbar.int64 in
    let cr11    = Crowbar.int64 in
    let cr12    = Crowbar.int64 in
    let cr13    = Crowbar.int64 in
    let cr14    = Crowbar.int64 in
    let cr15    = Crowbar.int64 in

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
    let crflags = Crowbar.int64 in

    Crowbar.map [
                  crax;     crcx;     crdx;     crbx;     crsp;     crbp;     crsi;     crdi;
                  cr8;      cr9;      cr10;     cr11;     cr12;     cr13;     cr14;     cr15;
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
      fun rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15
          (* xmm0_0 xmm0_1 xmm0_2 xmm0_3 xmm1_0 xmm1_1 xmm1_2 xmm1_3
          xmm2_0 xmm2_1 xmm2_2 xmm2_3 xmm3_0 xmm3_1 xmm3_2 xmm3_3
          xmm4_0 xmm4_1 xmm4_2 xmm4_3 xmm5_0 xmm5_1 xmm5_2 xmm5_3
          xmm6_0 xmm6_1 xmm6_2 xmm6_3 xmm7_0 xmm7_1 xmm7_2 xmm7_3
          xmm8_0 xmm8_1 xmm8_2 xmm8_3 xmm9_0 xmm9_1 xmm9_2 xmm9_3
          xmm10_0 xmm10_1 xmm10_2 xmm10_3 xmm11_0 xmm11_1 xmm11_2 xmm11_3
          xmm12_0 xmm12_1 xmm12_2 xmm12_3 xmm13_0 xmm13_1 xmm13_2 xmm13_3
          xmm14_0 xmm14_1 xmm14_2 xmm14_3 xmm15_0 xmm15_1 xmm15_2 xmm15_3 *)
          rflags ->
        let my_array = [|rax; rcx; rdx; rbx; rsp; rbp; rsi; rdi;
                          r8; r9; r10; r11; r12; r13; r14; r15;
                          rax; rcx; rdx; rbx; rsp; rbp; rsi; rdi;
                          r8; r9; r10; r11; r12; r13; r14; r15;
                          rax; rcx; rdx; rbx; rsp; rbp; rsi; rdi;
                          r8; r9; r10; r11; r12; r13; r14; r15;
                          rax; rcx; rdx; rbx; rsp; rbp; rsi; rdi;
                          r8; r9; r10; r11; r12; r13; r14; r15;
                          rax; rcx; rdx; rbx; rsp; rbp; rsi; rdi;
                          r8; r9; r10; r11; r12; r13; r14; r15;
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
