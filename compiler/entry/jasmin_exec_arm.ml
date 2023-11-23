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

  let pp_flags fmt asm_state =
    List.iter (fun f ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (arch_decl.toS_f.to_string f)
        pp_rflagv (Exec.read_flag Syscall_ocaml.sc_sem A.asm_e._asm asm_state f))
      arch_decl.toS_f._finC.cenum

  let pp_asm_state fmt asm_state =
    Format.fprintf fmt "@[<v>%a@;%a%a@]"
      pp_ip asm_state
      pp_regs asm_state
      pp_flags asm_state

  let regs_of_val l =
    List.map2 (fun r v -> (arch_decl.toS_r.to_string r, J.Conv.cz_of_z (Z.of_int32_unsigned v))) arch_decl.toS_r._finC.cenum l
  let flags_of_val l =
    List.map2 (fun f v -> (arch_decl.toS_f.to_string f, v)) arch_decl.toS_f._finC.cenum l

let parse_and_exec op args regs regxs xregs flags =
  let reg_values =
      try
        let l1 = regs_of_val regs in
        l1
      with Invalid_argument _ -> Format.eprintf "Not the right number of regs.@."; exit 1
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

    (* shifting rflags to last to maintain the struct packing *)
    let crflags = Crowbar.int32 in

    Crowbar.map [
                  cr0;  cr1;  cr2;  cr3;  cr4;  cr5;  cr6;  cr7;
                  cr8;  cr9;  cr10; cr11; cr12; clr;  csp;  crflags;
                ] (
      fun r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 lr sp
          rflags ->
          let my_array = [|
                            r0;  r1;  r2;   r3;   r4;   r5;   r6;   r7;
                            r8;  r9;  r10;  r11;  r12;  lr;   sp;   rflags
                          |] in
        my_array
    )
  in

  Crowbar.add_test ~name:"Differential Testing " [ asm_arr]  (fun asm_arr -> is_correct asm_arr)
