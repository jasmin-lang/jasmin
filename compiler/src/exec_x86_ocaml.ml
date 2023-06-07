open Jasmin
open Utils
open Glob_options

let main () =
  let call_conv =
    match !Glob_options.call_conv with
    | Linux -> X86_decl.x86_linux_call_conv
    | Windows -> X86_decl.x86_windows_call_conv
  in (*
  let lowering_vars _ = assert false in

  let (module Ocaml_params : Arch_full.Core_arch with type reg = X86_decl.register) =
    let lowering_opt =
      X86_lowering.{ use_lea = !Glob_options.lea;
                     use_set0 = !Glob_options.set0; } in
    let module Lowering_params = struct

        let lowering_vars = lowering_vars

        let lowering_opt = lowering_opt
      end in
    (module X86_arch_full.X86(Lowering_params))
  in
  let module Arch = Arch_full.Arch_from_Core_arch (Ocaml_params) in *)

  let pp_rflagv fmt r =
    let open Arch_decl in
    match r with
    | Def b -> Format.fprintf fmt "%b" b
    | Undef -> Format.fprintf fmt "undef"
  in

  let pp_ip fmt asm_state =
    Format.fprintf fmt "ip: %d" (Conv.int_of_nat (Exec_x86.read_ip Syscall_ocaml.sc_sem asm_state))
  in

  let pp_regs fmt asm_state =
    List.iter (fun r ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (X86_decl_core.string_of_register r)
        Z.pp_print (Conv.z_of_cz (Exec_x86.read_reg Syscall_ocaml.sc_sem asm_state r))) X86_decl.registers
  in

  let pp_regxs fmt asm_state =
    List.iter (fun rx ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (X86_decl_core.string_of_regx rx)
        Z.pp_print (Conv.z_of_cz (Exec_x86.read_regx Syscall_ocaml.sc_sem asm_state rx))) X86_decl.regxs
  in

  let pp_xregs fmt asm_state =
    List.iter (fun rx ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (X86_decl_core.string_of_xmm_register rx)
        Z.pp_print (Conv.z_of_cz (Exec_x86.read_xreg Syscall_ocaml.sc_sem asm_state rx))) X86_decl.xmm_registers
  in

  let pp_flags fmt asm_state =
    List.iter (fun f ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (X86_decl_core.string_of_rflag f)
        pp_rflagv (Exec_x86.read_flag Syscall_ocaml.sc_sem asm_state f)) X86_decl.rflags
  in

  let pp_asm_state fmt asm_state =
    Format.fprintf fmt "@[<v>%a@;%a%a%a%a@]"
      pp_ip asm_state
      pp_regs asm_state
      pp_regxs asm_state
      pp_xregs asm_state
      pp_flags asm_state
  in

  (* a bit horrible *)
  let parse_op (op:string) =
    let id = Location.mk_loc Location._dummy op in
    let op, _ = Pretyping.tt_prim (Arch_extra.asm_opI X86_arch_full.X86_core.asm_e) None id [] in
    match op with
    | BaseOp (_, op) -> op
    | ExtOp _ -> failwith "extop"
  in

  let parse_arg =
    let reg_names = List.map (fun r -> (Conv.string_of_cstring (X86_decl_core.string_of_register r), r)) X86_decl.registers in
    fun arg ->
      Arch_decl.Reg (List.assoc arg reg_names)
  in

  let dummy_asmscsem = fun _ _ -> assert false in
  let exec_i ip reg_values regx_values xreg_values flag_values fn i =
    let asm_state =
      match Exec_x86.mk_asm_state Syscall_ocaml.sc_sem (Syscall_ocaml.initial_state ())
            ip reg_values regx_values xreg_values flag_values fn i with
      | Utils0.Ok state -> state
      | Utils0.Error _ -> failwith "state initialization failed!"
    in
    Format.printf "Initial state:@;%a@." pp_asm_state asm_state;
    Format.printf "@[<v>Running instruction:@;%a@;@]@." (Ppasm.pp_instr "name") i;
    let asm_state' =
      match Exec_x86.exec_i Syscall_ocaml.sc_sem call_conv dummy_asmscsem asm_state i with
      | Utils0.Ok state -> state
      | Utils0.Error _ -> failwith "execution failed!"
    in
    Format.printf "New state:@;%a@." pp_asm_state asm_state';
    Exec_x86.of_asm_state Syscall_ocaml.sc_sem asm_state'
  in

  (* checking some basic stuff  *)
  let op = ref "ADD" in
  let args = ref ["RAX"; "RBX"] in
  let regs = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] in
  let regx = [0; 0; 0; 0; 0; 0; 0; 0] in
  let xreg = [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] in
  let flags = [Arch_decl.Undef; Arch_decl.Undef; Arch_decl.Undef; Arch_decl.Undef; Arch_decl.Undef] in

  let ip = Conv.nat_of_int 0 in
  let reg_values = List.map Conv.cz_of_int (regs) in
  let regx_values = List.map Conv.cz_of_int (regx) in
  let xreg_values = List.map Conv.cz_of_int (xreg) in
  let flag_values = flags in
  let op = parse_op !op in
  let args = List.map parse_arg !args in
  let i = Arch_decl.AsmOp (op, args) in
  let fn = Prog.F.mk "f" in
  let _ = exec_i ip reg_values regx_values xreg_values flag_values fn i in
  ()
