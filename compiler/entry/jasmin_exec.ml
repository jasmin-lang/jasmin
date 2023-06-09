(* -------------------------------------------------------------------- *)
module J = Jasmin

module Impl = struct

open Jasmin

let init_state ip reg_values regx_values xreg_values flag_values fn i =
  match Exec_x86.mk_asm_state Syscall_ocaml.sc_sem (Syscall_ocaml.initial_state ())
          ip reg_values regx_values xreg_values flag_values fn i with
  | Utils0.Ok state -> state
  | Utils0.Error _ -> failwith "state initialization failed!"

let exec_instr call_conv asm_state i =
  let dummy_asmscsem = fun _ _ -> assert false in
  match Exec_x86.exec_i Syscall_ocaml.sc_sem call_conv dummy_asmscsem asm_state i with
  | Utils0.Ok state -> state
  | Utils0.Error _ -> failwith "execution failed!"

let parse_op (op:string) =
  let id = Location.mk_loc Location._dummy op in
  let op, _ = Pretyping.tt_prim (Arch_extra.asm_opI X86_arch_full.X86_core.asm_e) None id [] in
  match op with
  | BaseOp (_, op) -> op
  | ExtOp _ -> failwith "extop"

let parse_arg =
  let reg_names = List.map (fun r -> (Conv.string_of_cstring (X86_decl_core.string_of_register r), r)) X86_decl.registers in
  fun arg ->
    Arch_decl.Reg (List.assoc arg reg_names)

  let pp_rflagv fmt r =
    let open Arch_decl in
    match r with
    | Def b -> Format.fprintf fmt "%b" b
    | Undef -> Format.fprintf fmt "undef"

  let pp_ip fmt asm_state =
    Format.fprintf fmt "ip: %d" (Conv.int_of_nat (Exec_x86.read_ip Syscall_ocaml.sc_sem asm_state))

  let pp_regs fmt asm_state =
    List.iter (fun r ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (X86_decl_core.string_of_register r)
        Z.pp_print (Conv.z_of_cz (Exec_x86.read_reg Syscall_ocaml.sc_sem asm_state r))) X86_decl.registers

  let pp_regxs fmt asm_state =
    List.iter (fun rx ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (X86_decl_core.string_of_regx rx)
        Z.pp_print (Conv.z_of_cz (Exec_x86.read_regx Syscall_ocaml.sc_sem asm_state rx))) X86_decl.regxs

  let pp_xregs fmt asm_state =
    List.iter (fun rx ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (X86_decl_core.string_of_xmm_register rx)
        Z.pp_print (Conv.z_of_cz (Exec_x86.read_xreg Syscall_ocaml.sc_sem asm_state rx))) X86_decl.xmm_registers

  let pp_flags fmt asm_state =
    List.iter (fun f ->
      Format.fprintf fmt "%a: %a@;"
        PrintCommon.pp_string0 (X86_decl_core.string_of_rflag f)
        pp_rflagv (Exec_x86.read_flag Syscall_ocaml.sc_sem asm_state f)) X86_decl.rflags

  let pp_asm_state fmt asm_state =
    Format.fprintf fmt "@[<v>%a@;%a%a%a%a@]"
      pp_ip asm_state
      pp_regs asm_state
      pp_regxs asm_state
      pp_xregs asm_state
      pp_flags asm_state
end

type arch = Amd64 | CortexM

let parse_and_exec call_conv =
  let call_conv =
    match call_conv with
    | J.Glob_options.Linux -> J.X86_decl.x86_linux_call_conv
    | J.Glob_options.Windows -> J.X86_decl.x86_windows_call_conv
  in

  let op = ref "ADD" in
  let args = ref ["RAX"; "RBX"] in
  let regs = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15] in
  let regx = [0; 0; 0; 0; 0; 0; 0; 0] in
  let xreg = [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] in
  let flags = [J.Arch_decl.Undef; J.Arch_decl.Undef; J.Arch_decl.Undef; J.Arch_decl.Undef; J.Arch_decl.Undef] in

  let ip = J.Conv.nat_of_int 0 in
  let reg_values = List.map J.Conv.cz_of_int (regs) in
  let regx_values = List.map J.Conv.cz_of_int (regx) in
  let xreg_values = List.map J.Conv.cz_of_int (xreg) in
  let flag_values = flags in
  let op = Impl.parse_op !op in
  let args = List.map Impl.parse_arg !args in 
  let i = J.Arch_decl.AsmOp (op, args) in
  let fn = J.Prog.F.mk "f" in

  let asm_state = Impl.init_state ip reg_values regx_values xreg_values flag_values fn i in
  Format.printf "Initial state:@;%a@." Impl.pp_asm_state asm_state;
  Format.printf "@[<v>Running instruction:@;%a@;@]@." (J.Ppasm.pp_instr "name") i;
  let asm_state' = Impl.exec_instr call_conv asm_state i in
  Format.printf "New state:@;%a@." Impl.pp_asm_state asm_state'

open Cmdliner

let arch =
  let alts = [ ("x86-64", Amd64); ("arm-m4", CortexM) ] in
  let doc =
    Format.asprintf "The target architecture (%s)" (Arg.doc_alts_enum alts)
  in
  let arch = Arg.enum alts in
  Arg.(value & opt arch Amd64 & info [ "arch" ] ~doc)

let call_conv =
  let alts =
    [ ("linux", J.Glob_options.Linux); ("windows", J.Glob_options.Windows) ]
  in
  let doc = Format.asprintf "Undocumented (%s)" (Arg.doc_alts_enum alts) in
  let call_conv = Arg.enum alts in
  Arg.(
    value
    & opt call_conv J.Glob_options.Linux
    & info [ "call-conv"; "cc" ] ~docv:"OS" ~doc)

let () =
  let doc = "Execute one Jasmin instruction" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jasmin_instr" ~version:J.Glob_options.version_string ~doc ~man
  in
  Cmd.v info Term.(const parse_and_exec $ call_conv)
  |> Cmd.eval |> exit
