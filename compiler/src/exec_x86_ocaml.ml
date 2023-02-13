open Jasmin
open Utils
open Glob_options

let main () =
  (* Parse command-line arguments *)
  let set_in _ = failwith "anonymous arguments are not allowed" in
  Arg.parse Glob_options.options set_in usage_msg;
  let c =
    match !color with
    | Auto -> Unix.isatty (Unix.descr_of_out_channel stderr)
    | Always -> true
    | Never -> false
  in
  if c then enable_colors ();

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
    | Def b -> Format.fprintf fmt "[Def %b]" b
    | Undef -> Format.fprintf fmt "Undef"
  in

  let dummy_asmscsem = fun _ _ -> assert false in
  let reg_values = List.map Conv.cz_of_int [1; -1; 1; 2; 2; 2; 3; 3; 3; 4; 4; 4; 5; 5; 5; 6] in
  let fn = Prog.F.mk "f" in
  let i = Arch_decl.AsmOp (X86_instr_decl.MOV U64, [Reg X86_decl_core.RSP; Reg X86_decl_core.RCX]) in
  match Exec_x86.exec_i Syscall_ocaml.sc_sem call_conv dummy_asmscsem (Syscall_ocaml.initial_state ()) reg_values fn i with
  | Utils0.Ok ((ip, reg_values'), flag_values') ->
      Format.printf "@[<v>ip: %a@;regs: @[<h>%a@]@;flags: @[<h>%a@]@]@."
        Z.pp_print (Conv.z_of_nat ip)
        (Format.pp_print_list ~pp_sep:Format.pp_print_space (fun fmt z -> Z.pp_print fmt (Conv.z_of_cz z))) reg_values'
        (Format.pp_print_list ~pp_sep:Format.pp_print_space pp_rflagv) flag_values'
  | Utils0.Error _ -> Format.printf "this is wrong, stupid guy!@."
