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
    let op, _ = Pretyping.tt_prim (Arch_extra.asm_opI A.asm_e) None id [] in
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
    fun arg ->
      try
        Arch_decl.Reg (List.assoc arg reg_names)
      with Not_found -> Format.eprintf "\"%s\" is not a valid register.@." arg; exit 1

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
    List.map2 (fun r v -> (arch_decl.toS_r.to_string r, J.Conv.cz_of_z (Z.of_int64 v))) arch_decl.toS_r._finC.cenum l
  let regxs_of_val l =
    List.map2 (fun r v -> (arch_decl.toS_rx.to_string r, J.Conv.cz_of_z (Z.of_int64 v))) arch_decl.toS_rx._finC.cenum l
  let xregs_of_val l =
    List.map2 (fun r v -> (arch_decl.toS_x.to_string r, J.Conv.cz_of_z (Z.of_int64 v))) arch_decl.toS_x._finC.cenum l
  let flags_of_val l =
    List.map2 (fun f v -> (arch_decl.toS_f.to_string f, v)) arch_decl.toS_f._finC.cenum l

let parse_and_exec op args reg regs regxs xregs flag flags =
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

  if (reg <> [] && (regs <> [] || regxs <> [] || xregs <> [])) then (Format.eprintf "Options \"--reg\" and {\"--regs\",\"--regxs\",\"--xregs\"} must not be used at the same time.@."; exit 1);
  if (flag <> [] && flags <> []) then (Format.eprintf "Options \"--flag\" and \"--flags\" must not be used at the same time.@."; exit 1);

  let reg_values =
    if reg <> [] then List.map (fun (r, v) -> (J.Conv.cstring_of_string r, J.Conv.cz_of_z (Z.of_int64 v))) reg
    else
      try
        let l1 = if regs <> [] then regs_of_val regs else [] in
        let l2 = if regxs <> [] then regxs_of_val regxs else [] in
        let l3 = if xregs <> [] then xregs_of_val xregs else [] in
        l1 @ l2 @ l3
      with Invalid_argument _ -> Format.eprintf "Not the right number of regs/regxs/xregs.@."; exit 1
  in

  let flag_values =
    if flag <> [] then List.map (fun (f, v) -> (J.Conv.cstring_of_string f, v)) flag
    else if flags = [] then []
    else
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

let parse_and_exec arch call_conv op args reg regs regxs xregs flag flags =
  (* we need to sync with glob_options for [tt_prim] to work, this is ugly *)
  begin match arch with
  | CortexM -> J.Glob_options.target_arch := ARM_M4
  | _ -> ()
  end;
  ImplA.parse_and_exec op args reg regs regxs xregs flag flags

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

let op =
  Arg.(required & pos 0 (some string) None & info [] ~docv:"OP")
let args =
  Arg.(value & pos_right 0 string [] & info [] ~docv:"ARG")

let reg =
  Arg.(value & opt_all (t2 ~sep:'=' string int) [] & info ["reg"] ~docv:"REG")

let regs =
  Arg.(value & opt (list int) [] & info ["regs"] ~docv:"REGS")

let regxs =
  Arg.(value & opt (list int) [] & info ["regxs"] ~docv:"REGXS")

let xregs =
  Arg.(value & opt (list int) [] & info ["xregs"] ~docv:"XREGS")

let flag_arg =
  let open J.Arch_decl in
  let parse s =
    if s = "1" then Ok (Def true)
    else if s = "0" then Ok (Def false)
    else if s = "x" then Ok Undef
    else Error (`Msg "unable to parse flag")
  in
  let print ppf f =
    match f with
    | Def b -> Format.fprintf ppf "%b" b
    | Undef -> Format.fprintf ppf "undef"
  in
  Cmdliner.Arg.conv ~docv:"FLAG" (parse, print)

let flag =
  Arg.(value & opt_all (t2 ~sep:'=' string flag_arg) [] & info ["flag"] ~docv:"FLAG")

let flags =
  Arg.(value & opt (list flag_arg) [] & info ["flags"] ~docv:"FLAGS")

open Ctypes
open Foreign

type asm_state
let asm_state : asm_state structure typ = structure "asm_state"
let rax = field asm_state "rax" int64_t
let rcx = field asm_state "rcx" int64_t
let rdx = field asm_state "rdx" int64_t
let rbx = field asm_state "rbx" int64_t
let rsp = field asm_state "rsp" int64_t
let rbp = field asm_state "rbp" int64_t
let rsi = field asm_state "rsi" int64_t
let rdi = field asm_state "rdi" int64_t
let r8 = field asm_state "r8" int64_t
let r9 = field asm_state "r9" int64_t
let r10 = field asm_state "r10" int64_t
let r11 = field asm_state "r11" int64_t
let r12 = field asm_state "r12" int64_t
let r13 = field asm_state "r13" int64_t
let r14 = field asm_state "r14" int64_t
let r15 = field asm_state "r15" int64_t
let rflags = field asm_state "rflags" int64_t
let () = seal asm_state

(* let increment_rax = foreign "increment_rax" (ptr asm_state @-> returning void) *)
let set_execute_get = foreign "set_execute_get" (ptr asm_state @-> returning void)

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
    setf state rflags 0L;

  let check state asm_arr  =
    let arch = Amd64 in
    let call_conv = !(J.Glob_options.call_conv) in
    let reg = [] in
    let regs = (Array.to_list asm_arr) in
    let regxs = [0L;0L;0L;0L;0L;0L;0L;0L] in
    let xregs = [0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L;0L] in
    let flag = [] in
    let flags = [J.Arch_decl.Def false; J.Arch_decl.Def false; J.Arch_decl.Def false; J.Arch_decl.Def false; J.Arch_decl.Def false]  in

    set_execute_get (addr state);
    let new_state = parse_and_exec arch call_conv !op_ref !args_ref reg regs regxs xregs flag flags in
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
    let result = ref true in
    for i = 0 to 15 do
      (* Skip checking rsp and rbp values *)
      if i <> 4 && i <> 5 then
      result := !result && (jasm.(i) = casm.(i))
    done;
    !result
  in
  Crowbar.check(check state asm_arr)

let () =
  let my_arg_array = Stdlib.Arg.read_arg "op_args.txt" in
  op_ref := my_arg_array.(0);                               (* ADD *)
  args_ref := String.split_on_char ' ' my_arg_array.(1);    (* RAX RBX *)

  let asm_arr =
    let crax = Crowbar.int64 in
    let crcx = Crowbar.int64 in
    let crdx = Crowbar.int64 in
    let crbx = Crowbar.int64 in
    let crsp = Crowbar.int64 in
    let crbp = Crowbar.int64 in
    let crsi = Crowbar.int64 in
    let crdi = Crowbar.int64 in
    let cr8 = Crowbar.int64 in
    let cr9 = Crowbar.int64 in
    let cr10 = Crowbar.int64 in
    let cr11 = Crowbar.int64 in
    let cr12 = Crowbar.int64 in
    let cr13 = Crowbar.int64 in
    let cr14 = Crowbar.int64 in
    let cr15 = Crowbar.int64 in

    Crowbar.map [crax; crcx; crdx; crbx; crsp; crbp; crsi; crdi;cr8; cr9; cr10; cr11; cr12; cr13; cr14; cr15] (
      fun rax rcx rdx rbx rsp rbp rsi rdi r8 r9 r10 r11 r12 r13 r14 r15 ->
        let my_array = [|rax; rcx; rdx; rbx; rsp; rbp; rsi; rdi; r8; r9; r10; r11; r12; r13; r14; r15|] in
        my_array
    )
  in

  Crowbar.add_test ~name:"check increment" [ asm_arr]  (fun asm_arr -> is_correct asm_arr)
