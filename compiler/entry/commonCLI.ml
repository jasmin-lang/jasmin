open Jasmin
open Cmdliner
open Utils

let get_arch_module arch call_conv : (module Arch_full.Arch) =
  (module Arch_full.Arch_from_Core_arch
            ((val match arch with
                  | Utils.X86_64 ->
                      (module (val CoreArchFactory.core_arch_x86 ~use_lea:false
                                     ~use_set0:false call_conv)
                      : Arch_full.Core_arch)
                  | Utils.ARM_M4 ->
                      (module CoreArchFactory.Core_arch_ARM
                      : Arch_full.Core_arch)
                  | Utils.RISCV ->
                      (module CoreArchFactory.Core_arch_RISCV
                      : Arch_full.Core_arch))))

let arch =
  let alts =
    [
      ("x86-64", Utils.X86_64); ("arm-m4", Utils.ARM_M4); ("riscv", Utils.RISCV);
    ]
  in
  let doc =
    Format.asprintf "The target architecture (%s)" (Arg.doc_alts_enum alts)
  in
  let arch = Arg.enum alts in
  Arg.(value & opt arch Utils.X86_64 & info [ "arch" ] ~doc)

let call_conv =
  let alts =
    [ ("linux", Glob_options.Linux); ("windows", Glob_options.Windows) ]
  in
  let doc = Format.asprintf "Undocumented (%s)" (Arg.doc_alts_enum alts) in
  let call_conv = Arg.enum alts in
  Arg.(
    value
    & opt call_conv Glob_options.Linux
    & info [ "call-conv"; "cc" ] ~docv:"OS" ~doc)

let idirs =
  let doc =
    "Bind ident to path for 'from ident require ...'"
  in
  let info = Arg.info [ "I"; "include" ] ~docv:"ident=path" ~doc in
  let conv = Arg.pair ~sep:'=' Arg.string Arg.dir in
  Arg.value (Arg.opt_all conv [] info)

let warn =
  let doc = "Print warnings" in
  Arg.(value & flag & info [ "warn" ] ~doc)

let after_pass =
  let alts =
    List.map
      (fun s -> (fst (Glob_options.print_strings s), s))
      Compiler.(List.filter (( > ) StackAllocation) compiler_step_list)
  in
  let doc =
    Format.asprintf "Run after the given compilation pass (%s)."
      (Arg.doc_alts_enum alts)
  in

  let passes = Arg.enum alts in
  Arg.(value & opt passes Typing & info [ "compile"; "after" ] ~doc)

let parse_and_compile (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) ~wi2i pass file idirs =
  let _env, pprog, _ast =
    try Compile.parse_file Arch.arch_info ~idirs file with
    | Annot.AnnotationError (loc, code) ->
        hierror ~loc:(Lone loc) ~kind:"annotation error" "%t" code
    | Pretyping.TyError (loc, code) ->
        hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror
          code
    | Syntax.ParseError (loc, msg) ->
        hierror ~loc:(Lone loc) ~kind:"parse error" "%s" (Option.default "" msg)
  in
  let prog =
    try Compile.preprocess Arch.reg_size Arch.asmOp pprog
    with Typing.TyError (loc, code) ->
      hierror ~loc:(Lmore loc) ~kind:"typing error" "%s" code
  in

  let prog =
    if not wi2i then prog else Compile.do_wint_int (module Arch) prog
  in

  let prog =
    if pass <= Compiler.ParamsExpansion then prog
    else
      let module E = struct
        exception Found
      end in
      let res = ref prog in
      let stop ~debug:_ step prog =
        if step = pass then (
          res := prog;
          raise E.Found)
      in
      let cp = Conv.cuprog_of_prog prog in
      (* We need to avoid catching compilation errors. *)
      match Compile.compile (module Arch) stop prog cp with
      | Utils0.Ok _ -> assert false
      | Utils0.Error e ->
          let e = Conv.error_of_cerror (Printer.pp_err ~debug:false) e in
          raise (HiError e)
      | exception E.Found -> !res
  in
  prog
