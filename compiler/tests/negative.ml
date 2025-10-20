(** Negative examples.

    This checks how the Jasmin compiler fails on selected programs.

    This test is run when executing `dune runtest`. *)

open Jasmin
open Utils
open Common
open Format

(** Specific configuration for some example programs. This in particular
    disables warnings that are expected. *)
let config path =
  let default () =
    Glob_options.verbosity := 0;
    Glob_options.introduce_export_renaming := true;
    set_warn_recoverable true;
    set_all_warnings ()
  in
  let reset_warn_recoverable () = set_warn_recoverable false in
  let disable_renaming () = Glob_options.introduce_export_renaming := false in
  default ();
  try
    List.assoc path
      [
        ("fail/common/bug_1214.jazz", disable_warnings [ KeptRenaming ]);
        ( "fail/param_expansion/x86-64/expression_arg.jazz",
          disable_warnings [ UnusedVar ] );
        ( "fail/param_expansion/x86-64/operator_arg.jazz",
          disable_warnings [ UnusedVar ] );
        ( "fail/register_allocation/arm-m4/bug_201.jazz",
          disable_warnings [ UnusedVar ] );
        ( "fail/register_allocation/arm-m4/too_many_args.jazz",
          disable_warnings [ UnusedVar ] );
        ( "fail/register_allocation/x86-64/bug_426_bis.jazz",
          disable_warnings [ UnusedVar ] );
        ( "fail/register_allocation/x86-64/too_many_args.jazz",
          disable_warnings [ UnusedVar ] );
        ( "fail/register_allocation/x86-64/too_many_large_args.jazz",
          disable_warnings [ UnusedVar ] );
        ( "fail/register_allocation/x86-64/unknown_type_register.jazz",
          disable_warnings [ UnusedVar ] );
        ("fail/slh/x86-64/export_takes_msf.jazz", disable_renaming);
        ( "fail/stack_allocation/x86-64/return_ptr_global.jazz",
          disable_warnings [ PedanticPretyping ] );
        ( "fail/stack_allocation/x86-64/return_ptr_local.jazz",
          disable_warnings [ PedanticPretyping ] );
        ( "fail/stack_allocation/x86-64/return_subslice.jazz",
          disable_warnings [ PedanticPretyping ] );
        ( "fail/typing/x86-64/bug_488.jazz",
          disable_warnings [ SimplifyVectorSuffix ] );
        ( "fail/typing/x86-64/export_stack_array_res.jazz",
          reset_warn_recoverable );
        ("fail/typing/x86-64/export_stack_res.jazz", reset_warn_recoverable);
        ("fail/typing/x86-64/non_inline_stack_arg.jazz", reset_warn_recoverable);
        ("fail/typing/x86-64/non_inline_stack_res.jazz", reset_warn_recoverable);
        ( "fail/typing/x86-64/res_wrong_type.jazz",
          disable_warnings [ PedanticPretyping ] );
        ( "fail/typing/x86-64/write_constant_pointer_direct_array.jazz",
          disable_warnings [ PedanticPretyping ] );
        ( "fail/typing/x86-64/write_constant_pointer_subproc_array.jazz",
          disable_warnings [ PedanticPretyping ] );
      ]
      ()
  with Not_found -> ()

(* Some statistics *)
type counters = {
  mutable annot : int;
  mutable pretyping : int;
  mutable parsing : int;
  mutable typing : int;
  mutable hi : int;
}

let counters : counters =
  { annot = 0; pretyping = 0; parsing = 0; typing = 0; hi = 0 }

let check_file_on_arch path errors arch =
  let exception Did_not_fail in
  let module Arch = (val CoreArchFactory.get_arch_module arch Linux) in
  printf "%s:\n@." path;
  try
    (try
       let _env, pprog, _ast = Compile.parse_file Arch.arch_info path in
       let prog = Compile.preprocess Arch.reg_size Arch.asmOp pprog in
       let cprog = Conv.cuprog_of_prog prog in
       let visit_prog_after_pass ~debug:_ _ _ = () in
       match Compile.compile (module Arch) visit_prog_after_pass prog cprog with
       | Utils0.Error e ->
           let e = Conv.error_of_cerror (Printer.pp_err ~debug:false) e in
           raise (HiError e)
       | Utils0.Ok _asm -> raise Did_not_fail
     with
    | Annot.AnnotationError (loc, code) ->
        printf "%a: %t" Location.pp_loc loc code;
        counters.annot <- counters.annot + 1
    | Pretyping.TyError (loc, code) ->
        printf "%a: %a\n\n" Location.pp_loc loc Pretyping.pp_tyerror code;
        counters.pretyping <- counters.pretyping + 1
    | Syntax.ParseError (loc, msg) ->
        printf "%a: %s\n\n" Location.pp_loc loc
          (Option.default "parse error" msg);
        counters.parsing <- counters.parsing + 1
    | Typing.TyError (loc, msg) ->
        printf "%a: %s\n\n" Location.pp_iloc loc msg;
        counters.typing <- counters.typing + 1
    | HiError err ->
        printf "%a\n\n" pp_hierror err;
        counters.hi <- counters.hi + 1);
    errors
  with Did_not_fail ->
    eprintf "%s did not fail as expected@." path;
    errors + 1

let check_file archs path errors =
  config path;
  List.fold_left (check_file_on_arch path) errors archs

let () =
  let result = check_dir check_file [] "fail" 0 in
  printf
    "Statistics:\n\
     \tAnnots: %6d\n\
     \tPretyping: %3d\n\
     \tParsing: %5d\n\
     \tTyping: %6d\n\
     \tCompile: %5d@."
    counters.annot counters.pretyping counters.parsing counters.typing
    counters.hi;
  exit result
