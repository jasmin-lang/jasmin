open Jasmin
open Common

let () =
  let p = load_file "error_messages.jazz" in
  let check_fails f =
    match Sct_checker_forward.ty_prog Arch.is_ct_sopn p [ f ] with
    | exception Annot.AnnotationError (_loc, msg) ->
        Format.printf "Annotation error in %s: %t@." f msg
    | exception Utils.HiError e ->
        Format.printf "Failed as expected %s: %a@." f Utils.pp_hierror
          { e with err_loc = Lnone }
    | _ -> assert false
  in
  List.iter check_fails
    [
      "assign_msf";
      "syscall";
      "update_msf_not_trans";
      "update_msf_wrong_expr";
      "update_msf_not_msf";
      "msf_trans";
      "not_known_as_msf";
      "msf_in_export";
      "should_be_a_msf";
      "at_least_transient";
      "unbound_level";
      "inconsistent_constraint";
      "bad_modmsf";
      "bad_nomodmsf";
      "call_bad_nomodmsf";
      "call_bad_nomodmsf2";
      "call_bad_nomodmsf3";
      "call_modmsf_destroys";
      "ret_high";
      "ret_transient";
      "ret_msf";
      "public_arg";
      "unknown function";
      "need_declassify";
    ]
