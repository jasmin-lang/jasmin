open Utils
open Glob_options
open Prog

let check_stack_size fds =
  List.iter
    (fun ( { Expr.sf_stk_sz; Expr.sf_stk_extra_sz; Expr.sf_align },
           { f_loc; f_annot; f_name } ) ->
      let hierror fmt =
        hierror ~loc:(Lone f_loc) ~funname:f_name.fn_name
          ~kind:"compilation error" ~sub_kind:"stack allocation" fmt
      in
      (match f_annot.stack_size with
      | None -> ()
      | Some expected ->
          let actual = Conv.z_of_cz sf_stk_sz in
          if Z.equal actual expected then (
            if !debug then
              Format.eprintf "INFO: %s has the expected stack size (%a)@."
                f_name.fn_name Z.pp_print expected)
          else
            hierror "the stack has size %a (expected: %a)" Z.pp_print actual
              Z.pp_print expected);
      (match f_annot.stack_allocation_size with
      | None -> ()
      | Some expected ->
          let actual =
            Conv.z_of_cz
              (Memory_model.round_ws sf_align
                 (BinInt.Z.add sf_stk_sz sf_stk_extra_sz))
          in
          if Z.equal actual expected then (
            if !debug then
              Format.eprintf "INFO: %s has the expected stack size (%a)@."
                f_name.fn_name Z.pp_print expected)
          else
            hierror "the stack has size %a (expected: %a)" Z.pp_print actual
              Z.pp_print expected);
      match f_annot.stack_align with
      | None -> ()
      | Some expected ->
          let actual = sf_align in
          let expected = Pretyping.tt_ws expected in
          if actual = expected then (
            if !debug then
              Format.eprintf "INFO: %s has the expected stack alignment (%s)@."
                f_name.fn_name (string_of_ws expected))
          else
            hierror "the stack has alignment %s (expected: %s)"
              (string_of_ws actual) (string_of_ws expected))
    fds
