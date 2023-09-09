open Utils
open Glob_options
open Prog

let check_stack_size fds =
  List.iter
    (fun ( { Expr.sf_stk_sz; Expr.sf_stk_extra_sz; Expr.sf_align; Expr.sf_max_call_depth },
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
      (match f_annot.stack_align with
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
              (string_of_ws actual) (string_of_ws expected));
      match f_annot.max_call_depth with
      | None -> ()
      | Some expected ->
          let actual = Conv.z_of_cz sf_max_call_depth in
          if actual = expected then (
            if !debug then
              Format.eprintf "INFO: %s has the expected max call depth (%a)@."
                f_name.fn_name Z.pp_print expected)
            else
              hierror "the maximum call depth is %a (expected: %a)"
                Z.pp_print actual Z.pp_print expected)
    fds

let rec check_no_for_loop ~funname s =
  List.iter (check_no_for_loop_i ~funname) s

and check_no_for_loop_i ~funname { i_desc; i_loc; _ } =
  check_no_for_loop_i_r ~funname ~loc:i_loc i_desc

and check_no_for_loop_i_r ~funname ~loc = function
  | Cassgn _ | Copn _ | Csyscall _ | Ccall _ -> ()
  | Cif (_, a, b) | Cwhile (_, a, _, b) ->
      check_no_for_loop ~funname a;
      check_no_for_loop ~funname b
  | Cfor _ ->
      hierror ~funname ~loc:(Lmore loc) ~kind:"compilation error"
        ~sub_kind:"loop unrolling" ~internal:false "for loops remain"

let check_no_for_loop (_, fds) =
  List.iter
    (fun { f_name; f_body; _ } ->
      check_no_for_loop ~funname:f_name.fn_name f_body)
    fds

let rec check_no_inline_instr ~funname s =
  List.iter (check_no_inline_instr_i ~funname) s

and check_no_inline_instr_i ~funname i =
  if has_annot "inline" i then
    hierror ~funname ~loc:(Lmore i.i_loc) ~internal:false
      ~kind:"compilation error" ~sub_kind:"loop unrolling"
      "“inline”-annotated instructions remain";
  check_no_inline_instr_i_r ~funname i.i_desc

and check_no_inline_instr_i_r ~funname = function
  | Cassgn _ | Copn _ | Csyscall _ | Cfor _ | Ccall _ -> ()
  | Cif (_, a, b) | Cwhile (_, a, _, b) ->
      check_no_inline_instr ~funname a;
      check_no_inline_instr ~funname b

let check_no_inline_instr (_, fds) =
  List.iter
    (fun { f_name; f_body; _ } ->
      check_no_inline_instr ~funname:f_name.fn_name f_body)
    fds
