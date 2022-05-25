open Utils
open Prog
open Glob_options

(* -------------------------------------------------------------------- *)
exception UsageError

let parse () =
  let error () = raise UsageError in
  let set_in s =
    if !infile <> "" then error();
    infile := s  in
  Arg.parse options set_in usage_msg;
  let c =
    match !color with
    | Auto -> Unix.isatty (Unix.descr_of_out_channel stderr)
    | Always -> true
    | Never -> false
  in
  if c then enable_colors ();
  if !infile = "" && (not !help_intrinsics) && (!safety_makeconfigdoc = None)
     && (not !help_version)
  then error()

(*--------------------------------------------------------------------- *)

let saved_extra_free_registers : (L.i_loc -> var option) ref = ref (fun _ -> None)

(* -------------------------------------------------------------------- *)
let rec warn_extra_i i = 
  match i.i_desc with
  | Cassgn (_, tag, _, _) | Copn (_, tag, _, _) ->
    begin match tag with
    | AT_rename ->
      warning ExtraAssignment i.i_loc
        "@[<v>extra assignment introduced:@;<0 2>%a@]"
        (Printer.pp_instr ~debug:false) i
    | AT_inline ->
      hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
        "@[<v>AT_inline flag remains in instruction:@;<0 2>@[%a@]@]"
        (Printer.pp_instr ~debug:false) i
    | _ -> ()
    end
  | Csyscall _ -> ()
  | Cif(_, c1, c2) | Cwhile(_,c1,_,c2) ->
    List.iter warn_extra_i c1;
    List.iter warn_extra_i c2;
  | Cfor _ ->
    hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
      "for loop remains"
  | Ccall _ -> ()

let warn_extra_fd (_, fd) =
  List.iter warn_extra_i fd.f_body
 
(* -------------------------------------------------------------------- *)
let check_safety_p s p source_p =
  let () = if SafetyConfig.sc_print_program () then
      let s1,s2 = Glob_options.print_strings s in
      Format.eprintf "@[<v>At compilation pass: %s@;%s@;@;\
                      %a@;@]@."
        s1 s2
        (Printer.pp_prog ~debug:true) p
  in

  let () = SafetyConfig.pp_current_config_diff () in

  let () =
    List.iter (fun f_decl ->
        if f_decl.f_cc = Export then
          let () = Format.eprintf "@[<v>Analyzing function %s@]@."
              f_decl.f_name.fn_name in

          let source_f_decl = List.find (fun source_f_decl ->
              f_decl.f_name.fn_name = source_f_decl.f_name.fn_name
            ) (snd source_p) in
          let module AbsInt = SafetyInterpreter.AbsAnalyzer(struct
              let main_source = source_f_decl
              let main = f_decl
              let prog = p
            end) in

          AbsInt.analyze ())
      (List.rev (snd p)) in
  ()


let check_sct _s p _source_p = 
  try Sct_checker_forward.ty_prog p (oget !sct_list)
  with Pretyping.TyError (loc, code) -> 
    hierror ~loc:(Lone loc) ~kind:"speculative constant type checker" "%a" 
      Pretyping.pp_tyerror code 
  
(* -------------------------------------------------------------------- *)
let main () =
  let is_regx tbl x = is_regx (Conv.var_of_cvar tbl x) in
  try
    parse();

    if !safety_makeconfigdoc <> None
    then (
      let dir = oget !safety_makeconfigdoc in
      SafetyConfig.mk_config_doc dir;
      exit 0);

    if !help_intrinsics
    then (Help.show_intrinsics (); exit 0);

    if !help_version
    then (Format.printf "%s@." version_string; exit 0);

    let () = if !check_safety then
        match !safety_config with
        | Some conf -> SafetyConfig.load_config conf
        | None -> () in

    let fname = !infile in
    let env, pprog, ast =
      try 
        let env = Pretyping.Env.empty in
        let env = List.fold_left Pretyping.Env.add_from env !Glob_options.idirs in
        Pretyping.tt_program env fname
      with
      | Pretyping.TyError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"typing error" "%a" Pretyping.pp_tyerror code
      | Syntax.ParseError (loc, msg) ->
          let msg =
            match msg with
            | None -> "unexpected token" (* default message *)
            | Some msg -> msg
          in
          hierror ~loc:(Lone loc) ~kind:"parse error" "%s" msg
    in

    if !print_dependencies then begin
      Format.printf "%a" 
        (pp_list " " (fun fmt p -> Format.fprintf fmt "%s" (BatPathGen.OfString.to_string p)))
        (List.tl (List.rev (Pretyping.Env.dependencies env)));
      exit 0
    end;
 
    if !latexfile <> "" then begin
      let out = open_out !latexfile in
      let fmt = Format.formatter_of_out_channel out in
      Format.fprintf fmt "%a@." Latex_printer.pp_prog ast;
      close_out out;
      if !debug then Format.eprintf "Pretty printed to LATEX@."
    end;
  
    eprint Compiler.Typing Printer.pp_pprog pprog;

    let prog = Subst.remove_params pprog in

    let prog =
      begin try
        let prog = Insert_copy_and_fix_length.doit prog in
        Typing.check_prog prog;
        prog
      with Typing.TyError(loc, code) ->
        hierror ~loc:(Lmore loc) ~kind:"typing error" "%s" code
      end
    in
    
    (* The source program, before any compilation pass. *)
    let source_prog = prog in
    
    let do_compile = ref true in
    let donotcompile () = do_compile := false in

    (* This function is called after each compilation pass.
        - Check program safety (and exit) if the time has come
        - Pretty-print the program
        - Add your own checker here!
    *)
    let visit_prog_after_pass ~debug s p =
      if s = SafetyConfig.sc_comp_pass () && !check_safety then
        check_safety_p s p source_prog
        |> donotcompile
      else if s = !Glob_options.sct_comp_pass && !sct_list <> None then
        check_sct s p source_prog
        |> donotcompile
      else
        eprint s (Printer.pp_prog ~debug) p in

    visit_prog_after_pass ~debug:true Compiler.ParamsExpansion prog;

    if !ec_list <> [] then begin
      let fmt, close =
        if !ecfile = "" then Format.std_formatter, fun () -> ()
        else
          let out = open_out !ecfile in
          let fmt = Format.formatter_of_out_channel out in
          fmt, fun () -> close_out out in
      begin try
        BatPervasives.finally
          (fun () -> close ())
          (fun () -> ToEC.extract fmt !model prog !ec_list)
          ()
      with e ->
        BatPervasives.ignore_exceptions
          (fun () -> if !ecfile <> "" then Unix.unlink !ecfile) ();
        raise e end;
      donotcompile()
    end;

    if !ct_list <> None then begin
        begin try Ct_checker_forward.ty_prog ~infer:!infer source_prog (oget !ct_list)
        with Pretyping.TyError (loc, code) -> hierror ~loc:(Lone loc) ~kind:"constant type checker" "%a" Pretyping.pp_tyerror code end;
        donotcompile()
    end; 

    if !do_compile then begin
  
    (* Now call the coq compiler *)
    let all_vars = Prog.rip :: Regalloc.X64.all_registers in
    let tbl, cprog = Conv.cuprog_of_prog all_vars () prog in

    if !debug then Printf.eprintf "translated to coq \n%!";

    let to_exec = Pretyping.Env.Exec.get env in
    if to_exec <> [] then begin
        let exec (f, m) =
          try
            let pp_range fmt (ptr, sz) =
              Format.fprintf fmt "%a:%a" Z.pp_print ptr Z.pp_print sz in
            Format.printf "/* Evaluation of %s (@[<h>%a@]):@." f.fn_name
              (pp_list ",@ " pp_range) m;
            let _m, vs =
              (** TODO: allow to configure the initial stack pointer *)
              let live = List.map (fun (ptr, sz) -> Conv.int64_of_z ptr, Conv.cz_of_z sz) m in
              (match (Low_memory.Memory.coq_M U64).init live (Conv.int64_of_z (Z.of_string "1024")) with Utils0.Ok m -> m | Utils0.Error err -> raise (Evaluator.Eval_error (Coq_xH, err))) |>
              Evaluator.exec (Expr.to_uprog (Arch_extra.asm_opI X86_extra.x86_extra) cprog) (Conv.cfun_of_fun tbl f) in
            Format.printf "@[<v>%a@]@."
              (pp_list "@ " Evaluator.pp_val) vs;
            Format.printf "*/@."
          with Evaluator.Eval_error (ii,err) ->
            let (i_loc, _, _) = Conv.get_iinfo tbl ii in
            hierror ~loc:(Lmore i_loc) ~kind:"evaluation error" "%a" Evaluator.pp_error err
        in
        List.iter exec to_exec
      end;


    let lowering_vars = Lowering.(
        let f ty n = 
          let v = V.mk n (Reg(Normal, Direct)) ty L._dummy [] in
          Conv.cvar_of_var tbl v in
        let b = f tbool in
        { fresh_OF = (b "OF").vname
        ; fresh_CF = (b "CF").vname
        ; fresh_SF = (b "SF").vname
        ; fresh_PF = (b "PF").vname
        ; fresh_ZF = (b "ZF").vname
        ; fresh_multiplicand = (fun sz -> (f (Bty (U sz)) "multiplicand").vname)
        ; is_regx = is_regx tbl
        }) in

    let fdef_of_cufdef fn cfd = Conv.fdef_of_cufdef tbl (fn,cfd) in
    let cufdef_of_fdef fd = snd (Conv.cufdef_of_fdef tbl fd) in

    let apply msg trans fn cfd =
      if !debug then Format.eprintf "START %s@." msg;
      let fd = fdef_of_cufdef fn cfd in
      if !debug then Format.eprintf "back to ocaml@.";
      let fd = trans fd in
      cufdef_of_fdef fd in

    let translate_var = Conv.var_of_cvar tbl in

    let fresh_id _gd x =
      let x = Conv.var_of_cvar tbl x in
      let x' = Prog.V.clone x in
      let cx = Conv.cvar_of_var tbl x' in
      cx.Var0.Var.vname in

    let fresh_reg name ty = 
      let name = Conv.string_of_string0 name in
      let ty = Conv.ty_of_cty ty in
      let p = Prog.V.mk name (Reg(Normal, Direct)) ty L._dummy [] in
      let cp = Conv.cvar_of_var tbl p in
      cp.Var0.Var.vname in
    
    let fresh_reg_ptr name ty = 
      let name = Conv.string_of_string0 name in
      let ty = Conv.ty_of_cty ty in
      let p = Prog.V.mk name (Reg (Normal, Pointer Writable)) ty L._dummy [] in
      let cp = Conv.cvar_of_var tbl p in
      cp.Var0.Var.vname in

    let fresh_counter =
      let i = Prog.V.mk "i__copy" Inline tint L._dummy [] in
      let ci = Conv.cvar_of_var tbl i in
      ci.Var0.Var.vname in
    
    let memory_analysis up : Compiler.stack_alloc_oracles =
      StackAlloc.memory_analysis (Printer.pp_err ~debug:!debug) ~debug:!debug tbl fresh_reg_ptr X86_params.aparams up
     in

    let global_regalloc fds =
      if !debug then Format.eprintf "START regalloc@.";
      let fds = List.map (Conv.fdef_of_csfdef tbl) fds in
      (* TODO: move *)
      (* Check the stacksize, stackallocsize & stackalign annotations, if any *)
      List.iter (fun ({ Expr.sf_stk_sz ; Expr.sf_stk_extra_sz ; Expr.sf_align }, { f_loc ; f_annot ; f_name }) ->
          let hierror fmt =
            hierror ~loc:(Lone f_loc) ~funname:f_name.fn_name
              ~kind:"compilation error" ~sub_kind:"stack allocation" fmt
          in
          begin match f_annot.stack_size with
          | None -> ()
          | Some expected ->
             let actual = Conv.z_of_cz sf_stk_sz in
             if Z.equal actual expected
             then (if !debug then Format.eprintf "INFO: %s has the expected stack size (%a)@." f_name.fn_name Z.pp_print expected)
             else hierror "the stack has size %a (expected: %a)" Z.pp_print actual Z.pp_print expected
          end;
          begin match f_annot.stack_allocation_size with
          | None -> ()
          | Some expected ->
             let actual = Conv.z_of_cz (Memory_model.round_ws sf_align (BinInt.Z.add sf_stk_sz sf_stk_extra_sz)) in
             if Z.equal actual expected
             then (if !debug then Format.eprintf "INFO: %s has the expected stack size (%a)@." f_name.fn_name Z.pp_print expected)
             else hierror "the stack has size %a (expected: %a)" Z.pp_print actual Z.pp_print expected
          end;
          begin match f_annot.stack_align with
          | None -> ()
          | Some expected ->
             let actual = sf_align in
             if actual = expected
             then (if !debug then Format.eprintf "INFO: %s has the expected stack alignment (%s)@." f_name.fn_name (string_of_ws expected))
             else hierror "the stack has alignment %s (expected: %s)" (string_of_ws actual) (string_of_ws expected)
          end
        ) fds;

      let fds, extra_free_registers =
        Regalloc.alloc_prog translate_var (fun _fd extra ->
            match extra.Expr.sf_save_stack with
            | Expr.SavedStackReg _ | Expr.SavedStackStk _ -> true
            | Expr.SavedStackNone -> false) fds in
      saved_extra_free_registers := extra_free_registers;
      let fds = List.map (fun (y,_,x) -> y, x) fds in
      let fds = List.map (Conv.csfdef_of_fdef tbl) fds in
      fds in

    let is_var_in_memory cv : bool =
      let v = Conv.vari_of_cvari tbl cv |> L.unloc in
      match v.v_kind with
      | Stack _ | Reg (_, Pointer _) | Global -> true
      | Const | Inline | Reg(_, Direct) -> false
     in

    let pp_cuprog s cp =
      Conv.prog_of_cuprog tbl cp |>
      visit_prog_after_pass ~debug:true s in

    let pp_csprog fmt cp =
      let p = Conv.prog_of_csprog tbl cp in
      Printer.pp_sprog ~debug:true tbl fmt p in

    let pp_linear fmt lp =
      PrintLinear.pp_prog tbl fmt lp in

    let rename_fd ii fn cfd =
      let ii, _, _ = Conv.get_iinfo tbl ii in
      let doit fd =
        let fd = Subst.clone_func fd in
        Subst.extend_iinfo ii fd in
      apply "rename_fd" doit fn cfd in

    let expand_fd fn cfd = 
      let fd = Conv.fdef_of_cufdef tbl (fn, cfd) in
      let vars, harrs = Array_expand.init_tbl fd in
      let cvar = Conv.cvar_of_var tbl in
      let vars = List.map cvar (Sv.elements vars) in
      let arrs = ref [] in
      let doarr x (ws, xs) = 
        arrs := 
          Array_expansion.{ 
            vi_v = cvar x;
            vi_s = ws;
            vi_n = List.map (fun x -> (cvar x).Var0.Var.vname) (Array.to_list xs); } :: !arrs in
      Hv.iter doarr harrs;
      { Array_expansion.vars = vars; arrs = !arrs } in

    let warning ii msg =
      if not !Glob_options.lea then begin
          let loc, _, _ = Conv.get_iinfo tbl ii in
          warning UseLea loc "%a" Printer.pp_warning_msg msg
        end;
      ii in

    let inline_var x =
      let x = Conv.var_of_cvar tbl x in
      x.v_kind = Inline in

   
    let is_glob x =
      let x = Conv.var_of_cvar tbl x in
      x.v_kind = Global in

    let split_live_ranges_fd fd = Regalloc.split_live_ranges fd in
    let renaming_fd fd = Regalloc.renaming fd in
    let remove_phi_nodes_fd fd = Regalloc.remove_phi_nodes fd in

    let removereturn sp = 
      let (fds,_data) = Conv.prog_of_csprog tbl sp in
      let tokeep = RemoveUnusedResults.analyse  fds in 
      let tokeep fn = tokeep (Conv.fun_of_cfun tbl fn) in
      tokeep in

    let is_reg_ptr x = 
      let x = Conv.var_of_cvar tbl x in
      is_reg_ptr_kind x.v_kind in

    let is_ptr x = 
      let x = Conv.var_of_cvar tbl x in
      is_ptr x.v_kind in

    let is_reg_array x =
      is_reg_arr (Conv.var_of_cvar tbl x)
    in

    let warn_extra s p =
      if s = Compiler.DeadCode_RegAllocation then
        let (fds, _) = Conv.prog_of_csprog tbl p in
        List.iter warn_extra_fd fds in

    let cparams = {
      Compiler.rename_fd    = rename_fd;
      Compiler.expand_fd    = expand_fd;
      Compiler.split_live_ranges_fd = apply "split live ranges" split_live_ranges_fd;
      Compiler.renaming_fd = apply "alloc inline assgn" renaming_fd;
      Compiler.remove_phi_nodes_fd = apply "remove phi nodes" remove_phi_nodes_fd;
      Compiler.stack_register_symbol = Var0.Var.vname (Conv.cvar_of_var tbl Prog.rsp);
      Compiler.global_static_data_symbol = Var0.Var.vname (Conv.cvar_of_var tbl Prog.rip);
      Compiler.stackalloc    = memory_analysis;
      Compiler.removereturn  = removereturn;
      Compiler.regalloc      = global_regalloc;
      Compiler.extra_free_registers = (fun ii ->
        let loc, _, _ = Conv.get_iinfo tbl ii in
        !saved_extra_free_registers loc |> omap (Conv.cvar_of_var tbl)
      );
      Compiler.lowering_vars = lowering_vars;
      Compiler.is_var_in_memory = is_var_in_memory;
      Compiler.print_uprog  = (fun s p -> pp_cuprog s p; p);
      Compiler.print_sprog  = (fun s p -> warn_extra s p;
                                          eprint s pp_csprog p; p);
      Compiler.print_linear = (fun s p -> eprint s pp_linear p; p);
      Compiler.warning      = warning;
      Compiler.inline_var   = inline_var;
      Compiler.lowering_opt = Lowering.{ use_lea = !Glob_options.lea;
                                         use_set0 = !Glob_options.set0; };
      Compiler.is_glob     = is_glob;
      Compiler.fresh_id    = fresh_id;
      Compiler.fresh_reg   = fresh_reg;
      Compiler.fresh_reg_ptr = fresh_reg_ptr;
      Compiler.fresh_counter = fresh_counter;
      Compiler.is_reg_ptr  = is_reg_ptr;
      Compiler.is_ptr      = is_ptr;
      Compiler.is_reg_array = is_reg_array;
      Compiler.is_regx      = is_regx tbl;
    } in

    let export_functions, subroutines =
      let conv fd = Conv.cfun_of_fun tbl fd.f_name in
      List.fold_right
        (fun fd ((e, i) as acc) ->
          match fd.f_cc with
          | Export -> (conv fd :: e, i)
          | Internal -> acc
          | Subroutine _ -> (e, conv fd :: i)
        )
        (snd prog)
        ([], []) in

    begin match
      Compiler.compile_prog_to_x86 cparams X86_params.aparams export_functions subroutines (Expr.to_uprog (Arch_extra.asm_opI X86_extra.x86_extra) cprog) with
    | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:!debug tbl) tbl e in
      raise (HiError e)
    | Utils0.Ok asm ->
      if !outfile <> "" then begin
        BatFile.with_file_out !outfile (fun out ->
          let fmt = BatFormat.formatter_of_out_channel out in
          Format.fprintf fmt "%a%!" (Ppasm.pp_prog tbl) asm);
          if !debug then Format.eprintf "assembly listing written@."
      end else if List.mem Compiler.Assembly !print_list then
          Format.printf "%a%!" (Ppasm.pp_prog tbl) asm
    end
    end
  with
  | Utils.HiError e ->
    Format.eprintf "%a@." pp_hierror e;
    exit 1

  | UsageError ->
    Arg.usage options usage_msg;
    exit 1

(* -------------------------------------------------------------------- *)
let () = main ()
