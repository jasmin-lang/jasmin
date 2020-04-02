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
  if !infile = "" then error()

(*--------------------------------------------------------------------- *)

let pp_var_i tbl fmt vi =
  let vi = Conv.vari_of_cvari tbl vi in
  Printer.pp_var ~debug:true fmt (Prog.L.unloc vi)

let pp_clval tbl fmt lv =
  Conv.lval_of_clval tbl lv |>
  Printer.(pp_glv (pp_var ~debug:true)) fmt

let rec pp_comp_err tbl fmt =
  let open Printer in
  function
  | Compiler_util.Cerr_varalloc(x,y,msg) ->
    Format.fprintf fmt "Variable allocation %a and %a: %a"
     (pp_var_i tbl) x (pp_var_i tbl) y pp_string0 msg
  | Compiler_util.Cerr_inline _ ->
    Format.fprintf fmt "Inlining error"
  | Compiler_util.Cerr_Loop s ->
    Format.fprintf fmt "loop iterator to small in %a"
      pp_string0 s
  | Compiler_util.Cerr_fold2 s ->
    Format.fprintf fmt "fold2 error in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqty (_, _, s) ->
    Format.fprintf fmt "neqty %a"
      pp_string0 s
  | Compiler_util.Cerr_neqop1(_, _, s) ->
    Format.fprintf fmt "op1 not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqop2(_, _, s) ->
    Format.fprintf fmt "op2 not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqopN(_, _, s) ->
    Format.fprintf fmt "opN not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqop(_,_, s) ->
    Format.fprintf fmt "opn not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqdir(s) ->
    Format.fprintf fmt "dir not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqexpr(_,_,s) ->
    Format.fprintf fmt "expression not equal in %a"
      pp_string0 s
  | Compiler_util.Cerr_neqlval(lv1, lv2, s) ->
    Format.fprintf fmt "lval not equal in %a: %a and %a"
      pp_string0 s (pp_clval tbl) lv1 (pp_clval tbl) lv2
  | Compiler_util.Cerr_neqfun(_,_,s) ->
    Format.fprintf fmt "funname not equal in %a"
       pp_string0 s
  | Compiler_util.Cerr_neqinstr(_,_,s) ->
    Format.fprintf fmt "instruction not equal in %a"
       pp_string0 s
  | Compiler_util.Cerr_unknown_fun(f1,s) ->
    Format.fprintf fmt "unknown function %s during %a"
     (Conv.fun_of_cfun tbl f1).fn_name
     pp_string0 s
  | Compiler_util.Cerr_in_fun f ->
    (pp_comp_ferr tbl) fmt f
  | Compiler_util.Cerr_arr_exp (e1, e2) ->
    Format.fprintf fmt "err arr exp %a and %a"
      (Printer.pp_expr ~debug:true) (Conv.expr_of_cexpr tbl e1)
      (Printer.pp_expr ~debug:true) (Conv.expr_of_cexpr tbl e2)
  | Compiler_util.Cerr_arr_exp_v _ ->
    Format.fprintf fmt "err arr exp: lval"
  | Compiler_util.Cerr_stk_alloc s ->
    Format.fprintf fmt "stack_alloc error %a"
      pp_string0 s
  | Compiler_util.Cerr_linear s ->
    Format.fprintf fmt "linearisation error %a"
      pp_string0 s
  | Compiler_util.Cerr_needspill _xs ->
    Format.fprintf fmt "Need spilling" 
  | Compiler_util.Cerr_assembler c ->
    begin match c with
    | Compiler_util.AsmErr_string s ->
      Format.fprintf fmt "assembler error %a"
        pp_string0 s
    | Compiler_util.AsmErr_cond e ->
      Format.fprintf fmt "assembler error: invalid condition %a"
        (Printer.pp_expr ~debug:true) (Conv.expr_of_cexpr tbl e)
    end

and pp_comp_ferr tbl fmt = function
  | Compiler_util.Ferr_in_body(f1,f2,(ii, err_msg)) ->
    let f1 = Conv.fun_of_cfun tbl f1 in
    let f2 = Conv.fun_of_cfun tbl f2 in
    let (i_loc, _) = Conv.get_iinfo tbl ii in
    Format.fprintf fmt "in functions %s and %s at position %a: %a"
      f1.fn_name f2.fn_name Printer.pp_iloc i_loc
      (pp_comp_err tbl) err_msg
  | Compiler_util.Ferr_neqfun(f1,f2) ->
    let f1 = Conv.fun_of_cfun tbl f1 in
    let f2 = Conv.fun_of_cfun tbl f2 in
    Format.fprintf fmt "function %s and %s not equal"
      f1.fn_name f2.fn_name
  | Compiler_util.Ferr_neqprog  ->
    Format.fprintf fmt "program not equal"
  | Compiler_util.Ferr_loop     ->
    Format.fprintf fmt "loop iterator to small"
  | Compiler_util.Ferr_uniqfun ->
    Format.fprintf fmt "two function declarations with the same name"
  | Compiler_util.Ferr_uniqglob ->
    Format.fprintf fmt "two global declarations with the same name"
  | Compiler_util.Ferr_topo ->
    Format.fprintf fmt "program is not a topological sorting of the call-graph"
  | Compiler_util.Ferr_lowering ->
    Format.fprintf fmt "lowering check fails"
  | Ferr_glob_neq ->
    Format.fprintf fmt "error global not equal"
  | Ferr_fun (f, err_msg) ->
    let f =  Conv.fun_of_cfun tbl f in
    Format.fprintf fmt "in function %s: %a"
      f.fn_name (pp_comp_err tbl) err_msg
  | Ferr_remove_glob (ii, x) ->
    let i_loc, _ = Conv.get_iinfo tbl ii in
    Format.fprintf fmt "Cannot remove global variable %a at %a"
     (pp_var_i tbl) x
     Printer.pp_iloc i_loc
  | Ferr_remove_glob_dup (_, _) ->
    Format.fprintf fmt "duplicate global: please report"
  | Compiler_util.Ferr_msg msg ->
    pp_comp_err tbl fmt msg


(* -------------------------------------------------------------------- *)
let main () =
  try

    parse();

    let fname = !infile in
    let ast   = Parseio.parse_program ~name:fname in
    let ast   = BatFile.with_file_in fname ast in

    if !latexfile <> "" then begin
      let out = open_out !latexfile in
      let fmt = Format.formatter_of_out_channel out in
      Format.fprintf fmt "%a@." Latex_printer.pp_prog ast;
      close_out out;
      if !debug then Format.eprintf "Pretty printed to LATEX@."
    end;

    let env, pprog  = Typing.tt_program Typing.Env.empty ast in
    eprint Compiler.Typing Printer.pp_pprog pprog;
    if !typeonly then exit 0;

    let prog = Subst.remove_params pprog in
    eprint Compiler.ParamsExpansion (Printer.pp_prog ~debug:true) prog;

    if !check_safety then begin
      let () =
        List.iter (fun f_decl ->
            if f_decl.f_cc = Export then
              let () = Format.eprintf "@[<v>Analyzing function %s@;@]@."
                  f_decl.f_name.fn_name in

              let module AbsInt = Safety.AbsAnalyzer(struct
                  let main = f_decl
                  let prog = prog
                end) in

              AbsInt.analyze ())
          (snd prog) in
      exit 0;
    end;

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
      exit 0
    end;

    (* FIXME: why this is not certified *)
    let prog = Inline_array_copy.doit prog in

    (* Generate the coq program if needed *)
    if !coqfile <> "" then begin
      (* FIXME: remove this option and coq_printer *)
      assert false
(*      let out = open_out !coqfile in
      let fmt = Format.formatter_of_out_channel out in
      Format.fprintf fmt "%a@." Coq_printer.pp_prog prog;
      close_out out;
      if !debug then Format.eprintf "coq program extracted@." *)
    end;
    if !coqonly then exit 0;

    (* Now call the coq compiler *)
    let all_vars = Prog.rip :: Regalloc.X64.all_registers in
    let tbl, cprog = Conv.cuprog_of_prog all_vars () prog in

    if !debug then Printf.eprintf "translated to coq \n%!";

    let to_exec = Typing.Env.Exec.get env in
    if to_exec <> [] then begin
        let exec (f, m) =
          try
            let pp_range fmt (ptr, sz) =
              Format.fprintf fmt "%a:%a" B.pp_print ptr B.pp_print sz in
            Format.printf "Evaluation of %s (@[<h>%a@]):@." f.fn_name
              (pp_list ",@ " pp_range) m;
            let _m, vs =
              (** TODO: allow to configure the initial stack pointer *)
              let live = List.map (fun (ptr, sz) -> Conv.int64_of_bi ptr, Conv.z_of_bi sz) m in
              (match Low_memory.Memory.coq_M.init live (Conv.int64_of_bi (Bigint.of_string "1024")) with Utils0.Ok m -> m | Utils0.Error err -> raise (Evaluator.Eval_error (Coq_xH, err))) |>
              Evaluator.exec (Expr.to_uprog cprog) (Conv.cfun_of_fun tbl f) in
            Format.printf "@[<v>%a@]@."
              (pp_list "@ " Evaluator.pp_val) vs
          with Evaluator.Eval_error (ii,err) ->
            Format.eprintf "%a" Evaluator.pp_error (tbl, ii, err)
        in
        List.iter exec to_exec
      end;


    let lowering_vars = Lowering.(
        let f ty n = 
          let v = V.mk n (Reg Direct) ty L._dummy in
          Conv.cvar_of_var tbl v in
        let b = f tbool in
        { fresh_OF = (b "OF").vname
        ; fresh_CF = (b "CF").vname
        ; fresh_SF = (b "SF").vname
        ; fresh_PF = (b "PF").vname
        ; fresh_ZF = (b "ZF").vname
        ; fresh_multiplicand = (fun sz -> (f (Bty (U sz)) "multiplicand").vname)
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
    
    let memory_analysis up : Compiler.stack_alloc_oracles =
      let open StackAlloc in
      let open Regalloc in
      if !debug then Format.eprintf "START memory analysis@.";
      let p = Conv.prog_of_cuprog tbl up in
      let pmap, fds = StackAlloc.alloc_prog p in
      if !debug then
        Format.eprintf "After memory analysis@.%a@."
          (Printer.pp_prog ~debug:true) ([], (List.map snd fds));

      (* remove unused result *)
      let tokeep = RemoveUnusedResults.analyse fds in
      let tokeep fn = tokeep (Conv.fun_of_cfun tbl fn) in
      let deadcode (extra, fd) =
        let (fn, cfd) = Conv.cufdef_of_fdef tbl fd in
        let fd = 
          match Dead_code.dead_code_fd tokeep fn cfd with
          | Utils0.Ok cfd -> Conv.fdef_of_cufdef tbl (fn, cfd) 
          | Utils0.Error _ -> (* ignore the error !! *) fd
        in
        (extra,fd) in
      let fds = List.map deadcode fds in
      if !debug then
        Format.eprintf "After remove unused return @.%a@."
          (Printer.pp_prog ~debug:true) ([], (List.map snd fds));

      (* register allocation *)
      let fds = Regalloc.alloc_prog translate_var (fun sao -> sao.sao_has_stack) fds in

      let atbl = Hf.create 117 in 
      let mk_oas (sao, ro, fd) = 
        let extra =
          if sao.sao_has_stack && ro.ro_rsp = None then [V.clone rsp] 
          else [] in
        let alloc, size, extrapos = 
          StackAlloc.alloc_stack sao.sao_alloc extra in
        let saved_stack = 
          if sao.sao_has_stack then
            match ro.ro_rsp with
            | Some x -> Expr.SavedStackReg (Conv.cvar_of_var tbl x)
            | None   -> Expr.SavedStackStk (Conv.z_of_int (List.hd extrapos))
          else Expr.SavedStackNone in

        let conv_pi pi = 
          Stack_alloc.({
            pp_ptr = Conv.cvar_of_var tbl pi.pi_ptr;
            pp_writable = pi.pi_writable;
            pp_align    = pi.pi_align;
          }) in
        let conv_ptr_kind = function
          | Pstack(i, ws) -> Stack_alloc.Pstack (Conv.z_of_int i, ws)
          | Pregptr p     -> Stack_alloc.Pregptr(Conv.cvar_of_var tbl p);
          | Pstkptr i     -> Stack_alloc.Pstkptr(Conv.z_of_int i) in
        let conv_alloc (x,k) = Conv.cvar_of_var tbl x, conv_ptr_kind k in
        
        let sao = 
          Stack_alloc.({
            sao_size = Conv.z_of_int size;
            sao_params = List.map (omap conv_pi) sao.sao_params;
            sao_return = List.map (omap Conv.nat_of_int) sao.sao_return;
            sao_alloc  = List.map conv_alloc alloc; 
            sao_to_save = List.map (Conv.cvar_of_var tbl) ro.ro_to_save;
            sao_rsp  = saved_stack;
            sao_return_address = omap (Conv.cvar_of_var tbl) ro.ro_return_address;
          }) in
        Hf.add atbl fd.f_name sao in
      List.iter mk_oas fds;
      let data, alloc = StackAlloc.alloc_mem pmap (fst p) in
      let tog (x,(i,ws)) = (Conv.cvar_of_var tbl x, (Conv.z_of_int i, ws)) in
      Compiler.({
        ao_globals      = data;
        ao_global_alloc = List.map tog alloc;
        ao_stack_alloc  = 
          fun fn -> 
          try Hf.find atbl (Conv.fun_of_cfun tbl fn)
          with Not_found -> assert false
      })
         
    in

    let global_regalloc sp = 
      if !debug then Format.eprintf "START regalloc@.";
      let (fds,_data) = Conv.prog_of_csprog tbl sp in
      let fds = 
        Regalloc.alloc_prog translate_var (fun extra ->
            match extra.Expr.sf_save_stack with
            | Expr.SavedStackReg _ | Expr.SavedStackStk _ -> true
            | Expr.SavedStackNone -> false) fds in
      let fds = List.map (fun (y,_,x) -> y, x) fds in
      let fds = List.map (Conv.csfdef_of_fdef tbl) fds in
      Expr.({
        p_funcs = fds;
        p_globs = sp.p_globs;
        p_extra = sp.p_extra; }) in

    let is_var_in_memory cv : bool =
      let v = Conv.vari_of_cvari tbl cv |> L.unloc in
      is_stack_kind v.v_kind in

    let pp_cuprog fmt cp =
      let p = Conv.prog_of_cuprog tbl cp in
      Printer.pp_prog ~debug:true fmt p in

    let pp_csprog fmt cp =
      let p = Conv.prog_of_csprog tbl cp in
      Printer.pp_sprog ~debug:true tbl fmt p in

    let pp_linear fmt lp =
      PrintLinear.pp_prog tbl fmt lp in

    let rename_fd ii fn cfd =
      let ii,_ = Conv.get_iinfo tbl ii in
      let doit fd =
        let fd = Subst.clone_func fd in
        Subst.extend_iinfo ii fd in
      apply "rename_fd" doit fn cfd in

    let warning ii msg =
      let loc,_ = Conv.get_iinfo tbl ii in
      Format.eprintf "WARNING: at %a, %a@." Printer.pp_iloc loc Printer.pp_warning_msg msg;
      ii in

    let inline_var x =
      let x = Conv.var_of_cvar tbl x in
      x.v_kind = Inline in

   
    let is_glob x =
      let x = Conv.var_of_cvar tbl x in
      x.v_kind = Global in

    let fresh_id _gd x =
      let x = Conv.var_of_cvar tbl x in
      let x' = Prog.V.clone x in
      let cx = Conv.cvar_of_var tbl x' in
      cx.Var0.Var.vname in

    let var_alloc_prog up = 
      let (_glob,fds) = Conv.prog_of_cuprog tbl up in
      let fds = Regalloc.split_live_ranges fds in
      let fds = List.map (Conv.cufdef_of_fdef tbl) fds in
      Expr.({
        p_funcs = fds;
        p_globs = up.p_globs;
        p_extra = up.p_extra; }) in
 
    let share_stk_prog up = 
      let (_glob,fds) = Conv.prog_of_cuprog tbl up in
      let fds = List.map Varalloc.alloc_stack_fd fds in
      let fds = List.map (Conv.cufdef_of_fdef tbl) fds in
      Expr.({
        p_funcs = fds;
        p_globs = up.p_globs;
        p_extra = up.p_extra; }) in

    let removereturn sp = 
      let (fds,_data) = Conv.prog_of_csprog tbl sp in
      let tokeep = RemoveUnusedResults.analyse  fds in 
      let tokeep fn = tokeep (Conv.fun_of_cfun tbl fn) in
      tokeep in

    let is_reg_ptr x = 
      let x = Conv.var_of_cvar tbl x in
      is_reg_ptr_kind x.v_kind in
      
    let cparams = {
      Compiler.rename_fd    = rename_fd;
      Compiler.expand_fd    = apply "arr exp" Array_expand.arrexp_func;
      Compiler.var_alloc_prog = (*apply "var alloc" *) var_alloc_prog;
      Compiler.share_stk_prog = (*apply "share stk" *) share_stk_prog;
      Compiler.stk_pointer_name = Var0.Var.vname (Conv.cvar_of_var tbl Prog.rsp);
      Compiler.global_static_data_symbol = Var0.Var.vname (Conv.cvar_of_var tbl Prog.rip);
      Compiler.stackalloc    = memory_analysis;
      Compiler.removereturn  = removereturn;
      Compiler.regalloc      = global_regalloc;
      Compiler.lowering_vars = lowering_vars;
      Compiler.is_var_in_memory = is_var_in_memory;
      Compiler.print_uprog  = (fun s p -> eprint s pp_cuprog p; p);
      Compiler.print_sprog  = (fun s p -> eprint s pp_csprog p; p);
      Compiler.print_linear = (fun p -> eprint Compiler.Linearisation pp_linear p; p);
      Compiler.warning      = warning;
      Compiler.inline_var   = inline_var;
      Compiler.lowering_opt = Lowering.{ use_lea = !Glob_options.lea;
                                         use_set0 = !Glob_options.set0; };
      Compiler.is_glob     = is_glob;
      Compiler.fresh_id    = fresh_id;
      Compiler.is_reg_ptr  = is_reg_ptr;
    } in

    let entries =
      let ep = List.filter (fun fd -> fd.f_cc <> Internal) (snd prog) in
      List.map (fun fd -> Conv.cfun_of_fun tbl fd.f_name) ep in

    begin match
      Compiler.compile_prog_to_x86 cparams entries (Expr.to_uprog cprog) with
    | Utils0.Error e ->
      Utils.hierror "compilation error %a@."
         (pp_comp_ferr tbl) e
    | Utils0.Ok asm ->
      if !outfile <> "" then begin
        BatFile.with_file_out !outfile (fun out ->
          let fmt = BatFormat.formatter_of_out_channel out in
          Format.fprintf fmt "%a%!" (Ppasm.pp_prog tbl) asm);
          if !debug then Format.eprintf "assembly listing written@."
      end else if List.mem Compiler.Assembly !print_list then
          Format.printf "%a%!" (Ppasm.pp_prog tbl) asm
    end
  with
  | Utils.HiError s ->
      Format.eprintf "%s\n%!" s; exit 1

  | UsageError ->
      Arg.usage options usage_msg;
      exit 1;

  | Syntax.ParseError (loc, None) ->
      Format.eprintf "%s: parse error\n%!"
        (Location.tostring loc);
      exit 1

  | Syntax.ParseError (loc, Some msg) ->
      Format.eprintf "%s: parse error: %s\n%!"
        (Location.tostring loc) msg;
      exit 1

  | Typing.TyError (loc, code) ->
      Format.eprintf "%s: typing error: %a\n%!"
        (Location.tostring loc)
        Typing.pp_tyerror code;
      exit 1

(* -------------------------------------------------------------------- *)
let () = main ()
