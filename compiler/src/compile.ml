open Utils
open Prog
open Glob_options

let preprocess reg_size asmOp p =
  let p =
    p |> Subst.remove_params |> Insert_copy_and_fix_length.doit reg_size
  in
  Typing.check_prog reg_size asmOp p;
  p

(* -------------------------------------------------------------------- *)

let parse_file reg_size asmOp_sopn fname =
  let env =
    List.fold_left Pretyping.Env.add_from Pretyping.Env.empty
      !Glob_options.idirs
  in
  Pretyping.tt_program reg_size asmOp_sopn env fname

(* -------------------------------------------------------------------- *)
let rec warn_extra_i asmOp i =
  match i.i_desc with
  | Cassgn (_, tag, _, _) | Copn (_, tag, _, _) -> (
      match tag with
      | AT_rename ->
          warning ExtraAssignment i.i_loc
            "@[<v>extra assignment introduced:@;<0 2>%a@]"
            (Printer.pp_instr ~debug:false asmOp)
            i
      | AT_inline ->
          hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
            "@[<v>AT_inline flag remains in instruction:@;<0 2>@[%a@]@]"
            (Printer.pp_instr ~debug:false asmOp)
            i
      | _ -> ())
  | Cif (_, c1, c2) | Cwhile (_, c1, _, c2) ->
      List.iter (warn_extra_i asmOp) c1;
      List.iter (warn_extra_i asmOp) c2
  | Cfor _ ->
      hierror ~loc:(Lmore i.i_loc) ~kind:"compilation error" ~internal:true
        "for loop remains"
  | Ccall _ | Csyscall _ -> ()

let warn_extra_fd asmOp (_, fd) = List.iter (warn_extra_i asmOp) fd.f_body

(*--------------------------------------------------------------------- *)

let compile (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) visit_prog_after_pass prog tbl cprog =
  let module Regalloc = Regalloc.Regalloc (Arch) in
  let module StackAlloc = StackAlloc.StackAlloc (Arch) in
  let fdef_of_cufdef fn cfd = Conv.fdef_of_cufdef tbl (fn, cfd) in
  let cufdef_of_fdef fd = snd (Conv.cufdef_of_fdef tbl fd) in

  let apply msg trans fn cfd =
    if !debug then Format.eprintf "START %s@." msg;
    let fd = fdef_of_cufdef fn cfd in
    if !debug then Format.eprintf "back to ocaml@.";
    let fd = trans fd in
    cufdef_of_fdef fd
  in

  let translate_var = Conv.var_of_cvar tbl in

  let memory_analysis up : Compiler.stack_alloc_oracles =
    StackAlloc.memory_analysis
      (Printer.pp_err ~debug:!debug)
      ~debug:!debug tbl up
  in

  let saved_extra_free_registers : (L.i_loc -> var option) ref =
    ref (fun _ -> None)
  in

  let global_regalloc fds =
    if !debug then Format.eprintf "START regalloc@.";
    let fds = List.map (Conv.fdef_of_csfdef tbl) fds in

    CheckAnnot.check_stack_size fds;

    let fds, extra_free_registers =
      Regalloc.alloc_prog translate_var
        (fun _fd extra ->
          match extra.Expr.sf_save_stack with
          | Expr.SavedStackReg _ | Expr.SavedStackStk _ -> true
          | Expr.SavedStackNone -> false)
        fds
    in
    saved_extra_free_registers := extra_free_registers;
    let fds = List.map (fun (y, _, x) -> (y, x)) fds in
    let fds = List.map (Conv.csfdef_of_fdef tbl) fds in
    fds
  in

  let is_var_in_memory cv : bool =
    let v = Conv.vari_of_cvari tbl cv |> L.unloc in
    match v.v_kind with
    | Stack _ | Reg (_, Pointer _) | Global -> true
    | Const | Inline | Reg (_, Direct) -> false
  in

  let pp_cuprog s cp =
    Conv.prog_of_cuprog tbl cp |> visit_prog_after_pass ~debug:true s
  in

  let pp_csprog fmt cp =
    let p = Conv.prog_of_csprog tbl cp in
    Printer.pp_sprog ~debug:true tbl Arch.asmOp fmt p
  in

  let pp_linear fmt lp = PrintLinear.pp_prog Arch.asmOp tbl fmt lp in

  let rename_fd ii fn cfd =
    let ii, _ = ii in
    let doit fd =
      let fd = Subst.clone_func fd in
      Subst.extend_iinfo ii fd
    in
    apply "rename_fd" doit fn cfd
  in

  let expand_fd fn cfd =
    let fd = Conv.fdef_of_cufdef tbl (fn, cfd) in
    let vars, harrs = Array_expand.init_tbl fd in
    let cvar = Conv.cvar_of_var tbl in
    let vars = List.map cvar (Sv.elements vars) in
    let arrs = ref [] in
    let doarr x (ws, xs) =
      arrs :=
        Array_expansion.
          {
            vi_v = cvar x;
            vi_s = ws;
            vi_n =
              List.map (fun x -> (cvar x).Var0.Var.vname) (Array.to_list xs);
          }
        :: !arrs
    in
    Hv.iter doarr harrs;
    { Array_expansion.vars; arrs = !arrs }
  in

  let warning ii msg =
    (if not !Glob_options.lea then
     let loc, _ = ii in
     warning UseLea loc "%a" Printer.pp_warning_msg msg);
    ii
  in

  let inline_var x =
    let x = Conv.var_of_cvar tbl x in
    x.v_kind = Inline
  in

  let is_glob x =
    let x = Conv.var_of_cvar tbl x in
    x.v_kind = Global
  in

  let fresh_id _gd x =
    let x = Conv.var_of_cvar tbl x in
    let x' = Prog.V.clone x in
    let cx = Conv.cvar_of_var tbl x' in
    cx.Var0.Var.vname
  in

  let fresh_reg name ty =
    let name = Conv.string_of_string0 name in
    let ty = Conv.ty_of_cty ty in
    let p = Prog.V.mk name (Reg (Normal, Direct)) ty L._dummy [] in
    let cp = Conv.cvar_of_var tbl p in
    cp.Var0.Var.vname
  in

  let fresh_counter =
    let i = Prog.V.mk "i__copy" Inline tint L._dummy [] in
    let ci = Conv.cvar_of_var tbl i in
    ci.Var0.Var.vname
  in

  let split_live_ranges_fd fd = Regalloc.split_live_ranges fd in
  let renaming_fd fd = Regalloc.renaming fd in
  let remove_phi_nodes_fd fd = Regalloc.remove_phi_nodes fd in

  let removereturn sp =
    let fds, _data = Conv.prog_of_csprog tbl sp in
    let tokeep = RemoveUnusedResults.analyse Arch.aparams.ap_is_move_op fds in
    let tokeep fn = tokeep (Conv.fun_of_cfun tbl fn) in
    tokeep
  in

  let is_regx tbl x = is_regx (Conv.var_of_cvar tbl x) in

  let is_reg_ptr x =
    let x = Conv.var_of_cvar tbl x in
    is_reg_ptr_kind x.v_kind
  in

  let is_ptr x =
    let x = Conv.var_of_cvar tbl x in
    is_ptr x.v_kind
  in

  let is_reg_array x = is_reg_arr (Conv.var_of_cvar tbl x) in

  let warn_extra s p =
    if s = Compiler.DeadCode_RegAllocation then
      let fds, _ = Conv.prog_of_csprog tbl p in
      List.iter (warn_extra_fd Arch.asmOp) fds
  in

  let cparams =
    {
      Compiler.rename_fd;
      Compiler.expand_fd;
      Compiler.split_live_ranges_fd =
        apply "split live ranges" split_live_ranges_fd;
      Compiler.renaming_fd = apply "alloc inline assgn" renaming_fd;
      Compiler.remove_phi_nodes_fd =
        apply "remove phi nodes" remove_phi_nodes_fd;
      Compiler.stack_register_symbol =
        Var0.Var.vname (Conv.cvar_of_var tbl Arch.rsp_var);
      Compiler.global_static_data_symbol =
        Var0.Var.vname (Conv.cvar_of_var tbl Arch.rip);
      Compiler.stackalloc = memory_analysis;
      Compiler.removereturn;
      Compiler.regalloc = global_regalloc;
      Compiler.extra_free_registers =
        (fun ii ->
          let loc, _ = ii in
          !saved_extra_free_registers loc |> omap (Conv.cvar_of_var tbl));
      Compiler.lowering_vars = Arch.lowering_vars tbl;
      Compiler.is_var_in_memory;
      Compiler.print_uprog =
        (fun s p ->
          pp_cuprog s p;
          p);
      Compiler.print_sprog =
        (fun s p ->
          warn_extra s p;
          eprint s pp_csprog p;
          p);
      Compiler.print_linear =
        (fun s p ->
          eprint s pp_linear p;
          p);
      Compiler.warning;
      Compiler.inline_var;
      Compiler.lowering_opt = Arch.lowering_opt;
      Compiler.is_glob;
      Compiler.fresh_id;
      Compiler.fresh_counter;
      Compiler.fresh_reg;
      Compiler.fresh_reg_ptr = Conv.fresh_reg_ptr tbl;
      Compiler.is_reg_ptr;
      Compiler.is_ptr;
      Compiler.is_reg_array;
      Compiler.is_regx = is_regx tbl;
    }
  in

  let export_functions, subroutines =
    let conv fd = Conv.cfun_of_fun tbl fd.f_name in
    List.fold_right
      (fun fd ((e, i) as acc) ->
        match fd.f_cc with
        | Export -> (conv fd :: e, i)
        | Internal -> acc
        | Subroutine _ -> (e, conv fd :: i))
      (snd prog) ([], [])
  in

  Compiler.compile_prog_to_asm Arch.asm_e Arch.call_conv Arch.aparams cparams
    export_functions subroutines
    (Expr.to_uprog Arch.asmOp cprog)

(*--------------------------------------------------------------------- *)
(* FIXME: how to share the initialization of the compiler, i.e cparams  *)

let compile_CL (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) tbl cprog toextract =
  let visit_prog_after_pass ~debug s p = 
    eprint s (Printer.pp_prog ~debug Arch.asmOp) p in

  let module Regalloc = Regalloc.Regalloc (Arch) in
  let module StackAlloc = StackAlloc.StackAlloc (Arch) in
  let fdef_of_cufdef fn cfd = Conv.fdef_of_cufdef tbl (fn, cfd) in
  let cufdef_of_fdef fd = snd (Conv.cufdef_of_fdef tbl fd) in

  let apply msg trans fn cfd =
    if !debug then Format.eprintf "START %s@." msg;
    let fd = fdef_of_cufdef fn cfd in
    if !debug then Format.eprintf "back to ocaml@.";
    let fd = trans fd in
    cufdef_of_fdef fd
  in

  let translate_var = Conv.var_of_cvar tbl in

  let memory_analysis up : Compiler.stack_alloc_oracles =
    StackAlloc.memory_analysis
      (Printer.pp_err ~debug:!debug)
      ~debug:!debug tbl up
  in

  let saved_extra_free_registers : (L.i_loc -> var option) ref =
    ref (fun _ -> None)
  in

  let global_regalloc fds =
    if !debug then Format.eprintf "START regalloc@.";
    let fds = List.map (Conv.fdef_of_csfdef tbl) fds in

    CheckAnnot.check_stack_size fds;

    let fds, extra_free_registers =
      Regalloc.alloc_prog translate_var
        (fun _fd extra ->
          match extra.Expr.sf_save_stack with
          | Expr.SavedStackReg _ | Expr.SavedStackStk _ -> true
          | Expr.SavedStackNone -> false)
        fds
    in
    saved_extra_free_registers := extra_free_registers;
    let fds = List.map (fun (y, _, x) -> (y, x)) fds in
    let fds = List.map (Conv.csfdef_of_fdef tbl) fds in
    fds
  in

  let is_var_in_memory cv : bool =
    let v = Conv.vari_of_cvari tbl cv |> L.unloc in
    match v.v_kind with
    | Stack _ | Reg (_, Pointer _) | Global -> true
    | Const | Inline | Reg (_, Direct) -> false
  in

  let pp_cuprog s cp = 
    Conv.prog_of_cuprog tbl cp |> visit_prog_after_pass ~debug:true s 
  in

  let pp_csprog fmt cp =
    let p = Conv.prog_of_csprog tbl cp in
    Printer.pp_sprog ~debug:true tbl Arch.asmOp fmt p
  in

  let pp_linear fmt lp = PrintLinear.pp_prog Arch.asmOp tbl fmt lp in

  let rename_fd ii fn cfd =
    let ii, _ = ii in
    let doit fd =
      let fd = Subst.clone_func fd in
      Subst.extend_iinfo ii fd
    in
    apply "rename_fd" doit fn cfd
  in

  let expand_fd fn cfd =
    let fd = Conv.fdef_of_cufdef tbl (fn, cfd) in
    let vars, harrs = Array_expand.init_tbl fd in
    let cvar = Conv.cvar_of_var tbl in
    let vars = List.map cvar (Sv.elements vars) in
    let arrs = ref [] in
    let doarr x (ws, xs) =
      arrs :=
        Array_expansion.
          {
            vi_v = cvar x;
            vi_s = ws;
            vi_n =
              List.map (fun x -> (cvar x).Var0.Var.vname) (Array.to_list xs);
          }
        :: !arrs
    in
    Hv.iter doarr harrs;
    { Array_expansion.vars; arrs = !arrs }
  in

  let warning ii msg =
    (if not !Glob_options.lea then
     let loc, _ = ii in
     warning UseLea loc "%a" Printer.pp_warning_msg msg);
    ii
  in

  let inline_var x =
    let x = Conv.var_of_cvar tbl x in
    x.v_kind = Inline
  in

  let is_glob x =
    let x = Conv.var_of_cvar tbl x in
    x.v_kind = Global
  in

  let fresh_id _gd x =
    let x = Conv.var_of_cvar tbl x in
    let x' = Prog.V.clone x in
    let cx = Conv.cvar_of_var tbl x' in
    cx.Var0.Var.vname
  in

  let fresh_reg name ty =
    let name = Conv.string_of_string0 name in
    let ty = Conv.ty_of_cty ty in
    let p = Prog.V.mk name (Reg (Normal, Direct)) ty L._dummy [] in
    let cp = Conv.cvar_of_var tbl p in
    cp.Var0.Var.vname
  in

  let fresh_counter =
    let i = Prog.V.mk "i__copy" Inline tint L._dummy [] in
    let ci = Conv.cvar_of_var tbl i in
    ci.Var0.Var.vname
  in

  let split_live_ranges_fd fd = Regalloc.split_live_ranges fd in
  let renaming_fd fd = Regalloc.renaming fd in
  let remove_phi_nodes_fd fd = Regalloc.remove_phi_nodes fd in

  let removereturn sp =
    let fds, _data = Conv.prog_of_csprog tbl sp in
    let tokeep = RemoveUnusedResults.analyse Arch.aparams.ap_is_move_op fds in
    let tokeep fn = tokeep (Conv.fun_of_cfun tbl fn) in
    tokeep
  in

  let is_regx tbl x = is_regx (Conv.var_of_cvar tbl x) in

  let is_reg_ptr x =
    let x = Conv.var_of_cvar tbl x in
    is_reg_ptr_kind x.v_kind
  in

  let is_ptr x =
    let x = Conv.var_of_cvar tbl x in
    is_ptr x.v_kind
  in

  let is_reg_array x = is_reg_arr (Conv.var_of_cvar tbl x) in

  let warn_extra s p =
    if s = Compiler.DeadCode_RegAllocation then
      let fds, _ = Conv.prog_of_csprog tbl p in
      List.iter (warn_extra_fd Arch.asmOp) fds
  in

  let cparams =
    {
      Compiler.rename_fd;
      Compiler.expand_fd;
      Compiler.split_live_ranges_fd =
        apply "split live ranges" split_live_ranges_fd;
      Compiler.renaming_fd = apply "alloc inline assgn" renaming_fd;
      Compiler.remove_phi_nodes_fd =
        apply "remove phi nodes" remove_phi_nodes_fd;
      Compiler.stack_register_symbol =
        Var0.Var.vname (Conv.cvar_of_var tbl Arch.rsp_var);
      Compiler.global_static_data_symbol =
        Var0.Var.vname (Conv.cvar_of_var tbl Arch.rip);
      Compiler.stackalloc = memory_analysis;
      Compiler.removereturn;
      Compiler.regalloc = global_regalloc;
      Compiler.extra_free_registers =
        (fun ii ->
          let loc, _ = ii in
          !saved_extra_free_registers loc |> omap (Conv.cvar_of_var tbl));
      Compiler.lowering_vars = Arch.lowering_vars tbl;
      Compiler.is_var_in_memory;
      Compiler.print_uprog =
        (fun s p ->
          pp_cuprog s p;
          p);
      Compiler.print_sprog =
        (fun s p ->
          warn_extra s p;
          eprint s pp_csprog p;
          p);
      Compiler.print_linear =
        (fun s p ->
          eprint s pp_linear p;
          p);
      Compiler.warning;
      Compiler.inline_var;
      Compiler.lowering_opt = Arch.lowering_opt;
      Compiler.is_glob;
      Compiler.fresh_id;
      Compiler.fresh_counter;
      Compiler.fresh_reg;
      Compiler.fresh_reg_ptr = Conv.fresh_reg_ptr tbl;
      Compiler.is_reg_ptr;
      Compiler.is_ptr;
      Compiler.is_reg_array;
      Compiler.is_regx = is_regx tbl;
    }
  in

  (* Fix cparams to expand all array *)
  let expand_fd fn cfd =
    let fd = Conv.fdef_of_cufdef tbl (fn, cfd) in
    let vars, harrs = Array_expand.init_tbl ~onlyreg:false fd in
    let cvar = Conv.cvar_of_var tbl in
    let vars = List.map cvar (Sv.elements vars) in
    let arrs = ref [] in
    let doarr x (ws, xs) =
      arrs :=
        Array_expansion.
          {
            vi_v = cvar x;
            vi_s = ws;
            vi_n =
              List.map (fun x -> (cvar x).Var0.Var.vname) (Array.to_list xs);
          }
        :: !arrs
    in
    Hv.iter doarr harrs;
    { Array_expansion.vars; arrs = !arrs }
  in

  (* Add array copy after inlining every where *)
  let is_array_init e = 
    match e with
    | Parr_init _ -> true
    | _ -> false in

  let rec add_array_copy_i i = 
    { i with i_desc = add_array_copy_id i.i_desc }

  and add_array_copy_id i = 
  match i with
  | Cif(e,c1,c2) -> Cif(e, add_array_copy_c c1, add_array_copy_c c2)
  | Cfor(x,r,c)  -> Cfor(x,r, add_array_copy_c c)
  | Cwhile(a,c1,e,c2) -> Cwhile(a, add_array_copy_c c1, e, add_array_copy_c c2)
  | Cassgn(Lvar x, t, _ty, e) when is_arr x.pl_desc && not (is_array_init e) ->
      let (ws,n) = array_kind x.pl_desc.v_ty in
      Copn([Lvar x],t, Ocopy(ws, Conv.pos_of_int n), [e])
  | Cassgn(Lasub (_, ws, n,_, _) as x, t, _ty, e) when not (is_array_init e) ->
      Copn([x],t, Ocopy(ws, Conv.pos_of_int n), [e])
  | Ccall _ | Copn _ | Csyscall _ | Cassgn _ -> i

  and add_array_copy_c c = 
    List.map add_array_copy_i c in

  let add_array_copy_f f = 
   { f with f_body = add_array_copy_c f.f_body } in
  let add_array_copy (g,fds) = (g, List.map add_array_copy_f fds) in  

  let cparams = {
      cparams with
      Compiler.is_reg_array = 
        (fun x -> is_arr (Conv.var_of_cvar tbl x));
      Compiler.expand_fd
    } in

  let doit f p = 
    match f p with
    | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:!debug tbl) tbl e in
      raise (HiError e)
    | Utils0.Ok p -> p in

  let cprog =   
    doit 
      (Compiler.compiler_CL_first_part Arch.asm_e Arch.aparams cparams
         [Conv.cfun_of_fun tbl toextract])
      (Expr.to_uprog Arch.asmOp cprog) in
     
  let cprog = 
    let p = Conv.prog_of_cuprog tbl (Obj.magic cprog) in
    Format.eprintf "Before add copy@.%a@." (Printer.pp_prog ~debug:true Arch.asmOp) p; 
    let p = add_array_copy p in
    Format.eprintf "After add copy@.%a@." (Printer.pp_prog ~debug:true Arch.asmOp) p; 
    let cp = Conv.cprog_of_prog tbl p in
    cp in      
  doit (Compiler.compiler_CL_second_part Arch.asm_e Arch.aparams cparams)
      (Expr.to_uprog Arch.asmOp cprog)
