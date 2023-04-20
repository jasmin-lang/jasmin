open Allocation
open Arch_extra
open Arch_params
open Array_copy
open Array_expansion
open Array_init
open Compiler_util
open Dead_calls
open Dead_code
open Eqtype
open Expr
open Inline
open Lowering
open MakeReferenceArguments
open Propagate_inline
open Remove_globals
open Utils0
open Compiler
open Utils
open Prog
open Glob_options


let compiler_first_part asm_e aparams cparams to_keep p =
  match array_copy_prog (asm_opI asm_e) cparams.fresh_counter
          (Equality.clone unit_eqType (Obj.magic unit_eqMixin) (fun x -> x))
          progUnit p with
  | Ok x ->
    let p0 = cparams.print_uprog ArrayCopy (Obj.magic x) in
    let p1 =
      add_init_prog (asm_opI asm_e) cparams.is_ptr
        (Equality.clone unit_eqType (Obj.magic unit_eqMixin) (fun x0 -> x0))
        progUnit (Obj.magic p0)
    in
    let p2 = cparams.print_uprog AddArrInit (Obj.magic p1) in
    (match inline_prog_err (Arch_extra.asm_opI asm_e) cparams.inline_var
             (Obj.magic cparams.rename_fd) (Obj.magic p2) with
     | Ok x0 ->
       let p3 = cparams.print_uprog Inlining (Obj.magic x0) in
       (match dead_calls_err_seq (asm_opI asm_e)
                (Equality.clone unit_eqType (Obj.magic unit_eqMixin)
                  (fun x1 -> x1)) progUnit to_keep (Obj.magic p3) with
        | Ok x1 ->
          let p4 = cparams.print_uprog RemoveUnusedFunction (Obj.magic x1) in
          (match unroll_loop (asm_opI asm_e) asm_e._asm._arch_decl.ad_fcp
                   aparams.ap_is_move_op (Obj.magic p4) with
           | Ok x2 ->
             let p5 = cparams.print_uprog Unrolling (Obj.magic x2) in
             let pv = split_live_ranges_prog asm_e cparams p5 in
             let pv0 = cparams.print_uprog Splitting pv in
             let pv1 = renaming_prog asm_e cparams pv0 in
             let pv2 = cparams.print_uprog Renaming pv1 in
             let pv3 = remove_phi_nodes_prog asm_e cparams pv2 in
             let pv4 = cparams.print_uprog RemovePhiNodes pv3 in
             (match check_uprog (asm_opI asm_e) (Obj.magic p5).p_extra
                      (Obj.magic p5).p_funcs (Obj.magic pv4).p_extra
                      (Obj.magic pv4).p_funcs with
              | Ok _ ->
                (match dead_code_prog (asm_opI asm_e) aparams.ap_is_move_op
                         (Equality.clone unit_eqType (Obj.magic unit_eqMixin)
                           (fun x3 -> x3)) progUnit (Obj.magic pv4) false with
                 | Ok x3 ->
                   let pv5 =
                     cparams.print_uprog DeadCode_Renaming (Obj.magic x3)
                   in
                   let pr =
                     remove_init_prog (asm_opI asm_e) cparams.is_reg_array
                       (Equality.clone unit_eqType (Obj.magic unit_eqMixin)
                         (fun x4 -> x4)) progUnit (Obj.magic pv5)
                   in
                   let pr0 = cparams.print_uprog RemoveArrInit (Obj.magic pr)
                   in
                   (match expand_prog (asm_opI asm_e)
                            (Obj.magic cparams.expand_fd) (Obj.magic pr0) with
                    | Ok x4 ->
                      let pe =
                        cparams.print_uprog RegArrayExpansion (Obj.magic x4)
                      in
                      (match remove_glob_prog (asm_opI asm_e) cparams.is_glob
                               cparams.fresh_id (Obj.magic pe) with
                       | Ok x5 ->
                         let pg =
                           cparams.print_uprog RemoveGlobal (Obj.magic x5)
                         in
                         (match makereference_prog (asm_opI asm_e)
                                  cparams.is_reg_ptr
                                  (Obj.magic cparams.fresh_reg_ptr)
                                  (Obj.magic pg) with
                          | Ok x6 ->
                            let pa =
                              cparams.print_uprog MakeRefArguments
                                (Obj.magic x6)
                            in
                            if aparams.ap_lop.lop_fvars_correct
                                 cparams.lowering_vars
                                 (Obj.magic unit_eqMixin) progUnit
                                 (Obj.magic pa).p_funcs
                            then let pl =
                                    lower_prog (asm_opI asm_e)
                                     (aparams.ap_lop.lop_lower_i
                                       cparams.is_regx) cparams.lowering_opt
                                     cparams.warning cparams.lowering_vars
                                     (Equality.clone unit_eqType
                                       (Obj.magic unit_eqMixin) (fun x8 ->
                                       x8)) progUnit cparams.is_var_in_memory
                                     (Obj.magic pa)
                                in
                                 let pl0 =
                                   cparams.print_uprog LowerInstruction
                                     (Obj.magic pl)
                                 in
                                 begin
                                   match pi_prog (Arch_extra.asm_opI asm_e)
                                          asm_e._asm._arch_decl.ad_fcp
                                          (Equality.clone unit_eqType
                                            (Obj.magic unit_eqMixin)
                                            (fun x7 -> x7)) progUnit
                                            (Obj.magic pl0) with
                                   | Ok x7 ->
                                     let pp =
                                       cparams.print_uprog PropagateInline
                                         (Obj.magic x7)
                                     in
                                     Ok pp
                                   | Error s -> Error s
                                 end
                            else let s =
                                   pp_internal_error_s
                                     ('l'::('o'::('w'::('e'::('r'::('i'::('n'::('g'::[]))))))))
                                     ('l'::('o'::('w'::('e'::('r'::('i'::('n'::('g'::(' '::('c'::('h'::('e'::('c'::('k'::(' '::('f'::('a'::('i'::('l'::('s'::[]))))))))))))))))))))
                                 in
                                 Error s
                          | Error s -> Error s)
                       | Error s -> Error s)
                    | Error s -> Error s)
                 | Error s -> Error s)
              | Error s -> Error s)
           | Error s -> Error s)
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s


let compiler_third_part asm_e aparams cparams entries ps =
  let rminfo = cparams.removereturn (Obj.magic ps) in
  (match check_removereturn entries rminfo with
   | Ok _ ->
     (match dead_code_prog_tokeep (asm_opI asm_e) aparams.ap_is_move_op false
              rminfo
              (Equality.clone sfe_eqType (Obj.magic sfe_eqMixin) (fun x -> x))
              (progStack (Arch_decl.arch_pd asm_e._asm._arch_decl)) ps with
      | Ok x ->
        let pr = cparams.print_sprog RemoveReturn (Obj.magic x) in
        let pa = { p_funcs = (cparams.regalloc pr.p_funcs); p_globs =
          pr.p_globs; p_extra = pr.p_extra }
        in
        let pa0 = cparams.print_sprog RegAllocation pa in
        (match Allocation.check_sprog (Arch_extra.asm_opI asm_e)
                 (Arch_decl.arch_pd asm_e._asm._arch_decl)
                 (Obj.magic pr).p_extra (Obj.magic pr).p_funcs
                 (Obj.magic pa0).p_extra (Obj.magic pa0).p_funcs  with
         | Ok _ ->
           (match dead_code_prog (asm_opI asm_e) aparams.ap_is_move_op
                    (Equality.clone sfe_eqType (Obj.magic sfe_eqMixin)
                      (fun x0 -> x0))
                    (progStack (Arch_decl.arch_pd asm_e._asm._arch_decl))
                    (Obj.magic pa0) true with
            | Ok x0 ->
              let pd =
                cparams.print_sprog DeadCode_RegAllocation (Obj.magic x0)
              in
              Ok (Obj.magic pd)
            | Error s -> Error s)
         | Error s -> Error s)
      | Error s -> Error s)
   | Error s -> Error s)

let check_export _ entries p =
  allM (fun fn ->
    match get_fundef p.p_funcs (Obj.magic fn) with
    | Some fd ->
      if eq_op return_address_location_eqType
           (Obj.magic (Obj.magic fd).f_extra.sf_return_address)
           (Obj.magic RAnone)
      then Ok ()
      else Error
             (pp_at_fn (Obj.magic fn)
               (Merge_varmaps.E.gen_error true None
                 (pp_s
                   ('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('s'::(' '::('a'::(' '::('r'::('e'::('t'::('u'::('r'::('n'::(' '::('a'::('d'::('d'::('r'::('e'::('s'::('s'::[])))))))))))))))))))))))))))))))))))))))))))
    | None ->
      Error
        (pp_at_fn (Obj.magic fn)
          (Merge_varmaps.E.gen_error true None
            (pp_s
              ('u'::('n'::('k'::('n'::('o'::('w'::('n'::(' '::('e'::('x'::('p'::('o'::('r'::('t'::(' '::('f'::('u'::('n'::('c'::('t'::('i'::('o'::('n'::[])))))))))))))))))))))))))))
    entries

let compiler_back_end asm_e call_conv aparams cparams entries pd =
  match check_export asm_e entries pd with
  | Ok _ ->
    (match Merge_varmaps.check (Arch_decl.arch_pd asm_e._asm._arch_decl) (asm_opI asm_e)
             (Asm_gen.ovm_i asm_e._asm._arch_decl call_conv) pd
             cparams.extra_free_registers (var_tmp asm_e aparams) with
     | Ok _ ->
       (match Linearization.linear_prog (Arch_decl.arch_pd asm_e._asm._arch_decl) (asm_opI asm_e)
                aparams.ap_lip pd with
        | Ok x ->
          let pl = cparams.print_linear Linearization x in
          (match Tunneling.tunnel_program (asm_opI asm_e) pl with
           | Ok x0 -> let pl0 = cparams.print_linear Tunneling x0 in Ok pl0
           | Error s -> Error s)
        | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s


module Scmp = struct
  type t = string
  let compare = compare
end

module Ss = Set.Make(Scmp)

let filter prog tbl cl_list =
  let rec used_func f =
    let (_,fundef) = f in
    used_func_c Ss.empty Linear.(fundef.lfd_body)

  and used_func_c used c =
    List.fold_left used_func_i used c

  and used_func_i used i =
    match i.li_i with
    | Lcall (_,(f,_))   -> Ss.add (Conv.string_of_funname tbl f) used
    | _ -> used
  in

  let tokeep = ref (Ss.of_list cl_list) in
  let dofun f =
    let (name,_) = f in
    if Ss.mem (Conv.string_of_funname tbl name) !tokeep then
      (tokeep := Ss.union (used_func f) !tokeep; true)
    else false in
  let lp_funcs = List.rev (List.filter dofun Linear.(prog.lp_funcs)) in
  Linear.({prog with lp_funcs})

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
  | Ccall _ | Csyscall _ | Cassert _ -> ()

let warn_extra_fd asmOp (_, fd) = List.iter (warn_extra_i asmOp) fd.f_body

let extract (type reg regx xreg rflag cond asm_op extra_op)
    (module Arch : Arch_full.Arch
      with type reg = reg
       and type regx = regx
       and type xreg = xreg
       and type rflag = rflag
       and type cond = cond
       and type asm_op = asm_op
       and type extra_op = extra_op) visit_prog_after_pass fmt prog tbl cprog tokeep =

  let asmOp = Arch.asmOp in
  let asm_e = Arch.asm_e in
  let call_conv = Arch.call_conv in
  let p = (Expr.to_uprog asmOp cprog) in

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
          !saved_extra_free_registers loc |> Option.map (Conv.cvar_of_var tbl));
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

  let aparams = Arch.aparams in
  
  match compiler_first_part asm_e aparams cparams (Seq.cat export_functions subroutines) p with
  | Ok x ->
    (* let up = Conv.prog_of_cuprog tbl x in *)
    (* Printer.pp_prog ~debug:false asmOp fmt up; *)
    let ao = cparams.stackalloc (Obj.magic x) in
    (match check_no_ptr (Obj.magic export_functions) ao.ao_stack_alloc with
     | Ok _ ->
       (match Stack_alloc.alloc_prog (Arch_decl.arch_pd asm_e._asm._arch_decl) (asm_opI asm_e) true
                (aparams.ap_sap cparams.is_regx) cparams.fresh_reg
                cparams.global_static_data_symbol
                cparams.stack_register_symbol ao.ao_globals
                ao.ao_global_alloc ao.ao_stack_alloc (Obj.magic x) with
       | Ok x0 ->
         let ps = cparams.print_sprog StackAllocation x0 in
         (match compiler_third_part asm_e aparams cparams export_functions
                  (Obj.magic ps) with
         | Ok x1 ->
           (match compiler_back_end asm_e call_conv aparams cparams (Obj.magic export_functions) x1 with
            | Ok x ->
              let x = filter x tbl tokeep in
              PrintLinear.pp_prog asmOp tbl fmt x;
              Ok x
            | Error s -> Error s)
         | Error s -> Error s)
       | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s
