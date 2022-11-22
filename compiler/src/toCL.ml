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
                                     aparams.ap_lop.lop_lower_i
                                     cparams.lowering_opt cparams.warning
                                     cparams.lowering_vars
                                     (Equality.clone unit_eqType
                                       (Obj.magic unit_eqMixin) (fun x7 ->
                                       x7)) progUnit cparams.is_var_in_memory
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
                aparams.ap_lip pd cparams.extra_free_registers with
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
    | Lcall (f,_)   -> Ss.add (Conv.string_of_funname tbl f) used
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


let extract asmOp fmt asm_e p aparams cparams entries subroutines tbl call_conv tokeep =
  match compiler_first_part asm_e aparams cparams (Seq.cat entries subroutines) p with
  | Ok x ->
    (* let up = Conv.prog_of_cuprog tbl x in *)
    (* Printer.pp_prog ~debug:false asmOp fmt up; *)
    let ao = cparams.stackalloc (Obj.magic x) in
    (match check_no_ptr (Obj.magic entries) ao.ao_stack_alloc with
     | Ok _ ->
       (match Stack_alloc.alloc_prog (Arch_decl.arch_pd asm_e._asm._arch_decl) (asm_opI asm_e) true
                (aparams.ap_sap cparams.is_regx) cparams.fresh_reg
                cparams.global_static_data_symbol
                cparams.stack_register_symbol ao.ao_globals
                ao.ao_global_alloc ao.ao_stack_alloc (Obj.magic x) with
       | Ok x0 ->
         let ps = cparams.print_sprog StackAllocation x0 in
         (match compiler_third_part asm_e aparams cparams entries
                  (Obj.magic ps) with
         | Ok x1 ->
           (match compiler_back_end asm_e call_conv aparams cparams (Obj.magic entries) x1 with
            | Ok x ->
              let x = filter x tbl tokeep in
              PrintLinear.pp_prog asmOp tbl fmt x;
              Ok x
            | Error s -> Error s)
         | Error s -> Error s)
       | Error s -> Error s)
     | Error s -> Error s)
  | Error s -> Error s
