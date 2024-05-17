open Utils
open Wsize
open Prog
open Regalloc

let pp_var = Printer.pp_var ~debug:true

let pp_var_ty fmt x =
 Format.fprintf fmt "%a %a" PrintCommon.pp_ty x.v_ty pp_var x

let pp_param_info fmt pi =
  let open Stack_alloc in
  match pi with
  | None -> Format.fprintf fmt "_"
  | Some pi ->
    Format.fprintf fmt "%s %a aligned on %s"
      (if pi.pp_writable then "mut" else "const")
      pp_var_ty (Conv.var_of_cvar pi.pp_ptr)
      (string_of_ws pi.pp_align)

let pp_slot fmt ((x, ws), ofs) =
  Format.fprintf fmt "%a: %a aligned on %s"
    Z.pp_print (Conv.z_of_cz ofs)
    pp_var_ty (Conv.var_of_cvar x)
    (string_of_ws ws)

let pp_zone fmt z =
  let open Stack_alloc in
  Format.fprintf fmt "[%a:%a]"
    Z.pp_print (Conv.z_of_cz z.z_ofs)
    Z.pp_print (Conv.z_of_cz z.z_len)

let pp_ptr_kind_init fmt pki =
  let open Stack_alloc in
  match pki with
  | PIdirect (v, z, sc) ->
    Format.fprintf fmt "%s %a %a"
      (if sc = Sglob then "global" else "stack")
      pp_var (Conv.var_of_cvar v)
      pp_zone z
  | PIregptr v ->
    Format.fprintf fmt "reg ptr %a"
      pp_var (Conv.var_of_cvar v)
  | PIstkptr (v, z, x) ->
    Format.fprintf fmt "stack ptr %a %a (pseudo-reg %a)"
      pp_var_ty (Conv.var_of_cvar v)
      pp_zone z
      pp_var_ty (Conv.var_of_cvar x)

let pp_alloc fmt (x, pki) =
    Format.fprintf fmt "%a -> %a" pp_var (Conv.var_of_cvar x) (pp_ptr_kind_init) pki

let pp_return fmt n =
  match n with
  | None -> Format.fprintf fmt "_"
  | Some n -> Format.fprintf fmt "%d" (Conv.int_of_nat n)

let pp_sao fmt sao =
  let open Stack_alloc in
  let max_size = Conv.z_of_cz sao.sao_max_size in
  let total_size =
    (* if the function is export, we must take into account the alignment
       of the stack *)
    match sao.sao_return_address with
    | RAnone -> Z.add max_size (Z.of_int (size_of_ws sao.sao_align - 1))
    | _ -> max_size
  in
  Format.fprintf fmt "alignment = %s@;size = %a; ioff = %a; extra size = %a@;max size = %a; total size = %a@;max call depth = %a@;params =@;<2 2>@[<v>%a@]@;return = @[<hov>%a@]@;slots =@;<2 2>@[<v>%a@]@;alloc= @;<2 2>@[<v>%a@]@;saved register = @[<hov>%a@]@;saved stack = %a@;return address = %a"
    (string_of_ws sao.sao_align)
    Z.pp_print (Conv.z_of_cz sao.sao_size)
    Z.pp_print (Conv.z_of_cz sao.sao_ioff)
    Z.pp_print (Conv.z_of_cz sao.sao_extra_size)
    Z.pp_print max_size
    Z.pp_print total_size
    Z.pp_print (Conv.z_of_cz sao.sao_max_call_depth)
    (pp_list "@;" pp_param_info) sao.sao_params
    (pp_list "@;" pp_return) sao.sao_return
    (pp_list "@;" pp_slot) sao.sao_slots
    (pp_list "@;" pp_alloc) sao.sao_alloc
    (pp_list "@;" (Printer.pp_to_save ~debug:true)) sao.sao_to_save
    (Printer.pp_saved_stack ~debug:true) sao.sao_rsp
    (Printer.pp_return_address ~debug:true) sao.sao_return_address

let pp_oracle up fmt saos =
  let open Compiler in
  let { ao_globals; ao_global_alloc; ao_stack_alloc } = saos in
  let pp_global fmt global =
    Format.fprintf fmt "%a" Z.pp_print (Conv.z_of_word U8 global)
  in
  let pp_stack_alloc fmt f =
    let sao = ao_stack_alloc f.f_name in
    Format.fprintf fmt "@[<v 2>%s@;%a@]" f.f_name.fn_name pp_sao sao
  in
  let _, fs = Conv.prog_of_cuprog up in
  Format.fprintf fmt "@[<v>Global data:@;<2 2>@[<hov>%a@]@;Global slots:@;<2 2>@[<v>%a@]@;Stack alloc:@;<2 2>@[<v>%a@]@]"
    (pp_list "@;" pp_global) ao_globals
    (pp_list "@;" pp_slot) ao_global_alloc
    (pp_list "@;" pp_stack_alloc) fs

module StackAlloc (Arch: Arch_full.Arch) = struct

module Regalloc = Regalloc (Arch)

let memory_analysis pp_err ~debug up =
  if debug then Format.eprintf "START memory analysis@.";
  let p = Conv.prog_of_cuprog up in
  let gao, sao = Varalloc.alloc_stack_prog Arch.callstyle Arch.reg_size p in
  
  (* build coq info *)
  let crip = Var0.Var.vname (Conv.cvar_of_var Arch.rip) in
  let crsp = Var0.Var.vname (Conv.cvar_of_var Arch.rsp_var) in
  let do_slots slots = 
    List.map (fun (x,ws,ofs) -> ((Conv.cvar_of_var x, ws), Conv.cz_of_int ofs)) slots in
  let cglobs = do_slots gao.gao_slots in
  
  let mk_csao fn = 
    let sao = Hf.find sao fn in
    let align = sao.sao_align in
    let size = sao.sao_size in
    let conv_pi (pi:Varalloc.param_info) = 
      Stack_alloc.({
        pp_ptr = Conv.cvar_of_var pi.pi_ptr;
        pp_writable = pi.pi_writable;
        pp_align    = pi.pi_align.ac_strict;
      }) in
    let conv_sub (i:Interval.t) = 
      Stack_alloc.{ z_ofs = Conv.cz_of_int i.min; 
                    z_len = Conv.cz_of_int (Interval.size i) } in
    let conv_ptr_kind x = function
      | Varalloc.Direct (s, i, sc) -> Stack_alloc.PIdirect (Conv.cvar_of_var s, conv_sub i, sc)
      | RegPtr s                   -> Stack_alloc.PIregptr(Conv.cvar_of_var s)
      | StackPtr s                 ->
        let xp = V.clone x in
        Stack_alloc.PIstkptr(Conv.cvar_of_var s,
                             conv_sub Interval.{min = 0; max = size_of_ws Arch.reg_size}, Conv.cvar_of_var xp) in
  
    let conv_alloc (x,k) = Conv.cvar_of_var x, conv_ptr_kind x k in
  
    let sao = Stack_alloc.{
        sao_align  = align;
        sao_size   = Conv.cz_of_int size;
        sao_ioff   = Z0;
        sao_extra_size = Z0;
        sao_max_size = Z0;
        sao_max_call_depth = Z0;
        sao_params = List.map (Option.map conv_pi) sao.sao_params;
        sao_return = List.map (Option.map Conv.nat_of_int) sao.sao_return;
        sao_slots  = do_slots sao.sao_slots;
        sao_alloc  = List.map conv_alloc (Hv.to_list sao.sao_alloc); 
        sao_to_save = [];
        sao_rsp     = SavedStackNone; 
        sao_return_address = RAnone;
        } in 
    sao in
  
  let atbl = Hf.create 117 in 
  let get_sao fn = 
    try Hf.find atbl fn 
    with Not_found -> 
      let csao = mk_csao fn in
      Hf.add atbl fn csao;
      csao in
  
  if debug && !Glob_options.print_stack_alloc then begin
    let saos =
      Compiler.({
        ao_globals      = gao.gao_data;
        ao_global_alloc = cglobs;
        ao_stack_alloc  = get_sao
      })
    in
    Format.eprintf
"(* -------------------------------------------------------------------- *)@.";
    Format.eprintf "(* Intermediate results of the stack allocation oracle *)@.@.";
    Format.eprintf "%a@.@.@." (pp_oracle up) saos
  end;

  let sp' =
    match
      Stack_alloc.alloc_prog
        Arch.pointer_data
        Arch.msf_size
        Arch.asmOp
        false
        Arch.aparams.ap_shp
        Arch.aparams.ap_sap
        (Conv.fresh_var_ident (Reg (Normal, Pointer Writable)) IInfo.dummy (Uint63.of_int 0))
        crip
        crsp
        gao.gao_data
        cglobs
        get_sao
        up
    with
    | Utils0.Ok sp -> sp 
    | Utils0.Error e ->
      let e = Conv.error_of_cerror pp_err e in
      raise (HiError e)
  in
  let fds, _ = Conv.prog_of_csprog sp' in
  
  if debug then
    Format.eprintf "After memory analysis@.%a@."
      (Printer.pp_prog ~debug:true Arch.reg_size Arch.asmOp) ([], (List.map snd fds));
  
  (* remove unused result *)
  let tokeep = RemoveUnusedResults.analyse fds in
  (* TODO: the code is duplicated between here and compiler.v, we should factorize *)
  let returned_params fn =
    let sao = get_sao fn in
    let _, fd = List.find (fun (_, fd) -> fd.f_name = fn) fds in
    match fd.f_cc with
    | Export _ -> Some sao.sao_return
    | _ -> None
  in
  let tokeep fn =
    match returned_params fn with
    | Some l ->
        let l' = List.map ((=) None) l in
        if List.for_all (fun x -> x) l' then None else Some l'
    | None -> tokeep fn
  in
  let deadcode (extra, fd) =
    let (fn, cfd) = Conv.cufdef_of_fdef fd in
    let fd = 
      match Dead_code.dead_code_fd Arch.asmOp Arch.aparams.ap_is_move_op false tokeep fn cfd with
      | Utils0.Ok cfd -> Conv.fdef_of_cufdef (fn, cfd)
      | Utils0.Error _ -> assert false in 
    (extra,fd) in
  let fds = List.map deadcode fds in
  if debug then
    Format.eprintf "After remove unused return @.%a@."
      (Printer.pp_prog ~debug:true Arch.reg_size Arch.asmOp) ([], (List.map snd fds));
  
  (* register allocation *)
  let translate_var = Conv.var_of_cvar in
  let has_stack f = FInfo.is_export f.f_cc && (Hf.find sao f.f_name).sao_modify_rsp in

  let internal_size_tbl = Hf.create 117 in
  let add_internal_size fd sz = Hf.add internal_size_tbl fd sz in
  let get_internal_size fd _ = Hf.find internal_size_tbl fd.f_name in

  let fix_subroutine_csao (_, fd) =
    match fd.f_cc with
    | Export _ -> ()
    | Internal -> assert false
    | Subroutine _ ->

    let fn = fd.f_name in
    let sao = Hf.find sao fn in
    let csao = get_sao fn in
    let to_save = [] in
    let rastack = Regalloc.subroutine_ra_by_stack fd in
    let extra = [] in

    let extra_size, align, extrapos = Varalloc.extend_sao sao extra in

    let align =
      if rastack && wsize_lt align Arch.reg_size then Arch.reg_size
      else align in

    let align, max_stk, max_call_depth =
      Sf.fold (fun fn (align, max_stk, max_call_depth) ->
          let sao = get_sao fn in
          let fn_align = sao.Stack_alloc.sao_align in
          let align = if wsize_lt align fn_align then fn_align else align in
          let fn_max = Conv.z_of_cz (sao.Stack_alloc.sao_max_size) in
          let max_stk = Z.max max_stk fn_max in
          let fn_max_call_depth = Conv.z_of_cz (sao.Stack_alloc.sao_max_call_depth) in
          let max_call_depth = Z.max max_call_depth fn_max_call_depth in
          align, max_stk, max_call_depth
        ) sao.sao_calls (align, Z.zero, Z.zero) in

    (* if we zeroize the stack, we ensure that the max size is a multiple of the
       size of the clear step. We use [fd.f_annot.stack_zero_strategy] and not
       [align], this is on purpose! We know that the first one divides the
       second one. *)
    let max_size =
      let stk_size =
        Z.add (Conv.z_of_cz csao.Stack_alloc.sao_size)
                   (Z.of_int extra_size) in
      let stk_size =
        Conv.z_of_cz (Memory_model.round_ws align (Conv.cz_of_z stk_size)) in
      add_internal_size fn stk_size;
      let max_size = Z.add max_stk stk_size in
      max_size
    in
    let max_call_depth = Z.succ max_call_depth in
    let saved_stack = Expr.SavedStackNone in

    let conv_to_save x =
      Conv.cvar_of_var x,
      List.assoc x extrapos
    in

    let compare_to_save (_, x) (_, y) = Stdlib.Int.compare y x in

    (* Stack slots for saving callee-saved registers are sorted in increasing order to simplify the check that they are all disjoint. *)
    let convert_to_save m =
      m |> List.rev_map conv_to_save |> List.sort compare_to_save |> List.rev_map (fun (x, n) -> x, Conv.cz_of_int n)
    in
    let csao =
      Stack_alloc.{ csao with
        sao_align = align;
        sao_ioff = Conv.cz_of_int (if rastack && not (FInfo.is_export fd.f_cc) then size_of_ws Arch.reg_size else 0);
        sao_extra_size = Conv.cz_of_int extra_size;
        sao_max_size = Conv.cz_of_z max_size;
        sao_max_call_depth = Conv.cz_of_z max_call_depth;
        sao_to_save = convert_to_save to_save;
        sao_rsp  = saved_stack;
        sao_return_address =
          (* This is a dummy value it will be fixed in fix_csao *)
          RAstack (None, Conv.cz_of_int 0, None)
      } in
    Hf.replace atbl fn csao
  in

  List.iter fix_subroutine_csao (List.rev fds);

  let fds = Regalloc.alloc_prog translate_var (fun fd _ -> has_stack fd) get_internal_size fds in

  let fix_csao (_, ro, fd) =
    match fd.f_cc with
    | Subroutine _ ->
      (* It as been already fixed by the previous pass fix_subroutine_csao,
         we just need to fix the return address *)
      let fn = fd.f_name in
      let csao = get_sao fn in
      let csao =
      Stack_alloc.{ csao with
        sao_return_address =
          match ro.ro_return_address with
          | StackDirect  -> RAstack (None, Conv.cz_of_int 0, None) (* FIXME stackDirect should provide a tmp register *)
          | StackByReg (r, tmp) -> RAstack (Some (Conv.cvar_of_var r), Conv.cz_of_int 0, Option.map Conv.cvar_of_var tmp)
          | ByReg (r, tmp)      -> RAreg (Conv.cvar_of_var r, Option.map Conv.cvar_of_var tmp)
      } in
      Hf.replace atbl fn csao
    | Internal -> assert false
    | Export _ ->

    let fn = fd.f_name in
    let sao = Hf.find sao fn in
    let csao = get_sao fn in 

    let to_save = ro.ro_to_save in 
    let has_stack = has_stack fd || to_save <> [] in

    let rsp = V.clone Arch.rsp_var in
    let extra =
      (* FIXME: how to make this more generic? *)
      let extra = List.rev to_save in
      if has_stack && ro.ro_rsp = None then extra @ [rsp]
      else extra in
      
    let extra_size, align, extrapos = Varalloc.extend_sao sao extra in

    let align, max_stk, max_call_depth =
      Sf.fold (fun fn (align, max_stk, max_call_depth) ->
          let sao = get_sao fn in
          let fn_align = sao.Stack_alloc.sao_align in
          let align = if wsize_lt align fn_align then fn_align else align in
          let fn_max = Conv.z_of_cz (sao.Stack_alloc.sao_max_size) in
          let max_stk = Z.max max_stk fn_max in
          let fn_max_call_depth = Conv.z_of_cz (sao.Stack_alloc.sao_max_call_depth) in
          let max_call_depth = Z.max max_call_depth fn_max_call_depth in
          align, max_stk, max_call_depth
        ) sao.sao_calls (align, Z.zero, Z.zero) in
    (* if we zeroize the stack, we may have to increase the alignment *)
    let align =
      match fd.f_cc, fd.f_annot.stack_zero_strategy with
      | Export _, Some (_, Some ws) ->
          if Z.equal max_stk Z.zero
            && Z.equal (Conv.z_of_cz csao.Stack_alloc.sao_size) Z.zero
            && extra_size = 0
          then
            (* no stack to clear, we don't change the alignment *)
            align
          else
            let ws = Pretyping.tt_ws ws in
            if wsize_lt align ws then ws else align
      | _, _ -> align
    in
    (* if we zeroize the stack, we ensure that the stack size of the export
       function is a multiple of the alignment (this is what we systematically
       do for subroutines). The difference is that, here, this is reflected
       by increasing extra_size. *)
    let extra_size =
      let stk_size = 
        Z.add (Conv.z_of_cz csao.Stack_alloc.sao_size)
                   (Z.of_int extra_size) in
      match fd.f_annot.stack_zero_strategy with
      | Some _ ->
          let round =
              Conv.z_of_cz (Memory_model.round_ws align (Conv.cz_of_z stk_size))
          in
          Z.to_int (Z.sub round (Conv.z_of_cz csao.Stack_alloc.sao_size))
      | None -> extra_size
    in
    (* if we zeroize the stack, we ensure that the max size is a multiple of the
       size of the clear step. We use [fd.f_annot.stack_zero_strategy] and not
       [align], this is on purpose! We know that the first one divides the
       second one. *)
    let max_size = 
      let stk_size = 
        Z.add (Conv.z_of_cz csao.Stack_alloc.sao_size)
                   (Z.of_int extra_size) in
      let stk_size = 
        match fd.f_cc with
        | Export _     -> stk_size
        | Subroutine _ ->
          Conv.z_of_cz (Memory_model.round_ws align (Conv.cz_of_z stk_size))
        | Internal -> assert false in
      let max_size = Z.add max_stk stk_size in
      match fd.f_cc, fd.f_annot.stack_zero_strategy with
      | Export _, Some (_, ows) ->
          let ws =
            match ows with
            | Some ws -> Pretyping.tt_ws ws
            | None -> align (* the default clear step is the alignment *)
          in
          Conv.z_of_cz (Memory_model.round_ws ws (Conv.cz_of_z max_size))
      | _, _ -> max_size
    in
    let max_call_depth = Z.succ max_call_depth in
    let saved_stack = 
      if has_stack then
        match ro.ro_rsp with
        | Some x -> Expr.SavedStackReg (Conv.cvar_of_var x)
        | None   -> Expr.SavedStackStk (Conv.cz_of_int (List.assoc rsp extrapos))
      else Expr.SavedStackNone in

    let conv_to_save x =
      Conv.cvar_of_var x,
      List.assoc x extrapos
    in

    let compare_to_save (_, x) (_, y) = Stdlib.Int.compare y x in

    (* Stack slots for saving callee-saved registers are sorted in increasing order to simplify the check that they are all disjoint. *)
    let convert_to_save m =
      m |> List.rev_map conv_to_save |> List.sort compare_to_save |> List.rev_map (fun (x, n) -> x, Conv.cz_of_int n)
    in
    let csao =
      Stack_alloc.{ csao with
        sao_align = align;
        sao_ioff = Conv.cz_of_int 0;
        sao_extra_size = Conv.cz_of_int extra_size;
        sao_max_size = Conv.cz_of_z max_size;
        sao_max_call_depth = Conv.cz_of_z max_call_depth;
        sao_to_save = convert_to_save to_save; 
        sao_rsp  = saved_stack;
        sao_return_address = RAnone
      } in
    Hf.replace atbl fn csao in
  List.iter fix_csao (List.rev fds);
  
  let saos =
    Compiler.({
      ao_globals      = gao.gao_data;
      ao_global_alloc = cglobs;
      ao_stack_alloc  =
        fun fn ->
        try Hf.find atbl fn
        with Not_found -> assert false
    })
  in

  if !Glob_options.print_stack_alloc then begin
    Format.eprintf
"(* -------------------------------------------------------------------- *)@.";
    Format.eprintf "(* Final results of the stack allocation oracle *)@.@.";
    Format.eprintf "%a@.@.@." (pp_oracle up) saos
  end;

  saos

end
