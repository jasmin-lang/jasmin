open Prog

type 'len slhvar = {
  gv : 'len gvar;
  gvi : 'len gvar_i;
  lv : 'len glval;
  gx : 'len gexpr;
}

let count = ref (Utils.Uniq.gen ())
let msf_count = ref 0

let mk_init (var : 'len slhvar) (loc : L.i_loc) =
  {
    i_desc = Copn ([ var.lv ], AT_keep, Sopn.Oslh SLHinit, []);
    i_loc = loc;
    i_info = ();
    i_annot = [];
  }

let mk_update (cond : 'len gexpr) (var : 'len slhvar) (loc : L.i_loc) =
  {
    i_desc = Copn ([ var.lv ], AT_none, Sopn.Oslh SLHupdate, [ cond; var.gx ]);
    i_loc = loc;
    i_info = ();
    i_annot = [];
  }

let mk_mov (lhs : 'len slhvar) (rhs : 'len slhvar) (loc : L.i_loc) =
  {
    i_desc = Copn ([ lhs.lv ], AT_none, Sopn.Oslh SLHmove, [ rhs.gx ]);
    i_loc = loc;
    i_info = ();
    i_annot = [];
  }

let mk_slhvar (name : string) (reg_kind : Wsize.reg_kind) =
  let msf_gvar =
    GV.mk
      (name ^ string_of_int !msf_count)
      (Reg (reg_kind, Direct))
      (Bty (U U64)) L._dummy []
  in
  msf_count := !msf_count + 1;
  let msf_gvar_i = Location.mk_loc L._dummy msf_gvar in
  let msf_lval = Lvar msf_gvar_i in
  let msf_expr = Pvar { gv = msf_gvar_i; gs = Slocal } in
  { gv = msf_gvar; gvi = msf_gvar_i; lv = msf_lval; gx = msf_expr }

let add_slh_protect (msf : 'len slhvar) spill_instr unspill_instr
    (should_spill_msf : bool) (i : ('len, unit, 'asm) ginstr) :
    ('len, unit, 'asm) ginstr list =
  let check_i_annot i = Annotations.has_symbol "protect" i.i_annot in
  match i.i_desc with
  | Cassgn (Lvar lhs, tag, wsize, e) when check_i_annot i -> (
      let lhs_gvar = L.unloc lhs in
      let lhs_expr = Pvar { gv = lhs; gs = Slocal } in
      if is_ptr lhs_gvar.v_kind then
        let new_i =
          {
            i with
            i_desc =
              Copn
                ( [ Lvar lhs ],
                  tag,
                  Sopn.Oslh (SLHprotect_ptr Coq_xH),
                  [ lhs_expr; msf.gx ] );
          }
        in
        if should_spill_msf then
          [ unspill_instr i.i_loc; new_i (* spill_instr i.i_loc; *) ]
        else [ new_i ]
      else
        match wsize with
        | Bty (U wordsize) ->
            let new_i =
              {
                i with
                i_desc =
                  Copn
                    ( [ Lvar lhs ],
                      tag,
                      Sopn.Oslh (SLHprotect wordsize),
                      [ lhs_expr; msf.gx ] );
              }
            in
            if should_spill_msf then
              [ unspill_instr i.i_loc; new_i (* spill_instr i.i_loc; *) ]
            else [ new_i ]
        | _ -> [ i ])
  | _ -> [ i ]

let rec is_export_fn (funcs : (pexpr, 'info, 'asm) gfunc list)
    (fun_name : funname) =
  let hd_name = (List.hd funcs).f_name in
  if compare hd_name fun_name == 0 then
    match (List.hd funcs).f_cc with Export _ -> true | _ -> false
  else is_export_fn (List.tl funcs) fun_name

let rec add_setmsf_instr (msf : 'len slhvar) (mmx_msf : 'len slhvar) spill_instr
    unspill_instr funcs (should_spill_msf : bool)
    (i : ('len, unit, 'asm) ginstr) : ('len, unit, 'asm) ginstr list =
  (* TODO revert to count *)
  let name = "slh_bool" ^ string_of_int !msf_count in
  let b = GV.mk name Inline (Bty Bool) L._dummy [] in
  let _ = msf_count := !msf_count + 1 in
  let b_gvar_i = Location.mk_loc L._dummy b in
  let b_expr = Pvar { gv = b_gvar_i; gs = Slocal } in
  let b_lval = Lvar b_gvar_i in
  let is_cond_var (var : 'len gexpr) : bool =
    match var with Pvar _ | Papp1 _ -> true | _ -> false
  in
  let add_slh_block body =
    List.flatten
      (List.map
         (add_slh_protect msf spill_instr unspill_instr should_spill_msf)
         (List.flatten
            (List.map
               (add_setmsf_instr msf mmx_msf spill_instr unspill_instr funcs
                  should_spill_msf)
               body)))
  in
  let init_instr = mk_init msf i.i_loc in
  match i.i_desc with
  | Csyscall (_, _, _) ->
      if should_spill_msf then [ i; init_instr; spill_instr i.i_loc ]
      else [ i; init_instr ]
  | Ccall (vars, func_name, inputs) ->
      let final_msf = if should_spill_msf then mmx_msf else msf in
      if is_export_fn funcs func_name then
        if should_spill_msf then [ i; init_instr; spill_instr i.i_loc ]
        else [ i; init_instr ]
      else
        [
          {
            i with
            i_desc =
              Ccall (final_msf.lv :: vars, func_name, final_msf.gx :: inputs);
          };
        ]
  | Cif (cond, if_body, else_body) ->
      let cond_expr = if is_cond_var cond then cond else b_expr in
      let init_b_instr =
        if is_cond_var cond then []
        else
          [
            {
              i_desc = Cassgn (b_lval, AT_inline, Bty Bool, cond);
              i_loc = i.i_loc;
              i_info = ();
              i_annot = [];
            };
          ]
      in
      let update_msf_if = mk_update cond_expr msf i.i_loc in
      let update_msf_else = mk_update (Papp1 (E.Onot, cond_expr)) msf i.i_loc in
      let if_block =
        if should_spill_msf then
          unspill_instr i.i_loc :: update_msf_if :: spill_instr i.i_loc
          :: add_slh_block if_body
        else update_msf_if :: add_slh_block if_body
      in
      let else_block =
        if should_spill_msf then
          unspill_instr i.i_loc :: update_msf_else :: spill_instr i.i_loc
          :: add_slh_block else_body
        else update_msf_else :: add_slh_block else_body
      in
      init_b_instr
      @ [ { i with i_desc = Cif (cond_expr, if_block, else_block) } ]
  | Cwhile (alignf, c1, cond, c2) ->
      let cond_expr = if is_cond_var cond then cond else b_expr in
      let init_b_instr =
        if is_cond_var cond then []
        else
          [
            {
              i_desc = Cassgn (b_lval, AT_inline, Bty Bool, cond);
              i_loc = i.i_loc;
              i_info = ();
              i_annot = [];
            };
          ]
      in
      let update_msf_body = mk_update cond_expr msf i.i_loc in
      let update_msf_after =
        mk_update (Papp1 (E.Onot, cond_expr)) msf i.i_loc
      in
      let c1 = add_slh_block c1 @ init_b_instr in
      let c2 =
        if should_spill_msf then
          unspill_instr i.i_loc :: update_msf_body :: spill_instr i.i_loc
          :: add_slh_block c2
        else update_msf_body :: add_slh_block c2
      in
      let new_i = { i with i_desc = Cwhile (alignf, c1, cond_expr, c2) } in
      if should_spill_msf then
        [ new_i; unspill_instr i.i_loc; update_msf_after; spill_instr i.i_loc ]
      else [ new_i; update_msf_after ]
  | Cfor (it, rn, body) ->
      [ { i with i_desc = Cfor (it, rn, add_slh_block body) } ]
  | _ -> [ i ]

let add_slh_instrs msf mmx_msf spill_instr unspill_instr body funcs
    (should_spill_msf : bool) =
  List.flatten
    (List.map
       (add_slh_protect msf spill_instr unspill_instr should_spill_msf)
       (List.flatten
          (List.map
             (add_setmsf_instr msf mmx_msf spill_instr unspill_instr funcs
                should_spill_msf)
             body)))

let add_slh_local (mmx_msf : 'len slhvar) funcs
    (func : (pexpr, 'info, 'asm) gfunc) (should_spill_msf : bool) =
  let msf = mk_slhvar "msf" Normal in

  let spill_instr loc = mk_mov mmx_msf msf loc in
  let unspill_instr loc = mk_mov msf mmx_msf loc in
  let final_msf = if should_spill_msf then mmx_msf else msf in
  let append_None prev_cc =
    match prev_cc with
    | FInfo.Subroutine prev_returned_params ->
        let prev' =
          List.map (Option.map succ) prev_returned_params.returned_params
        in
        FInfo.Subroutine { returned_params = None :: prev' }
    | _ -> prev_cc
  in
  {
    (* TODO move msfs to the end *)
    f_loc = func.f_loc;
    f_annot = func.f_annot;
    f_cc = append_None func.f_cc;
    f_name = func.f_name;
    f_tyin = Bty (U U64) :: func.f_tyin;
    f_args = final_msf.gv :: func.f_args;
    f_body =
      add_slh_instrs msf mmx_msf spill_instr unspill_instr func.f_body funcs
        should_spill_msf;
    f_tyout = Bty (U U64) :: func.f_tyout;
    f_outannot =
      ((Location.mk_loc Location._dummy "msf", None) :: final_msf.gv.v_annot)
      :: func.f_outannot;
    f_ret = final_msf.gvi :: func.f_ret;
  }

let add_slh_export funcs (msf : 'len slhvar) (mmx_msf : 'len slhvar)
    (func : (pexpr, 'info, 'asm) gfunc) (should_spill_msf : bool) =
  let init_instr = mk_init msf L.i_dummy in
  let spill_instr = mk_mov mmx_msf msf in
  let unspill_instr loc = mk_mov msf mmx_msf loc in
  let init_instr =
    if should_spill_msf then [ init_instr; spill_instr init_instr.i_loc ]
    else [ init_instr ]
  in
  {
    func with
    f_body =
      init_instr
      (* :: spill_instr init_instr.i_loc
         :: add_slh_instrs msf mmx_msf spill_instr unspill_instr func.f_body funcs
              should_spill_msf; *)
      @ add_slh_instrs msf mmx_msf spill_instr unspill_instr func.f_body funcs
          should_spill_msf;
  }

let add_slh_func funcs (func : (pexpr, 'info, 'asm) gfunc)
    (should_spill_msf : bool) =
  let msf = mk_slhvar "msf" Normal in
  let mmx_msf = mk_slhvar "mmx_msf" Extra in
  match func.f_cc with
  | Export _ -> add_slh_export funcs msf mmx_msf func should_spill_msf
  | _ -> add_slh_local mmx_msf funcs func should_spill_msf

let add_slh (pprog : (unit, 'asm) pprog) (should_spill_msf : bool) :
    (unit, 'asm) pprog =
  (* let should_spill_msf = true in *)
  let match_item (item : ('len, 'info, 'asm) gmod_item) prev_funcs =
    match item with MIfun gfunc -> prev_funcs @ [ gfunc ] | _ -> prev_funcs
  in
  let rec get_all_funcs pprog_in =
    match pprog_in with
    | [] -> []
    | hd :: tl -> match_item hd (get_all_funcs tl)
  in
  let prev_funcs = get_all_funcs pprog in
  let process_item (item : ('len, 'info, 'asm) gmod_item) =
    match item with
    | MIfun gfunc -> MIfun (add_slh_func prev_funcs gfunc should_spill_msf)
    | _ -> item
  in
  (* pprog *)
  List.map process_item pprog
