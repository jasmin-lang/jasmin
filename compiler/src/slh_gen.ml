open Prog

type 'len slhvar = {
  gv : 'len gvar;
  gvi : 'len gvar_i;
  lv : 'len glval;
  gx : 'len gexpr;
}

let count = ref (Utils.Uniq.gen ())
let msf_count = ref 0

let mk_slhvar name reg_kind =
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
    (i : ('len, unit, 'asm) ginstr) : ('len, unit, 'asm) ginstr list =
  let check_i_annot i = Annotations.has_symbol "protect" i.i_annot in
  match i.i_desc with
  | Cassgn (Lvar lhs, tag, wsize, e) when check_i_annot i -> (
      let lhs_gvar = L.unloc lhs in
      let lhs_expr = Pvar { gv = lhs; gs = Slocal } in
      if is_ptr lhs_gvar.v_kind then
        [
          unspill_instr i.i_loc;
          {
            i with
            i_desc =
              Copn
                ( [ Lvar lhs ],
                  tag,
                  Sopn.Oslh (SLHprotect_ptr Coq_xH),
                  [ lhs_expr; msf.gx ] );
          };
          spill_instr i.i_loc;
        ]
      else
        match wsize with
        | Bty (U wordsize) ->
            [
              unspill_instr i.i_loc;
              {
                i with
                i_desc =
                  Copn
                    ( [ Lvar lhs ],
                      tag,
                      Sopn.Oslh (SLHprotect wordsize),
                      [ lhs_expr; msf.gx ] );
              };
              spill_instr i.i_loc;
            ]
        | _ -> [ i ])
  | _ -> [ i ]

let rec is_export_fn (funcs : (pexpr, 'info, 'asm) gfunc list)
    (fun_name : funname) =
  let hd_name = (List.hd funcs).f_name in
  if compare hd_name fun_name == 0 then
    match (List.hd funcs).f_cc with Export _ -> true | _ -> false
  else is_export_fn (List.tl funcs) fun_name

let rec add_setmsf_instr (msf : 'len slhvar) (mmx_msf : 'len slhvar)
    (spill_instr : L.i_loc -> ('len, unit, 'asm) ginstr) unspill_instr funcs
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
         (add_slh_protect msf spill_instr unspill_instr)
         (List.flatten
            (List.map
               (add_setmsf_instr msf mmx_msf spill_instr unspill_instr funcs)
               body)))
  in
  match i.i_desc with
  | Csyscall (_, _, _) ->
      let init_instr =
        {
          i_desc = Copn ([ msf.lv ], AT_keep, Sopn.Oslh SLHinit, []);
          i_loc = i.i_loc;
          i_info = ();
          i_annot = [];
        }
      in
      [ i; init_instr; spill_instr i.i_loc ]
  | Ccall (vars, func_name, inputs) ->
      if is_export_fn funcs func_name then
        let init_instr =
          {
            i_desc = Copn ([ msf.lv ], AT_keep, Sopn.Oslh SLHinit, []);
            i_loc = i.i_loc;
            i_info = ();
            i_annot = [];
          }
        in
        [ i; init_instr; spill_instr i.i_loc ]
      else
        [
          (* unspill_instr i.i_loc; *)
          {
            i with
            i_desc = Ccall (mmx_msf.lv :: vars, func_name, mmx_msf.gx :: inputs);
          };
          (* spill_instr i.i_loc; *)
        ]
  | Cif (cond, if_body, else_body) ->
      (* TODO: remove this condvar if tests pass *)
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
      let update_msf_if =
        {
          i_desc =
            Copn
              ([ msf.lv ], AT_none, Sopn.Oslh SLHupdate, [ cond_expr; msf.gx ]);
          i_loc = i.i_loc;
          i_info = ();
          i_annot = [];
        }
      in

      let update_msf_else =
        {
          i_desc =
            Copn
              ( [ msf.lv ],
                AT_none,
                Sopn.Oslh SLHupdate,
                [ Papp1 (E.Onot, cond_expr); msf.gx ] );
          i_loc = i.i_loc;
          i_info = ();
          i_annot = [];
        }
      in
      init_b_instr
      @ [ unspill_instr i.i_loc ]
      @ [
          {
            i with
            i_desc =
              Cif
                ( cond_expr,
                  update_msf_if :: spill_instr i.i_loc :: add_slh_block if_body,
                  update_msf_else :: spill_instr i.i_loc
                  :: add_slh_block else_body );
          };
        ]
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
      let update_msf_body =
        {
          i_desc =
            Copn
              ([ msf.lv ], AT_none, Sopn.Oslh SLHupdate, [ cond_expr; msf.gx ]);
          i_loc = i.i_loc;
          i_info = ();
          i_annot = [];
        }
      in
      (* TODO change update_msf to fn *)
      let update_msf_after =
        {
          i_desc =
            Copn
              ( [ msf.lv ],
                AT_none,
                Sopn.Oslh SLHupdate,
                [ Papp1 (E.Onot, cond_expr); msf.gx ] );
          i_loc = i.i_loc;
          i_info = ();
          i_annot = [];
        }
      in
      [
        unspill_instr i.i_loc;
        {
          i with
          i_desc =
            Cwhile
              ( alignf,
                add_slh_block c1 @ init_b_instr,
                cond_expr,
                (update_msf_body :: spill_instr i.i_loc :: add_slh_block c2)
                @ [ unspill_instr i.i_loc ] );
        };
        (* unspill_instr i.i_loc; *)
        update_msf_after;
        spill_instr i.i_loc;
      ]
  | Cfor (it, rn, body) ->
      [ { i with i_desc = Cfor (it, rn, add_slh_block body) } ]
  | _ -> [ i ]

let add_slh_instrs msf mmx_msf spill_instr unspill_instr body funcs =
  List.flatten
    (List.map
       (add_slh_protect msf spill_instr unspill_instr)
       (List.flatten
          (List.map
             (add_setmsf_instr msf mmx_msf spill_instr unspill_instr funcs)
             body)))

let add_slh_local (mmx_msf : 'len slhvar) funcs
    (func : (pexpr, 'info, 'asm) gfunc) =
  let msf = mk_slhvar "msf" Normal in

  let spill_instr loc =
    {
      i_desc = Copn ([ mmx_msf.lv ], AT_none, Sopn.Oslh SLHmove, [ msf.gx ]);
      i_loc = loc;
      i_info = ();
      i_annot = [];
    }
  in
  let unspill_instr loc =
    {
      i_desc = Copn ([ msf.lv ], AT_none, Sopn.Oslh SLHmove, [ mmx_msf.gx ]);
      i_loc = loc;
      i_info = ();
      i_annot = [];
    }
  in
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
    f_args = mmx_msf.gv :: func.f_args;
    f_body =
      add_slh_instrs msf mmx_msf spill_instr unspill_instr func.f_body funcs;
    f_tyout = Bty (U U64) :: func.f_tyout;
    f_outannot =
      ((Location.mk_loc Location._dummy "msf", None) :: mmx_msf.gv.v_annot)
      :: func.f_outannot;
    f_ret = mmx_msf.gvi :: func.f_ret;
  }

let add_slh_export funcs (msf : 'len slhvar) (mmx_msf : 'len slhvar)
    (func : (pexpr, 'info, 'asm) gfunc) =
  let init_instr =
    {
      i_desc = Copn ([ msf.lv ], AT_keep, Sopn.Oslh SLHinit, []);
      i_loc = L.i_dummy;
      i_info = ();
      i_annot = [];
    }
  in
  let spill_instr loc =
    {
      i_desc = Copn ([ mmx_msf.lv ], AT_none, Sopn.Oslh SLHmove, [ msf.gx ]);
      i_loc = loc;
      i_info = ();
      i_annot = [];
    }
  in
  let unspill_instr loc =
    {
      i_desc = Copn ([ msf.lv ], AT_none, Sopn.Oslh SLHmove, [ mmx_msf.gx ]);
      i_loc = loc;
      i_info = ();
      i_annot = [];
    }
  in
  {
    func with
    f_body =
      init_instr
      :: spill_instr init_instr.i_loc
      :: add_slh_instrs msf mmx_msf spill_instr unspill_instr func.f_body funcs;
  }

let add_slh_func funcs (func : (pexpr, 'info, 'asm) gfunc) =
  let msf = mk_slhvar "msf" Normal in

  let mmx_msf = mk_slhvar "mmx_msf" Extra in
  (* if the function is export, add init_msf. Otherwise, add msf argument and
     result. *)
  match func.f_cc with
  | Export _ -> add_slh_export funcs msf mmx_msf func
  | _ -> add_slh_local mmx_msf funcs func

let add_slh (pprog : (unit, 'asm) pprog) =
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
    | MIfun gfunc -> MIfun (add_slh_func prev_funcs gfunc)
    | _ -> item
  in
  List.map process_item pprog
