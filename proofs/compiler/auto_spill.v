Require Import var expr.
Require Import psem_defs compiler_util.

Import Utf8 ssreflect ssrbool eqtype.

(* TODO: generalize progT ? *)

(*
Spill-map: statique par fonction
Exceptions à la spill-map: dynamique, construit par le checker
*)

Module E.

Definition pass_name := "auto spill"%string.

Definition gen_error ii (msg: pp_error) :=
  {| pel_msg      := msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := ii
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := false
  |}.

Definition error ii msg := gen_error (Some ii) msg.

End E.

Record spillmap : Type :=
  mkSpillmap {
    slots: Mvar.t var;
    spillable: Sv.t;
  }.

Section WITH_PARAMS.
  Context
  `{asmop : asmOp}
   {LC: LoopCounter}
    (autospill_fd: option (funname -> _ufundef -> _ufundef * list (var * var)))
  .

  Section WITH_SPILLMAP.

  Context (spillmap: spillmap).

  Definition check_lone_instr (i: instr) (exn: Sv.t) : cexec Sv.t :=
    let: MkI ii i := i in
    if i is Cassgn (Lvar d) tg ty (Pvar (Gvar s Slocal)) then
      if Mvar.get spillmap.(slots) d == Some (v_var s) then
        (* Spilling *)
        ok (Sv.remove s exn)
      else if Mvar.get spillmap.(slots) s == Some (v_var d) then
        (* Unspill *)
             assert (~~ Sv.mem d exn) (E.error ii (pp_s "unspilling stale data")) >> ok exn
      else Error (E.error ii (pp_s "…"))
    else Error (E.error ii (pp_s "unexpected unmatched instruction")).

  Section CHECK_INSTR.
    Context (check_instr: instr_info → instr_r → instr_r → Sv.t → cexec Sv.t).

    Fixpoint check_cmd (c c': cmd) (exn: Sv.t) : cexec Sv.t :=
      match c, c' with
      | [::], _ => foldM check_lone_instr exn c'
      | MkI ii _ :: _, [::] => Error (E.error ii (pp_s "trailing source instructions"))
      | MkI ii i :: d, MkI ii' i' :: c' =>
          if ii_eqb ii ii' then
            check_instr ii i i' exn >>= check_cmd d c'
          else check_lone_instr (MkI ii' i') exn >>= check_cmd c c'
      end.

    End CHECK_INSTR.

  Definition check_write ii (written: Sv.t) (exn: Sv.t) : cexec Sv.t :=
    Let _ := assert (Sv.for_all (λ x, Mvar.get spillmap.(slots) x == None) written)
                    (E.error ii (pp_s "write to a spill slot")) in
    ok (Sv.union exn (Sv.inter written spillmap.(spillable))).

  Fixpoint check_instr ii (i i': instr_r) (exn: Sv.t) : cexec Sv.t :=
    match i, i' with
    | Cassgn x _ ty e, Cassgn x' _ ty' e' =>
        Let _ := assert [&& eq_lval x x', ty == ty' & eq_expr e e'] (E.error ii (pp_s "modified assignment")) in
        check_write ii (vrv x) exn
    | Copn xs _ op es, Copn xs' _ op' es' =>
        Let _ := assert [&& all2 eq_lval xs xs', op == op' & all2 eq_expr es es'] (E.error ii (pp_s "modified operation")) in
        check_write ii (vrvs xs) exn
    | Csyscall xs op es, Csyscall xs' op' es' =>
        Let _ := assert [&& all2 eq_lval xs xs', op == op' & all2 eq_expr es es'] (E.error ii (pp_s "modified syscall")) in
        check_write ii (vrvs xs) exn
    | Ccall xs fn es, Ccall xs' fn' es' =>
        Let _ := assert [&& all2 eq_lval xs xs', fn == fn' & all2 eq_expr es es'] (E.error ii (pp_s "modified function call")) in
        check_write ii (vrvs xs) exn
    | Cif e th el, Cif e' th' el' =>
        Let _ := assert (eq_expr e e') (E.error ii (pp_s "modified if")) in
        Let exn_th := check_cmd check_instr th th' exn in
        Let exn_el := check_cmd check_instr el el' exn in
        ok (Sv.union exn_th exn_el)
    | Cwhile _ c1 e _ c2, Cwhile _ c1' e' _ c2' =>
        Let _ := assert (eq_expr e e') (E.error ii (pp_s "modified while")) in
        (fix loop n exn :=
           if n is S n then
             Let exn1 := check_cmd check_instr c1 c1' exn in
             Let exn2 := check_cmd check_instr c2 c2' exn1 in
             if Sv.subset exn2 exn then ok exn1 else loop n (Sv.union exn exn2)
           else Error (E.error ii (pp_s "no more fuel…"))
        ) loop_counter exn
    | Cassgn _ _ _ _, _ | Copn _ _ _ _, _
    | Csyscall _ _ _, _ | Ccall _ _ _, _
    | Cassert _, _ | Cfor _ _ _, _
    | Cif _ _ _, _ | Cwhile _ _ _ _ _, _
      => Error (E.error ii (pp_s "mismatched source instruction"))
    end.

  End WITH_SPILLMAP.

  Definition build_spillmap (twins: list (var * var)) : cexec spillmap :=
    foldM (λ '(r, m) sm,
        Let _ := assert (Mvar.get sm.(slots) r == None) (E.gen_error None (pp_s "spillable spill slot")) in
        Let _ := assert (convertible (vtype m) (vtype r)) (E.gen_error None (pp_s "incompatible types")) in
        let im := Sv.add r sm.(spillable) in
        Let _ := assert (~~ Sv.mem m im) (E.gen_error None (pp_s "a spillable register is used as a spill slot")) in
        ok {| slots := Mvar.set sm.(slots) m r; spillable := im |}
        ) {| slots := Mvar.empty _; spillable := Sv.empty |} twins.

  Definition check_eq_metadata (fd fd': ufundef) : bool :=
    [&& f_tyin fd == f_tyin fd', f_tyout fd == f_tyout fd'
      , f_extra fd == f_extra fd'
      , eq_var_is (f_params fd) (f_params fd') & eq_var_is (f_res fd) (f_res fd')].

  Definition auto_spill_prog (p: _uprog) : cexec _uprog :=
    if autospill_fd is Some transformation then
      let checked fn fd :=
        let: (fd', twins) := transformation fn fd in
        Let spillmap := build_spillmap twins in
        Let _ := assert (check_eq_metadata fd fd') (E.gen_error None (pp_s "modified metadata")) in
        Let exn := check_write spillmap (entry_info_of_fun_info fd.(f_info)) (sv_of_list v_var fd.(f_params)) Sv.empty in
        check_cmd spillmap (check_instr spillmap) fd.(f_body) fd'.(f_body) exn >> ok fd'
      in
      Let fds := map_cfprog_name checked p.(p_funcs) in
      ok {|
          p_funcs := fds;
          p_globs := p.(p_globs);
          p_extra := p.(p_extra);
        |}
    else ok p.

End WITH_PARAMS.
