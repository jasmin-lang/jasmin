(*
*)
Require Import one_varmap expr_facts.
Import Utf8.
Import all_ssreflect.
Import expr compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** This is a checker that it is safe to merge the local variables of a function and its caller.

Variables that are overwritten by the callee are not live at the call sites.



*)

Module E.

Definition pass_name := "one-varmap checker"%string.

Definition gen_error (internal:bool) (ii:option instr_info) (msg:pp_error) :=
  {| pel_msg      := msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := ii
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := internal
  |}.

Definition internal_error ii msg :=
  gen_error true (Some ii) (pp_s msg).

Definition error ii msg :=
  gen_error false (Some ii) (pp_s msg).

Definition ii_loop_iterator :=
  ii_loop_iterator pass_name.

End E.

Section PROG.
Context {pd: PointerData} {asm_op} {asmop : asmOp asm_op} {ovm_i : one_varmap_info}.
Context (p: sprog) (extra_free_registers: instr_info → option var).
Context (var_tmp : var).

(** Set of variables written by a function (including RA and extra registers),
      assuming this information is known for the called functions. *)

Definition add_extra_free_registers ii (D:Sv.t) :=
  if extra_free_registers ii is Some r then Sv.add r D
  else D.

Local Notation extra_free_registers_at := (extra_free_registers_at extra_free_registers).

Lemma add_extra_free_registersE ii D :
  Sv.Equal (add_extra_free_registers ii D) (Sv.union (extra_free_registers_at ii) D).
Proof.
  rewrite /add_extra_free_registers /extra_free_registers_at; case: extra_free_registers; SvD.fsetdec.
Qed.

Let magic_variables : Sv.t := magic_variables p.

Section WRITE1.

  Context (writefun: funname → Sv.t).

  Definition writefun_ra (fn: funname) :=
    let ra :=
      match get_fundef (p_funcs p) fn with
      | None => Sv.empty
      | Some fd => Sv.union (ra_vm fd.(f_extra) var_tmp) (saved_stack_vm fd)
      end in
    Sv.union (writefun fn) ra.

  Fixpoint write_i_rec s (i:instr_r) :=
    match i with
    | Cassgn x _ _ _  => vrv_rec s x
    | Copn xs _ _ _   => vrvs_rec s xs
    | Cif   _ c1 c2   => foldl write_I_rec (foldl write_I_rec s c2) c1
    | Cfor  x _ c     => foldl write_I_rec (Sv.add x s) c
    | Cwhile _ c _ c' => foldl write_I_rec (foldl write_I_rec s c') c
    | Ccall _ _ fn _  => Sv.union s (writefun_ra fn)
    end
  with write_I_rec s i :=
    match i with
    | MkI ii i => add_extra_free_registers ii (write_i_rec s i)
    end.

  Definition write_I := write_I_rec Sv.empty.
  Definition write_i := write_i_rec Sv.empty.

  Definition write_c_rec := foldl write_I_rec.
  Definition write_c := write_c_rec Sv.empty.

  Definition write_fd (fd: sfundef) := write_c fd.(f_body).

  Lemma write_c_recE c : ∀ s, Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)).
  Proof.
    apply: (@cmd_rect _ _
              (λ i, ∀ s, Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)))
              (λ i, ∀ s, Sv.Equal (write_I_rec s i) (Sv.union s (write_I i)))
              (λ c, ∀ s, Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)))).
    - by move => i ii ih s; rewrite /write_I /= !add_extra_free_registersE !ih; SvD.fsetdec.
    - by SvD.fsetdec.
    - by move => i c' hi hc' s; rewrite /write_c /= !hc' -/write_I hi; SvD.fsetdec.
    - by move => x tg ty e s; rewrite /write_i /= -vrv_recE.
    - by move => xs tg op es s; rewrite /write_i /= -vrvs_recE.
    - by move => e c1 c2 h1 h2 s; rewrite /write_i /= -!/write_c_rec -/write_c !h1 h2; SvD.fsetdec.
    - by move => v d lo hi body h s; rewrite /write_i /= -!/write_c_rec !h; SvD.fsetdec.
    - by move => a c1 e c2  h1 h2 s; rewrite /write_i /= -!/write_c_rec -/write_c !h1 h2; SvD.fsetdec.
    by move => i xs fn es s; rewrite /write_i /=; SvD.fsetdec.
  Qed.

  Lemma write_I_recE ii i s :
    Sv.Equal (write_I_rec s (MkI ii i))
             (Sv.union (write_i_rec s i) (extra_free_registers_at ii)).
  Proof. rewrite /= add_extra_free_registersE; SvD.fsetdec. Qed.

End WRITE1.

Definition get_wmap (wmap: Mp.t Sv.t) (fn: funname) : Sv.t :=
  odflt Sv.empty (Mp.get wmap fn).

Definition mk_wmap :=
  foldr (λ '(f, fd) wmap,
         let w := write_fd (get_wmap wmap) fd in
         Mp.set wmap f w)
        (Mp.empty _) p.(p_funcs).

Definition check_wmap (wmap: Mp.t Sv.t) : bool :=
  all (λ '(f, fd), Sv.subset (write_fd (get_wmap wmap) fd) (get_wmap wmap f)) (p_funcs p).

Definition check_fv (ii:instr_info) (D R : Sv.t) :=
  assert (disjoint D R) (E.error ii "modified expression").

Definition check_e (ii:instr_info) (D : Sv.t) (e : pexpr) :=
  check_fv ii D (read_e e).

Definition check_es ii D es :=
  foldM (fun e _ => check_e ii D e) tt es.

Section CHECK.

  Context (writefun: funname → Sv.t).

  Section CHECK_c.

    Context (check_i: Sv.t → instr → cexec Sv.t).

    Fixpoint check_c (D: Sv.t) (c: cmd) :=
      if c is i :: c' then
        Let D := check_i D i in
        check_c D c'
      else ok D.

    Context (ii: instr_info) (c1: cmd) (efv: Sv.t) (c2: cmd).

    Fixpoint wloop (n: nat) (D: Sv.t) :=
      if n is S n' then
        (* while c1 e c2 = c1; while e do c2; c1 *)
        Let D1 := check_c D c1 in
        Let _ := check_fv ii  D1 efv in
        Let D2 := check_c D1 c2 in
        if Sv.subset D2 D then ok D1
        else wloop n' (Sv.union D2 D)
      else Error (E.ii_loop_iterator ii).

  End CHECK_c.

  Section CHECK_i.

  Definition check_lv ii (D:Sv.t) (x:lval) :=
    Let _ := check_fv ii D (read_rv x) in
    ok (Sv.diff D (vrv x)).

  Definition check_lvs ii (D:Sv.t) (xs:lvals) :=
    foldM (fun x D => check_lv ii D x) D xs.

  Fixpoint check_i (sz: wsize) (D:Sv.t) (i: instr) : cexec Sv.t :=
    let: MkI ii ir := i in
    Let _ :=
      if extra_free_registers ii is Some r
      then
        assert (vtype r == sword Uptr) (E.internal_error ii "bad type for extra free register") >>
        assert (if ir is Cwhile _ _ _ _ then false else true) (E.internal_error ii "loops need no extra register")
      else ok tt in
    check_ir sz ii (add_extra_free_registers ii D) ir

  with check_ir sz ii D ir :=
    match ir with
    | Cassgn x tag ty e =>
      Let _ := check_e ii D e in
      check_lv ii D x
    | Copn xs tag o es =>
      Let _ := check_es ii D es in
      check_lvs ii D xs
    | Cif b c1 c2 =>
      Let _ := check_e ii D b in
      Let D1 := check_c (check_i sz) D c1 in
      Let D2 := check_c (check_i sz) D c2 in
      ok (Sv.union D1 D2)
    | Cfor _ _ _ =>
      Error (E.internal_error ii "for loop should be unrolled")
    | Cwhile _ c e c' =>
      if e == Pbool false then check_c (check_i sz) D c
      else wloop (check_i sz) ii c (read_e e) c' Loop.nb D

    | Ccall _ xs fn es =>
      if get_fundef (p_funcs p) fn is Some fd then
        Let _ := check_es ii D es in
        Let _ := assert (sf_align (f_extra fd) ≤ sz)%CMP
          (E.internal_error ii "alignment constraints error") in
        Let _ := assert (if sf_return_address (f_extra fd) is RAstack _ then extra_free_registers ii != None else true)
          (E.internal_error ii "no extra free register to compute the return address") in
        Let _ := assert
          (all2 (λ e a, if e is Pvar (Gvar v Slocal) then v_var v == v_var a else false) es (f_params fd))
          (E.internal_error ii "bad call args") in
        Let _ := assert
          (all2 (λ x r, if x is Lvar v then v_var v == v_var r else false) xs (f_res fd))
          (E.internal_error ii "bad call dests") in
        let W := writefun_ra writefun fn in
        ok (Sv.diff (Sv.union D W) (sv_of_list v_var (f_res fd)))
      else Error (E.internal_error ii "call to unknown function")

    end.

  Lemma check_ir_CwhileP sz ii aa c e c' D D' :
    check_ir sz ii D (Cwhile aa c e c') = ok D' →
    if e == Pbool false
    then check_c (check_i sz) D c = ok D'
    else
      ∃ D1 D2,
        [/\ check_c (check_i sz) D1 c = ok D',
            check_e ii D' e = ok tt,
            check_c (check_i sz) D' c' = ok D2,
            check_ir sz ii D1 (Cwhile aa c e c') = ok D' &
            Sv.Subset D D1 /\ Sv.Subset D2 D1 ].
  Proof.
    rewrite /check_ir; case: eqP => // _; rewrite -/check_i.
    elim: Loop.nb D => // n ih /=; t_xrbindP => D D1 h1 he D2 h2.
    case: (equivP idP (Sv.subset_spec _ _)) => d.
    - case => ?; subst D1; exists D, D2; split => //; last by split.
      by rewrite h1 /= he /= h2 /=; move /Sv.subset_spec : d => ->.
    move => /ih{ih} [D4] [D3]; rewrite /check_e => -[ h he' h' heq [le le'] ].
    exists D4, D3; split => //; last by split; SvD.fsetdec.
    by rewrite h /= he' /= h' /=; move /Sv.subset_spec: le' => ->.
  Qed.

  End CHECK_i.

  Notation check_cmd sz := (check_c (check_i sz)).

  Let check_preserved_register W J name r :=
    Let _ :=
      assert (vtype r == sword Uptr) (E.gen_error true None (pp_box [::pp_s "bad register type for"; pp_s name; pp_var r])) in
    Let _ :=
      assert (~~ Sv.mem r W) (E.gen_error true None (pp_box [::pp_s "the function writes its"; pp_s name; pp_var r])) in
    assert (~~Sv.mem r J) (E.gen_error true None (pp_box [::pp_s "the function depends on its"; pp_s name; pp_var r])).

  Definition check_fd (fn:funname) (fd: sfundef) :=
    let params := sv_of_list v_var fd.(f_params) in
    let DI := Sv.inter params (ra_undef fd var_tmp) in
    Let D := check_cmd fd.(f_extra).(sf_align) DI fd.(f_body) in
    let res := sv_of_list v_var fd.(f_res) in
    let W' := writefun_ra writefun fn in
    Let _ := assert (disjoint D res)
                    (E.gen_error true None (pp_s "not able to ensure equality of the result")) in
    Let _ := assert (disjoint params magic_variables)
                    (E.gen_error true None (pp_s "the function has RSP or global-data as parameter")) in
    Let _ := assert (~~ Sv.mem (vid p.(p_extra).(sp_rsp)) res)
                    (E.gen_error true None (pp_s "the function returns RSP")) in
    Let _ := assert (disjoint W' magic_variables)
                    (E.gen_error true None (pp_s "the function writes to RSP or global-data")) in
    let W := writefun fn in
    let J := Sv.union magic_variables params in
    let e := fd.(f_extra) in
    Let _  :=
      if sf_save_stack e is SavedStackReg r then
         check_preserved_register W J "saved stack pointer" r
      else ok tt in
    match sf_return_address e with
    | RAreg ra => check_preserved_register W J "return address" ra
    | RAstack _ => ok tt
    | RAnone =>
        let to_save := sv_of_list fst fd.(f_extra).(sf_to_save) in
        Let _ := assert (disjoint to_save res)
                    (E.gen_error true None (pp_s "the function returns a callee-saved register")) in
        Let _ := assert (Sv.subset (Sv.inter callee_saved W') to_save)
                    (E.gen_error true None (pp_s "the function kills some callee-saved registers")) in
        assert (all (λ x : var_i, if vtype x is sword _ then true else false ) (f_params fd))
            (E.gen_error true None (pp_s "the export function has non-word arguments"))
    end.

  Definition check_prog := map_cfprog_name check_fd (p_funcs p).

End CHECK.

Definition check :=
  let wmap := mk_wmap in
  Let _ := assert (check_wmap wmap) (E.gen_error true None (pp_s "invalid wmap")) in
  Let _ := assert (p.(p_extra).(sp_rip) != p.(p_extra).(sp_rsp)) (E.gen_error true None (pp_s "rip and rsp clash")) in
  Let _ := assert (~~ Sv.mem var_tmp magic_variables) (E.gen_error true None (pp_s "RAX clashes with RSP or RIP")) in
  Let _ := check_prog (get_wmap wmap) in
  ok tt.

End PROG.
