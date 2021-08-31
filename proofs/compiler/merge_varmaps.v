(*
*)
Require Import psem sem_one_varmap.
Import Utf8.
Import all_ssreflect.
Import var compiler_util.
Import x86_variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** This is a checker that it is safe to merge the local variables of a function and its caller.

Variables that are overwritten by the callee are not live at the call sites.



*)

Section PROG.

Context (p: sprog) (extra_free_registers: instr_info → option var).

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

Section WRITE1.

  Context (writefun: funname → Sv.t).

  Definition writefun_ra (fn: funname) :=
    let ra :=
      match get_fundef (p_funcs p) fn with
      | None => Sv.empty
      | Some fd =>
        Sv.union
          match fd.(f_extra).(sf_return_address) with
          | RAnone => Sv.add (var_of_register RAX) (sv_of_flags rflags)
          | RAreg ra => Sv.singleton ra
          | RAstack _ => Sv.empty
          end
          match fd.(f_extra).(sf_save_stack) with
          | SavedStackNone | SavedStackStk _ => Sv.empty
          | SavedStackReg r => Sv.singleton r
          end
      end in
    Sv.union (writefun fn) ra.

  Fixpoint write_i_rec s i :=
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
    apply: (@cmd_rect
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
    - by move => i xs fn es s; rewrite /write_i /=; SvD.fsetdec.
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
  assert (disjoint D R) (ii, (Cerr_one_varmap "modified expression")).

Definition check_e (ii:instr_info) (D : Sv.t) (e : pexpr) :=
  check_fv ii D (read_e e).

Definition check_es ii D es := 
  foldM (fun e _ => check_e ii D e) tt es.

Section CHECK.

  Context (writefun: funname → Sv.t).

  Section CHECK_c.

    Context (check_i: Sv.t → instr → ciexec Sv.t).

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
      else cierror ii (Cerr_Loop "MVM check").

  End CHECK_c.

  Section CHECK_i.

  Definition check_lv ii (D:Sv.t) (x:lval) := 
    Let _ := check_fv ii D (read_rv x) in
    ok (Sv.diff D (vrv x)).

  Definition check_lvs ii (D:Sv.t) (xs:lvals) := 
    foldM (fun x D => check_lv ii D x) D xs.
  
  Fixpoint check_i (sz: wsize) (D:Sv.t) (i: instr) : ciexec Sv.t :=
    let: MkI ii ir := i in
    Let _ := 
      assert (if extra_free_registers ii is Some r then vtype r == sword Uptr else true)
         (ii, (Cerr_one_varmap "bad type for extra free register : Please report")) in
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
      cierror ii (Cerr_one_varmap "for loop should be unrolled")
    | Cwhile _ c e c' =>
      
      if e == Pbool false then check_c (check_i sz) D c
      else wloop (check_i sz) ii c (read_e e) c' Loop.nb D

    | Ccall _ xs fn es =>
      if get_fundef (p_funcs p) fn is Some fd then
        Let _ := check_es ii D es in
        Let _ := assert (sf_align (f_extra fd) ≤ sz)%CMP
          (ii, Cerr_one_varmap "alignment constraints error") in
        Let _ := assert (if sf_return_address (f_extra fd) is RAstack _ then extra_free_registers ii != None else true)
          (ii, Cerr_one_varmap "no extra free register to compute the return address") in
        Let _ := assert 
          (all2 (λ e a, if e is Pvar (Gvar v Slocal) then v_var v == v_var a else false) es (f_params fd))
          (ii, Cerr_one_varmap "bad call args") in
        Let _ := assert
          (all2 (λ x r, if x is Lvar v then v_var v == v_var r else false) xs (f_res fd))
          (ii, Cerr_one_varmap "bad call dests") in
        let W := writefun_ra writefun fn in
        ok (Sv.diff (Sv.union D W) (set_of_var_i_seq Sv.empty (f_res fd)))
      else cierror ii (Cerr_one_varmap "call to unknown function")
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
    elim: Loop.nb D => // n ih /=; t_xrbindP => D D1 h1 [] he D2 h2.
    case: (equivP idP (Sv.subset_spec _ _)) => d.
    - case => ?; subst D1; exists D, D2; split => //; last by split.
      by rewrite h1 /= he /= h2 /=; move /Sv.subset_spec : d => ->.
    move => /ih{ih} [D4] [D3]; rewrite /check_e => -[ h he' h' heq [le le'] ].
    exists D4, D3; split => //; last by split; SvD.fsetdec.
    by rewrite h /= he' /= h' /=; move /Sv.subset_spec: le' => ->.
  Qed.

  End CHECK_i.

  Notation check_cmd sz := (check_c (check_i sz)).

  Let magic_variables : Sv.t :=
    magic_variables p.

  Let check_preserved_register fn W J name r :=
    Let _ := 
      assert (vtype r == sword Uptr) (Ferr_fun fn (Cerr_one_varmap ("bad register type for " ++ name))) in
    Let _ := 
      assert (~~ Sv.mem r W) (Ferr_fun fn (Cerr_one_varmap ("the function writes its " ++ name))) in
    assert (~~Sv.mem r J) (Ferr_fun fn (Cerr_one_varmap ("the function depends on its " ++ name))).

  Definition check_fd (ffd: sfun_decl) :=
    let: (fn, fd) := ffd in
    let DI := 
      match sf_return_address (f_extra fd) with
      | RAnone =>
        Sv.add (var_of_register RAX)
        match sf_save_stack (f_extra fd) with
        | SavedStackReg r => Sv.add r (sv_of_flags rflags)
        | _ => sv_of_flags rflags
        end
    | RAreg ra => Sv.singleton ra
    | RAstack _ => Sv.empty 
    end in

    Let D := add_finfo fn fn (check_cmd fd.(f_extra).(sf_align) DI fd.(f_body)) in
    let params := set_of_var_i_seq Sv.empty fd.(f_params) in
    let res := set_of_var_i_seq Sv.empty fd.(f_res) in
    Let _ := 
      assert (disjoint D res)
             (Ferr_fun fn (Cerr_one_varmap "not able to ensure equality of the result")) in
    Let _ := assert (var.disjoint params magic_variables)
                    (Ferr_fun fn (Cerr_one_varmap "the function has RSP or global-data as parameter")) in
    Let _ := assert (~~ Sv.mem (vid (string_of_register RSP)) res)
                    (Ferr_fun fn (Cerr_one_varmap "the functions returns RSP")) in
    Let _ := assert (var.disjoint (writefun_ra writefun fn) magic_variables)
                    (Ferr_fun fn (Cerr_one_varmap "the function writes to RSP or global-data")) in
    let W := writefun fn in
    let J := Sv.union magic_variables params in
    let e := fd.(f_extra) in
    Let _  := 
      if sf_save_stack e is SavedStackReg r then 
         check_preserved_register fn W J "saved stack pointer" r 
      else ok tt in
    match sf_return_address e with
    | RAreg ra => check_preserved_register fn W J "return address" ra
    | RAstack _ => ok tt
    | RAnone =>
        Let _ := assert (string_of_register RAX != p.(p_extra).(sp_rip)) (Ferr_fun fn (Cerr_one_varmap "RAX and RIP clash, please report")) in
        assert (all (λ x : var_i, if vtype x is sword _ then true else false ) (f_params fd))
            (Ferr_fun fn (Cerr_one_varmap "the export function has non-word arguments"))
    end.

  Definition check_prog := mapM check_fd (p_funcs p).

End CHECK.

Definition check :=
  let wmap := mk_wmap in
  Let _ := assert (check_wmap wmap) (Ferr_msg (Cerr_one_varmap "invalid wmap")) in
  Let _ := assert (p.(p_extra).(sp_rip) != string_of_register RSP) (Ferr_msg (Cerr_one_varmap "rip and rsp clash, please report")) in
  Let _ := check_prog (get_wmap wmap) in
  ok tt.

End PROG.
