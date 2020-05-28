(*
*)
Require Import psem.
Import Utf8.
Import all_ssreflect.
Import compiler_util.
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
Section WRITE1.

  Context (writefun: funname → Sv.t).

  Definition writefun_ra (fn: funname) :=
    let ra :=
      match get_fundef (p_funcs p) fn with
      | None => Sv.empty
      | Some fd =>
        match fd.(f_extra).(sf_return_address) with
        | RAnone | RAstack _ => Sv.empty
        | RAreg ra => Sv.singleton ra
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
    | MkI ii i =>
      let result := write_i_rec s i in
      if extra_free_registers ii is Some r
      then Sv.add r result
      else result
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
    - move => i ii ih s; rewrite /write_I /=; case: extra_free_registers => [ r | ]; rewrite ih; SvD.fsetdec.
    - SvD.fsetdec.
    - move => i c' hi hc' s. rewrite /write_c /= !hc' -/write_I hi; SvD.fsetdec.
    - by move => x tg ty e s; rewrite /write_i /= -vrv_recE.
    - by move => xs tg op es s; rewrite /write_i /= -vrvs_recE.
    - move => e c1 c2 h1 h2 s; rewrite /write_i /= -!/write_c_rec -/write_c !h1 h2; SvD.fsetdec.
    - move => v d lo hi body h s; rewrite /write_i /= -!/write_c_rec !h; SvD.fsetdec.
    - move => a c1 e c2  h1 h2 s; rewrite /write_i /= -!/write_c_rec -/write_c !h1 h2; SvD.fsetdec.
    move => i xs fn es s; rewrite /write_i /=; SvD.fsetdec.
  Qed.

  Definition extra_free_registers_at ii : Sv.t :=
    if extra_free_registers ii is Some r then Sv.singleton r else Sv.empty.

  Lemma write_I_recE ii i s :
    Sv.Equal (write_I_rec s (MkI ii i))
             (Sv.union (write_i_rec s i) (extra_free_registers_at ii)).
  Proof. rewrite /extra_free_registers_at /=; case: extra_free_registers => *; SvD.fsetdec. Qed.

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

Section CHECK.

  Context (writefun: funname → Sv.t).

  Section CHECK_c.

    Context (check_i: instr → Sv.t → ciexec Sv.t).

    Fixpoint check_c (c: cmd) (s: Sv.t) :=
      if c is i :: c' then
        Let s := check_c c' s in
        check_i i s
      else ok s.

    Context (ii: instr_info) (c1: cmd) (e: pexpr) (c2: cmd).

    Fixpoint wloop (n: nat) (s: Sv.t) :=
      if n is S n' then
        (* while c1 e c2 = c1; while e do c2; c1 *)
        let se := read_e_rec s e in
        Let s1 := check_c c1 se in
        Let s2 := check_c c2 s1 in
        if Sv.subset s2 s then ok s1
        else wloop n' (Sv.union s2 s)
      else cierror ii (Cerr_Loop "MVM check").

  End CHECK_c.

  Section CHECK_i.

  Fixpoint check_i (i: instr) (D: Sv.t) :=
    let: MkI ii ir := i in
    Let D2 := check_ir ii ir D in
    Let _ := assert (if extra_free_registers ii is Some r then negb (Sv.mem r D2) else true)
                        (ii, Cerr_one_varmap "extra register (for rastack) is not free") in
    ok D2
  with check_ir ii ir D :=
    match ir with
    | Cassgn x tag ty e =>
      ok (read_rv_rec (read_e_rec (Sv.diff D (vrv x)) e) x)
    | Copn xs tag o es =>
      ok (read_es_rec (read_rvs_rec (Sv.diff D (vrvs xs)) xs) es)
    | Cif b c1 c2 =>
      Let D1 := check_c check_i c1 D in
      Let D2 := check_c check_i c2 D in
      ok (read_e_rec (Sv.union D1 D2) b)
    | Cfor _ _ _ =>
      cierror ii (Cerr_one_varmap "for loop should be unrolled")
    | Cwhile _ c e c' =>
      if e == Pbool false then check_c check_i c D
      else wloop check_i ii c e c' Loop.nb D
    | Ccall _ xs fn es =>
      if get_fundef (p_funcs p) fn is Some fd then
        Let _ := assert (sf_return_address (f_extra fd) != RAnone)
          (ii, Cerr_one_varmap "nowhere to store the return address") in
        Let _ := assert (if sf_return_address (f_extra fd) is RAstack _ then extra_free_registers ii != None else true)
          (ii, Cerr_one_varmap "no extra free register to compute the return address") in
        Let _ := assert
          (all2 (λ e a, if e is Pvar (Gvar v Slocal) then v_var v == v_var a else false) es (f_params fd))
          (ii, Cerr_one_varmap "bad call args") in
        Let _ := assert
          (all2 (λ x r, if x is Lvar v then v_var v == v_var r else false) xs (f_res fd))
          (ii, Cerr_one_varmap "bad call dests") in
        let W := writefun_ra writefun fn in
        let D1 := read_rvs_rec (Sv.diff D (vrvs xs)) xs in (* Remark read_rvs xs is empty since all variables *)
        let inter := Sv.inter D1 W in
        Let _ := assert (Sv.is_empty inter) (ii, Cerr_needspill fn (Sv.elements inter)) in
        ok (read_es_rec D1 es)
      else cierror ii (Cerr_one_varmap "call to unknown function")
    end.

  End CHECK_i.

  Notation check_cmd := (check_c check_i).

  Definition set_of_var_i_seq : Sv.t → seq var_i → Sv.t :=
    foldl (λ acc x, Sv.add (v_var x) acc).

  Definition live_after_fd (fd: sfundef) : Sv.t :=
    set_of_var_i_seq Sv.empty fd.(f_res).

  Let magic_variables : Sv.t :=
    Sv.add (vid p.(p_extra).(sp_rip)) (Sv.add (vid (string_of_register RSP)) Sv.empty).

  Definition check_fd (ffd: sfun_decl) :=
    let: (fn, fd) := ffd in
    let O := live_after_fd fd in
    Let I := add_finfo fn fn (check_cmd fd.(f_body) O) in
    Let _ := assert (Sv.subset I (set_of_var_i_seq magic_variables fd.(f_params)))
                    (Ferr_fun fn (Cerr_one_varmap_free fn (Sv.elements I))) in
    Let _ := assert (Sv.is_empty (Sv.inter magic_variables (writefun_ra writefun fn))) (Ferr_fun fn (Cerr_one_varmap "the function writes to RSP or global-data")) in
    let e := fd.(f_extra) in
    Let _ := match e.(sf_save_stack) with SavedStackReg r => assert (~~Sv.mem r (writefun fn))
                                                                    (Ferr_fun fn (Cerr_one_varmap "the function writes the saved RSP"))
                                     | SavedStackStk _ | SavedStackNone => ok tt
             end in
    match e.(sf_return_address) with
    | RAreg ra =>
      Let _ := assert (~~Sv.mem ra (writefun fn)) (Ferr_fun fn (Cerr_one_varmap "the function writes its return address")) in
      assert(~~Sv.mem ra I)  (Ferr_fun fn (Cerr_one_varmap "the function depends of its return address"))
    | RAnone | RAstack _ => ok tt
    end.

  Definition check_prog := mapM check_fd (p_funcs p).

End CHECK.

Definition check :=
  let wmap := mk_wmap in
  Let _ := assert (check_wmap wmap) (Ferr_msg (Cerr_one_varmap "invalid wmap")) in
  Let _ := check_prog (get_wmap wmap) in
  ok tt.

End PROG.

