(*
*)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import one_varmap.
Import Utf8.
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
Context {pd: PointerData} {syscall_state : Type} {asm_op} {asmop : asmOp asm_op} {ovm_i : one_varmap_info}.
Context (p: sprog).
Context (var_tmp : Sv.t).

Let magic_variables : Sv.t := magic_variables p.

(** Set of variables written by a function (including RA and extra registers),
      assuming this information is known for the called functions. *)
Section WRITE1.

  Context (writefun: funname → Sv.t).

  Definition writefun_ra (fn: funname) :=
    let ra :=
      match get_fundef (p_funcs p) fn with
      | None => Sv.empty
      | Some fd => Sv.union (ra_vm fd.(f_extra) var_tmp) (saved_stack_vm fd)
      end in
    Sv.union (writefun fn) ra.

  Definition writefun_ra_call (fn: funname) :=
    Sv.union (writefun_ra fn) (fd_tmp_call p fn).

  Fixpoint write_i_rec s (i:instr_r) :=
    match i with
    | Cassgn x _ _ _  => vrv_rec s x
    | Copn xs _ _ _   => vrvs_rec s xs
    | Csyscall xs o _ => vrvs_rec (Sv.union s syscall_kill) (to_lvals (syscall_sig o).(scs_vout))
    | Cif   _ c1 c2   => foldl write_I_rec (foldl write_I_rec s c2) c1
    | Cfor  x _ c     => foldl write_I_rec (Sv.add x s) c
    | Cwhile _ c _ c' => foldl write_I_rec (foldl write_I_rec s c') c
    | Ccall _ fn _    => Sv.union s (writefun_ra_call fn)
    end
  with write_I_rec s i :=
    match i with
    | MkI ii i => write_i_rec s i
    end.

  Definition write_I := write_I_rec Sv.empty.
  Definition write_i := write_i_rec Sv.empty.

  Definition write_c_rec := foldl write_I_rec.
  Definition write_c := write_c_rec Sv.empty.

  Definition write_fd (fd: sfundef) := write_c fd.(f_body).

End WRITE1.

Definition get_wmap (wmap: Mf.t Sv.t) (fn: funname) : Sv.t :=
  odflt Sv.empty (Mf.get wmap fn).

Definition mk_wmap :=
  foldr (λ '(f, fd) wmap,
         let w := write_fd (get_wmap wmap) fd in
         Mf.set wmap f w)
        (Mf.empty _) p.(p_funcs).

Definition check_wmap (wmap: Mf.t Sv.t) : bool :=
  all (λ '(f, fd), Sv.subset (write_fd (get_wmap wmap) fd) (get_wmap wmap f)) (p_funcs p).

Definition check_fv (ii:instr_info) (D R : Sv.t) :=
  let I := Sv.inter D R in
  assert (Sv.is_empty I) 
         (E.gen_error true (Some ii) 
                      (pp_hov (pp_s "modified expression :" :: map pp_var (Sv.elements I)))).

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
    check_ir sz ii D ir

  with check_ir sz ii D ir :=
    match ir with
    | Cassgn x tag ty e =>
      Let _ := check_e ii D e in
      check_lv ii D x
    | Copn xs tag o es =>
      Let _ := check_es ii D es in
      check_lvs ii D xs
    | Csyscall xs o es =>
      let osig := syscall_sig o in
      let o_params := osig.(scs_vin) in
      let o_res := osig.(scs_vout) in
      Let _ := check_es ii D es in
      Let _ := assert
        (all2 (λ e a, if e is Pvar (Gvar v Slocal) then v_var v == a else false) es o_params)
        (E.internal_error ii "bad syscall args") in
      Let _ := assert
        (all2 (λ x r, if x is Lvar v then v_var v == r else false) xs o_res)
        (E.internal_error ii "bad syscall dests") in
      let W := syscall_kill in
      ok (Sv.diff (Sv.union D W) (vrvs (to_lvals (syscall_sig o).(scs_vout))))
    | Cif b c1 c2 =>
      Let _ := check_e ii D b in
      Let D1 := check_c (check_i sz) D c1 in
      Let D2 := check_c (check_i sz) D c2 in
      ok (Sv.union D1 D2)
    | Cfor _ _ _ =>
      Error (E.internal_error ii "for loop should be unrolled")
    | Cwhile _ c e c' =>
      if is_false e then check_c (check_i sz) D c
      else wloop (check_i sz) ii c (read_e e) c' Loop.nb D

    | Ccall xs fn es =>
      if get_fundef (p_funcs p) fn is Some fd then
        let tmp := tmp_call (f_extra fd) in
        Let _ := check_es ii (Sv.union D tmp) es in
        Let _ := assert (sf_align (f_extra fd) ≤ sz)%CMP
          (E.internal_error ii "alignment constraints error") in
        Let _ := assert
          (all2 (λ e a, if e is Pvar (Gvar v Slocal) then v_var v == v_var a else false) es (f_params fd))
          (E.internal_error ii "bad call args") in
        Let _ := assert
          (all2 (λ x r, if x is Lvar v then v_var v == v_var r else false) xs (f_res fd))
          (E.internal_error ii "bad call dests") in
        let W := writefun_ra writefun fn in
        let res := sv_of_list v_var (f_res fd) in
        Let _ := assert
          (disjoint tmp res)
          (E.internal_error ii "tmp call write dests") in
        ok (Sv.union (Sv.diff (Sv.union D W) res) tmp)
      else Error (E.internal_error ii "call to unknown function")

    end.

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
    Let _ := assert (disjoint magic_variables (tmp_call e))
                    (E.gen_error true None (pp_s "not (disjoint magic_variables tmp_call)")) in
    match sf_return_address e with
    | RAreg ra _ => check_preserved_register W J "return address" ra
    | RAstack ra _ _ =>
         if ra is Some r then 
            assert (vtype r == sword Uptr) 
             (E.gen_error true None (pp_box [::pp_s "bad register type for"; pp_s "return address"; pp_var r]))
         else ok tt
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
  Let _ := assert (disjoint var_tmp magic_variables) (E.gen_error true None (pp_s "RAX clashes with RSP or RIP")) in
  Let _ := check_prog (get_wmap wmap) in
  ok tt.

End PROG.
