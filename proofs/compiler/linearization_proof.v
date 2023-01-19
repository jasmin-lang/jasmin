(* * Syntax and semantics of the linear language *)

(* ** Imports and settings *)
From Coq
Require Import Setoid Morphisms Lia.

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith Utf8.
        Import Relations.

Require sem_one_varmap_facts label.
Import ssrZ.
Import ssrring.
Import psem psem_facts sem_one_varmap compiler_util label sem_one_varmap_facts low_memory.
Require Import constant_prop constant_prop_proof.
Require Export linearization linear_sem.
Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {spp : SemPexprParams asm_op syscall_state}
  {ovm_i : one_varmap_info}.

Notation spointer := (sword Uptr) (only parsing).

Lemma wunsigned_sub_small (p: pointer) (n: Z) :
  (0 <= n < wbase Uptr →
   wunsigned (p - wrepr Uptr n) <= wunsigned p →
   wunsigned (p - wrepr Uptr n) = wunsigned p - n)%Z.
Proof.
  move=> n_range.
  rewrite wunsigned_sub_if wunsigned_repr_small //.
  case: ZleP => //.
  by lia.
Qed.

Lemma wunsigned_top_stack_after_aligned_alloc m e m' :
  (0 <= sf_stk_sz e →
   0 <= sf_stk_extra_sz e →
   stack_frame_allocation_size e < wbase Uptr →
   is_align (top_stack m) (sf_align e) →
   alloc_stack m (sf_align e) (sf_stk_sz e) (sf_stk_ioff e) (sf_stk_extra_sz e) = ok m' →
  wunsigned (top_stack m) = wunsigned (top_stack m') + stack_frame_allocation_size e)%Z.
Proof.
  move => sz_pos extra_pos sf_noovf sp_align ok_m'.
  rewrite (alloc_stack_top_stack ok_m') (top_stack_after_aligned_alloc _ sp_align) -/(stack_frame_allocation_size _) wrepr_opp wunsigned_sub.
  - lia.
  have sf_pos : (0 <= stack_frame_allocation_size e)%Z.
  - rewrite /stack_frame_allocation_size.
    have := round_ws_range (sf_align e) (sf_stk_sz e + sf_stk_extra_sz e).
    lia.
  assert (top_stack_range := wunsigned_range (top_stack m)).
  split; last lia.
  rewrite Z.le_0_sub.
  exact: (aligned_alloc_no_overflow sz_pos extra_pos sf_noovf sp_align ok_m').
Qed.

Local Open Scope seq_scope.

Lemma map_li_of_copn_args_label_in_lcmd ii args :
  label_in_lcmd (map (li_of_copn_args ii) args) = [::].
Proof. by elim: args => [|[]]. Qed.

Lemma set_up_sp_register_label_in_lcmd liparams x sf_sz al y :
  label_in_lcmd (set_up_sp_register liparams x sf_sz al y) = [::].
Proof.
  rewrite /set_up_sp_register.
  case: lip_set_up_sp_register => // ?.
  by rewrite map_li_of_copn_args_label_in_lcmd.
Qed.

Lemma set_up_sp_stack_label_in_lcmd liparams x sf_sz al off :
  label_in_lcmd (set_up_sp_stack liparams x sf_sz al off) = [::].
Proof.
  rewrite /set_up_sp_stack.
  case: lip_set_up_sp_stack => // ?.
  by rewrite map_li_of_copn_args_label_in_lcmd.
Qed.

Lemma map_li_of_copn_args_has_label lbl ii args :
  has (is_label lbl) (map (li_of_copn_args ii) args) = false.
Proof. by elim: args => [|[]]. Qed.

Lemma set_up_sp_register_has_label lbl liparams x sf_sz al y :
  has (is_label lbl) (set_up_sp_register liparams x sf_sz al y) = false.
Proof.
  rewrite /set_up_sp_register.
  case: lip_set_up_sp_register => // ?.
  by rewrite map_li_of_copn_args_has_label.
Qed.

Lemma set_up_sp_stack_has_label lbl liparams x sf_sz al off :
  has (is_label lbl) (set_up_sp_stack liparams x sf_sz al off) = false.
Proof.
  rewrite /set_up_sp_stack.
  case: lip_set_up_sp_stack => // ?.
  by rewrite map_li_of_copn_args_has_label.
Qed.

Lemma all_has {T} (p q: pred T) (s: seq T) :
  all p s →
  has q s →
  exists2 t, List.In t s & p t && q t.
Proof.
  elim: s => // t s ih /= /andP[] pt ps /orP[] r.
  - exists t; first by left.
    by rewrite pt.
  by case: (ih ps r) => y Y Z; exists y; first right.
Qed.

Lemma align_bind ii a p1 l :
  (let: (lbl, lc) := align ii a p1 in (lbl, lc ++ l)) =

  align ii a (let: (lbl, lc) := p1 in (lbl, lc ++ l)).
Proof. by case: p1 a => lbl lc []. Qed.

Section CAT.

  Context
    (liparams : linearization_params)
    (p : sprog)
    (extra_free_registers : instr_info -> option var).

  Let linear_i := linear_i liparams p.

  Let Pi (i:instr) :=
    forall fn lbl tail,
     linear_i fn i lbl tail =
     let: (lbl, lc) := linear_i fn i lbl [::] in (lbl, lc ++ tail).

  Let Pr (i:instr_r) :=
    forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall fn lbl tail,
     linear_c (linear_i fn) c lbl tail =
     let: (lbl, lc) := linear_c (linear_i fn) c lbl [::] in (lbl, lc ++ tail).

  Let Pf (fd:sfundef) := True.

  Let HmkI: forall i ii, Pr i -> Pi (MkI ii i).
  Proof. by []. Qed.

  Let Hskip : Pc [::].
  Proof. by []. Qed.

  Let Hseq : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc fn lbl l /=.
    by rewrite Hc; case: linear_c => lbl1 lc1; rewrite Hi (Hi _ lbl1 lc1); case: linear_i => ??; rewrite catA.
  Qed.

  Let Hassgn : forall x tg ty e, Pr (Cassgn x tg ty e).
  Proof. by move => x tg [] // sz e ii lbl c /=; case: assert. Qed.

  Let Hopn : forall xs t o es, Pr (Copn xs t o es).
  Proof. by []. Qed.

  Let Hsyscall : forall xs o es, Pr (Csyscall xs o es).
  Proof. by []. Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii fn lbl l /=.
    case Heq1: (c1)=> [|i1 l1].
    + by rewrite Hc2 (Hc2 _ _ [:: _]); case: linear_c => lbl1 lc1; rewrite cats1 /= cat_rcons.
    rewrite -Heq1=> {Heq1 i1 l1};case Heq2: (c2)=> [|i2 l2].
    + by rewrite Hc1 (Hc1 _ _ [::_]); case: linear_c => lbl1 lc1; rewrite cats1 /= cat_rcons.
    rewrite -Heq2=> {Heq2 i2 l2}.
    rewrite Hc1 (Hc1 _ _ [::_]); case: linear_c => lbl1 lc1.
    rewrite Hc2 (Hc2 _ _ [::_ & _]); case: linear_c => lbl2 lc2.
    by rewrite /= !cats1 /= -!cat_rcons catA.
  Qed.

  Let Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir, lo, hi) c).
  Proof. by []. Qed.

  Let Hwhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    move=> a c e c' Hc Hc' ii fn lbl l /=.
    case: is_bool => [ [] | ].
    + rewrite Hc' (Hc' _ _ [:: _]) align_bind; f_equal; case: linear_c => lbl1 lc1.
      by rewrite Hc (Hc _ _ (_ ++ _)); case: linear_c => lbl2 lc2; rewrite !catA cats1 -cat_rcons.
    + by apply Hc.
    case: c' Hc' => [ _ | i c' ].
    + by rewrite Hc (Hc _ _ [:: _]) align_bind; case: linear_c => lbl1 lc1; rewrite /= cats1 cat_rcons.
    move: (i :: c') => { i c' } c' Hc'.
    rewrite Hc (Hc _ _ [:: _]); case: linear_c => lbl1 lc1.
    rewrite Hc' (Hc' _ _ (_ :: _)); case: linear_c => lbl2 lc2.
    rewrite /=. f_equal. f_equal.
    by case: a; rewrite /= cats1 -catA /= cat_rcons.
  Qed.

  Let Hcall : forall i xs f es, Pr (Ccall i xs f es).
  Proof.
    move => ini xs fn es ii fn' lbl tail /=.
    case: get_fundef => // fd; case: ifP => //.
    by case: sf_return_address => // [ ra | ra ra_ofs ] _; rewrite cats0 -catA.
  Qed.

  Lemma linear_i_nil fn i lbl tail :
     linear_i fn i lbl tail =
     let: (lbl, lc) := linear_i fn i lbl [::] in (lbl, lc ++ tail).
  Proof.
    apply (@instr_Rect _ _ Pr Pi Pc HmkI Hskip Hseq Hassgn Hopn Hsyscall Hif Hfor Hwhile Hcall).
  Qed.

  Lemma linear_c_nil fn c lbl tail :
     linear_c (linear_i fn) c lbl tail =
     let: (lbl, lc) := linear_c (linear_i fn) c lbl [::] in (lbl, lc ++ tail).
  Proof.
    apply (@cmd_rect _ _ Pr Pi Pc HmkI Hskip Hseq Hassgn Hopn Hsyscall Hif Hfor Hwhile Hcall).
  Qed.

End CAT.

(* Predicate describing valid labels occurring inside instructions:
    “valid_labels fn lo hi i” expresses that labels in instruction “i” are within the range [lo; hi[
    and that remote labels to a function other than “fn” are always 1.
*)
Definition valid_labels (fn: funname) (lo hi: label) (i: linstr) : bool :=
  match li_i i with
  | Lopn _ _ _
  | Lsyscall _
  | Lalign
  | Ligoto _
  | Lret
    => true
  | Llabel _ lbl
  | LstoreLabel _ lbl
  | Lcond _ lbl
    => (lo <=? lbl) && (lbl <? hi)
  | Lgoto (fn', lbl) | Lcall _ (fn', lbl) =>
    if fn' == fn then (lo <=? lbl) && (lbl <? hi) else lbl == 1
  end%positive.

Definition valid (fn: funname) (lo hi: label) (lc: lcmd) : bool :=
  all (valid_labels fn lo hi) lc.

Lemma valid_cat fn min max lc1 lc2 :
  valid fn min max (lc1 ++ lc2) = valid fn min max lc1 && valid fn min max lc2.
Proof. exact: all_cat. Qed.

Lemma valid_add_align fn lbl1 lbl2 ii a c :
  valid fn lbl1 lbl2 (add_align ii a c) = valid fn lbl1 lbl2 c.
Proof. by case: a. Qed.

Lemma valid_le_min min2 fn min1 max lc :
  (min1 <=? min2)%positive ->
  valid fn min2 max lc ->
  valid fn min1 max lc.
Proof.
  move => /Pos_leb_trans h; apply: sub_all; rewrite /valid_labels => -[_/=] [] // => [ _ [fn' lbl] | k lbl | [ fn' lbl ] | _ lbl | _ lbl ].
  1,3: case: ifP => // _.
  all: by case/andP => /h ->.
Qed.

Lemma valid_le_max max1 fn max2 min lc :
  (max1 <=? max2)%positive ->
  valid fn min max1 lc ->
  valid fn min max2 lc.
Proof.
  move => /Pos_lt_leb_trans h; apply: sub_all; rewrite /valid_labels => -[_/=] [] // => [ _ [fn' lbl] | k lbl | [ fn' lbl ] | _ lbl | _ lbl ].
  1,3: case: ifP => // _.
  all: by case/andP => -> /h.
Qed.

Lemma find_labelE lbl c :
  find_label lbl c =
  if c is i :: c'
  then
    if is_label lbl i
    then ok O
    else Let r := find_label lbl c' in ok r.+1
  else type_error.
Proof.
  case: c => // i c; rewrite /find_label /=.
  case: (is_label lbl i) => //.
  rewrite ltnS.
  by case: ifP.
Qed.

Lemma find_label_cat_hd lbl c1 c2:
  ~~ has (is_label lbl) c1 ->
  find_label lbl (c1 ++ c2) =
  (Let pc := find_label lbl c2 in ok (size c1 + pc)).
Proof.
  rewrite /find_label find_cat size_cat => /negbTE ->.
  by rewrite ltn_add2l;case:ifP.
Qed.

(** Disjoint labels: all labels in “c” are below “lo” or above “hi”. *)
Definition disjoint_labels (lo hi: label) (c: lcmd) : Prop :=
  ∀ lbl, (lo <= lbl < hi)%positive → ~~ has (is_label lbl) c.

Arguments disjoint_labels _%positive _%positive _.

Lemma disjoint_labels_cat lo hi P Q :
  disjoint_labels lo hi P →
  disjoint_labels lo hi Q →
  disjoint_labels lo hi (P ++ Q).
Proof.
  by move => p q lbl r; rewrite has_cat negb_or (p _ r) (q _ r).
Qed.

Lemma disjoint_labels_w lo' hi' lo hi P :
  (lo' <= lo)%positive →
  (hi <= hi')%positive →
  disjoint_labels lo' hi' P →
  disjoint_labels lo hi P.
Proof. move => L H k lbl ?; apply: k; lia. Qed.

Lemma disjoint_labels_wL lo' lo hi P :
  (lo' <= lo)%positive →
  disjoint_labels lo' hi P →
  disjoint_labels lo hi P.
Proof. move => L; apply: (disjoint_labels_w L); lia. Qed.

Lemma disjoint_labels_wH hi' lo hi P :
  (hi <= hi')%positive →
  disjoint_labels lo hi' P →
  disjoint_labels lo hi P.
Proof. move => H; apply: (disjoint_labels_w _ H); lia. Qed.

Lemma valid_disjoint_labels fn A B C D P :
  valid fn A B P →
  (D <= A)%positive ∨ (B <= C)%positive →
  disjoint_labels C D P.
Proof.
  move => V U lbl [L H]; apply/negP => K.
  have {V K} [i _ /andP[] ] := all_has V K.
  case: i => ii [] // k lbl' /andP[] /Pos.leb_le a /Pos.ltb_lt b /eqP ?; subst lbl'.
  lia.
Qed.

Lemma valid_has_not_label fn A B P lbl :
  valid fn A B P →
  (lbl < A ∨ B <= lbl)%positive →
  ~~ has (is_label lbl) P.
Proof.
  move => /(valid_disjoint_labels) - /(_ lbl (lbl + 1)%positive) V R; apply: V; lia.
Qed.

Definition LSem_step p s1 s2 :
  lsem1 p s1 s2 -> lsem p s1 s2 := rt_step _ _ s1 s2.

Lemma snot_spec gd s e b :
  sem_pexpr gd s e = ok (Vbool b) →
  sem_pexpr gd s (snot e) = sem_pexpr gd s (Papp1 Onot e).
Proof.
elim: e b => //.
- by case => // e _ b; rewrite /= /sem_sop1 /=; t_xrbindP => z -> b' /to_boolI -> _ /=;
  rewrite negbK.
- by case => // e1 He1 e2 He2 b /=; t_xrbindP => v1 h1 v2 h2 /sem_sop2I [b1 [b2 [b3]]] []
  /to_boolI hb1 /to_boolI hb2 [?] ?; subst v1 v2 b3;
  rewrite /= (He1 _ h1) (He2 _ h2) /= h1 h2;
  apply: (f_equal (@Ok _ _)); rewrite /= ?negb_and ?negb_or.
move => st p hp e1 he1 e2 he2 b /=.
t_xrbindP => bp vp -> /= -> trv1 v1 h1 htr1 trv2 v2 h2 htr2 /= h.
have : exists (b1 b2:bool), st = sbool /\ sem_pexpr gd s e1 = ok (Vbool b1) /\ sem_pexpr gd s e2 = ok (Vbool b2).
+ rewrite h1 h2;case: bp h => ?;subst.
  + have [??]:= truncate_valI htr1;subst st v1.
    by move: htr2; rewrite /truncate_val; t_xrbindP => /= b2 /to_boolI -> ?;eauto.
  have [??]:= truncate_valI htr2;subst st v2.
  by move: htr1; rewrite /truncate_val; t_xrbindP => /= b1 /to_boolI -> ?;eauto.
move=> [b1 [b2 [-> []/dup[]hb1 /he1 -> /dup[]hb2 /he2 ->]]] /=.
by rewrite hb1 hb2 /=; case bp.
Qed.

Lemma add_align_nil ii a c : add_align ii a c = add_align ii a [::] ++ c.
Proof. by case: a. Qed.

Definition is_linear_of (p : lprog) (fn : funname) (c : lcmd) : Prop :=
  exists2 fd,
    get_fundef (lp_funcs p) fn = Some fd
    & lfd_body fd = c.


Section LINEARIZATION_PARAMS.

Context
  (liparams : linearization_params).

Record h_linearization_params :=
  {
    spec_lip_allocate_stack_frame :
      forall (lp : lprog) sp_rsp fn (s : estate) pc ii ts sz,
        let rsp := vid sp_rsp in
        let vm := evm s in
        let args := lip_allocate_stack_frame liparams rsp sz in
        let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
        let ts' := pword_of_word (ts - wrepr Uptr sz) in
        let s' := with_vm s (vm.[rsp <- ok ts'])%vmap in
        (vm.[rsp])%vmap = ok (pword_of_word ts)
        -> eval_instr lp i (of_estate s fn pc)
           = ok (of_estate s' fn pc.+1);

    spec_lip_free_stack_frame :
      forall (lp : lprog) sp_rsp fn (s : estate) pc ii ts sz,
        let rsp := vid sp_rsp in
        let vm := evm s in
        let args := lip_free_stack_frame liparams rsp sz in
        let i := MkLI ii (Lopn args.1.1 args.1.2 args.2) in
        let ts' := pword_of_word (ts + wrepr Uptr sz) in
        let s' := with_vm s (vm.[rsp <- ok ts'])%vmap in
        (vm.[rsp])%vmap = ok (pword_of_word ts)
        -> eval_instr lp i (of_estate s fn pc)
           = ok (of_estate s' fn pc.+1);

    spec_lip_set_up_sp_register :
      forall (lp : lprog) sp_rsp fn (s : estate) r ts al sz P Q,
        let: vrspi := vid sp_rsp in
        let: vrsp := v_var vrspi in
        let: vtmpi := vid (lip_tmp liparams) in
        let: vtmp := v_var vtmpi in
        let: ts' := align_word al (ts - wrepr Uptr sz) in
        let : lcmd := set_up_sp_register liparams vrspi sz al r in
        is_linear_of lp fn (P ++ lcmd ++ Q)
        -> isSome (lip_set_up_sp_register liparams vrspi sz al r)
        -> vtype r = sword Uptr
        -> vtmp <> vrsp
        -> vname (v_var r) \notin (lip_not_saved_stack liparams)
        -> v_var r <> vrsp
        -> get_var (evm s) vrsp = ok (Vword ts)
        -> wf_vm (evm s)
        -> exists vm',
            let: ls := of_estate s fn (size P) in
            let: s' := with_vm s vm' in
            let: ls' := of_estate s' fn (size P + size lcmd) in
            [/\ lsem lp ls ls'
              , wf_vm vm'
              , vm' = (evm s)
                  [\ Sv.add (v_var r) (Sv.add vtmp (Sv.add vrsp vflags)) ]
              , get_var vm' vrsp = ok (Vword ts')
              , get_var vm' (v_var r) = ok (Vword ts)
              & forall x,
                  Sv.In x vflags
                  -> ~ is_ok (vm'.[x]%vmap)
                  -> (evm s).[x]%vmap = vm'.[x]%vmap
            ];

    spec_lip_set_up_sp_stack :
      forall (lp : lprog) sp_rsp fn (s : estate) ts m' al sz off P Q,
        let: vrspi := vid sp_rsp in
        let: vrsp := v_var vrspi in
        let: vtmpi := vid (lip_tmp liparams) in
        let: vtmp := v_var vtmpi in
        let: ts' := align_word al (ts - wrepr Uptr sz) in
        let : lcmd := set_up_sp_stack liparams vrspi sz al off in
        is_linear_of lp fn (P ++ lcmd ++ Q)
        -> isSome (lip_set_up_sp_stack liparams vrspi sz al off)
        -> vtmp <> vrsp
        -> get_var (evm s) vrsp = ok (Vword ts)
        -> wf_vm (evm s)
        -> write (emem s) (ts' + wrepr Uptr off)%R ts = ok m'
        -> exists vm',
             let: ls := of_estate s fn (size P) in
             let: s' := {| escs := escs s; evm := vm'; emem := m'; |} in
             let: ls' := of_estate s' fn (size P + size lcmd) in
             [/\ lsem lp ls ls'
               , wf_vm vm'
               , vm' = (evm s) [\ Sv.add vtmp (Sv.add vrsp vflags) ]
               , get_var vm' vrsp = ok (Vword ts')
               & forall x,
                   Sv.In x vflags
                   -> ~ is_ok (vm'.[x]%vmap)
                   -> (evm s).[x]%vmap = vm'.[x]%vmap
             ];

    hlip_lassign :
      forall
        (lp : lprog) fn (s1 s2 : estate) pc ii x e ws li ws'
        (w : word ws) (w' : word ws'),
        lassign liparams x ws e = Some li
        -> sem_pexpr [::] s1 e = ok (Vword w')
        -> truncate_word ws w' = ok w
        -> write_lval [::] x (Vword w) s1 = ok s2
        -> eval_instr lp (MkLI ii li) (of_estate s1 fn pc)
           = ok (of_estate s2 fn pc.+1);
  }.

Section HLIPARAMS.
  Context
    (hliparams : h_linearization_params).

  Lemma spec_lassign
    lp s1 s2 x e ws ws' (w : word ws) (w' : word ws') ii fn pc :
    isSome (lassign liparams x ws e)
    -> sem_pexpr [::] s1 e = ok (Vword w')
    -> truncate_word ws w' = ok w
    -> write_lval [::] x (Vword w) s1 = ok s2
    -> let li := of_olinstr_r ii (lassign liparams x ws e) in
       eval_instr lp li (of_estate s1 fn pc) = ok (of_estate s2 fn pc.+1).
  Proof.
    case h: lassign => [li|] // _.
    move: h.
    exact: hlip_lassign.
  Qed.

  Lemma spec_lmove lp s1 s2 x ws (w : word ws) y ii fn pc :
    isSome (lmove liparams x ws y)
    -> get_gvar [::] (evm s1) y = ok (Vword w)
    -> write_var x (Vword w) s1 = ok s2
    -> let li := of_olinstr_r ii (lmove liparams x ws y) in
       eval_instr lp li (of_estate s1 fn pc) = ok (of_estate s2 fn pc.+1).
  Proof.
    rewrite /lmove.
    move=> h hsemy.
    apply: (spec_lassign lp (x := Lvar x) (e := Pvar y) _ _ _ h hsemy).
    exact: truncate_word_u.
  Qed.

  Lemma valid_lassign fn lbl0 lbl1 ii x w e :
    valid fn lbl0 lbl1 [:: of_olinstr_r ii (lassign liparams x w e) ].
  Proof. rewrite /lassign. by case: lip_lassign => [[[? ?] ?]|]. Qed.

End HLIPARAMS.

End LINEARIZATION_PARAMS.

(** Technical lemma about the compilation: monotony and unicity of labels. *)
Section VALIDITY.
  Context
    (p : sprog)
    (extra_free_registers : instr_info -> option var)
    (lp : lprog)
    (liparams : linearization_params)
    (hliparams : h_linearization_params liparams).

  Let Pr (i: instr_r) : Prop :=
    ∀ ii fn lbl,
      let: (lbli, li) :=
         linear_i liparams p fn (MkI ii i) lbl [::] in
      (lbl <= lbli)%positive ∧ valid fn lbl lbli li.

  Let Pi (i: instr) : Prop :=
    ∀ fn lbl,
      let: (lbli, li) :=
         linear_i liparams p fn i lbl [::] in
      (lbl <= lbli)%positive ∧ valid fn lbl lbli li.

  Let Pc (c: cmd) : Prop :=
    ∀ fn lbl,
      let: (lblc, lc) :=
         linear_c (linear_i liparams p fn) c lbl [::] in
      (lbl <= lblc)%positive ∧ valid fn lbl lblc lc.

  Let HMkI i ii : Pr i → Pi (MkI ii i).
  Proof. exact. Qed.

  Let Hnil : Pc [::].
  Proof. move => fn lbl /=; split => //; lia. Qed.

  Let Hcons (i : instr) (c : cmd) : Pi i → Pc c → Pc (i :: c).
  Proof.
    move => hi hc fn lbl /=.
    case: linear_c (hc fn lbl) => lblc lc [Lc Vc]; rewrite linear_i_nil.
    case: linear_i (hi fn lblc) => lbli li [Li Vi]; split; first lia.
    rewrite valid_cat; apply/andP; split.
    - apply: valid_le_min _ Vi; apply/Pos.leb_le; lia.
    apply: valid_le_max _ Vc; apply/Pos.leb_le; lia.
  Qed.

  Let Hassign (x : lval) (tg : assgn_tag) (ty : stype) (e : pexpr) : Pr (Cassgn x tg ty e).
  Proof.
    move => ii fn lbl /=.
    case: ty;
      (split => //; first exact: Pos.le_refl).
    exact: valid_lassign.
  Qed.

  Let Hopn (xs : lvals) (t : assgn_tag) (o : sopn) (es : pexprs) : Pr (Copn xs t o es).
  Proof. split => //; exact: Pos.le_refl. Qed.

  Let Hsyscall (xs : lvals) (o : syscall_t) (es : pexprs) : Pr (Csyscall xs o es).
  Proof. split => //; exact: Pos.le_refl. Qed.

  Let Hif (e : pexpr) (c1 c2 : cmd) : Pc c1 → Pc c2 → Pr (Cif e c1 c2).
  Proof.
    move => hc1 hc2 ii fn lbl /=.
    case: c1 hc1 => [ | i1 c1 ] hc1.
    - rewrite linear_c_nil.
      case: linear_c (hc2 fn (next_lbl lbl)); rewrite /next_lbl => lblc2 lc2 [L2 V2]; split; first lia.
      have lbl_lt_lblc2 : (lbl <? lblc2)%positive by apply/Pos.ltb_lt; lia.
      rewrite /= valid_cat /= /valid_labels /= Pos.leb_refl /= lbl_lt_lblc2 /= andbT.
      apply: valid_le_min _ V2; apply/Pos.leb_le; lia.
    case: c2 hc2 => [ | i2 c2 ] hc2.
    - rewrite linear_c_nil.
      case: linear_c (hc1 fn (next_lbl lbl)); rewrite /next_lbl => lblc1 lc1 [L1 V1]; split; first lia.
      have lbl_lt_lblc1 : (lbl <? lblc1)%positive by apply/Pos.ltb_lt; lia.
      rewrite /= valid_cat /= /valid_labels /= Pos.leb_refl /= lbl_lt_lblc1 /= andbT.
      apply: valid_le_min _ V1; apply/Pos.leb_le; lia.
    rewrite linear_c_nil.
    case: linear_c (hc1 fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc1 lc1 [L1 V1].
    rewrite linear_c_nil.
    case: linear_c (hc2 fn lblc1) => lblc2 lc2 [L2 V2]; split; first lia.
    have lbl_lt_lblc2 : (lbl <? lblc2)%positive by apply/Pos.ltb_lt; lia.
    have lblp1_lt_lblc2 : (lbl + 1 <? lblc2)%positive by apply/Pos.ltb_lt; lia.
    have lbl_le_lblp1 : (lbl <=? lbl + 1)%positive by apply/Pos.leb_le; lia.
    rewrite /= valid_cat /= valid_cat /= /valid_labels /= Pos.leb_refl /= eqxx lbl_lt_lblc2 lblp1_lt_lblc2 lbl_le_lblp1 /= andbT.
    apply/andP; split.
    - apply: valid_le_min _ V2; apply/Pos.leb_le; lia.
    apply: valid_le_min; last apply: valid_le_max _ V1.
    all: apply/Pos.leb_le; lia.
  Qed.

  Let Hfor (v : var_i) (d: dir) (lo hi : pexpr) (c : cmd) : Pc c → Pr (Cfor v (d, lo, hi) c).
  Proof. split => //; exact: Pos.le_refl. Qed.

  Let Hwhile (a : expr.align) (c : cmd) (e : pexpr) (c' : cmd) : Pc c → Pc c' → Pr (Cwhile a c e c').
  Proof.
    move => hc hc' ii fn lbl /=.
    case: is_boolP => [ [] | {e} e ].
    - rewrite linear_c_nil.
      case: linear_c (hc' fn (next_lbl lbl)); rewrite /next_lbl => lblc' lc' [Lc' Vc'].
      rewrite linear_c_nil.
      case: linear_c (hc fn lblc') => lblc lc [Lc Vc] /=; split; first lia.
      have lbl_lt_lblc : (lbl <? lblc)%positive by apply/Pos.ltb_lt; lia.
      rewrite valid_add_align /= !valid_cat /= /valid_labels /= Pos.leb_refl eqxx lbl_lt_lblc /= andbT.
      apply/andP; split.
      - apply: valid_le_min _ Vc; apply/Pos.leb_le; lia.
      apply: valid_le_max; last apply: valid_le_min _ Vc'; apply/Pos.leb_le; lia.
    - by case: linear_c (hc fn lbl).
    case: c' hc' => [ | i' c' ] hc'.
    - rewrite linear_c_nil.
      case: linear_c (hc fn (next_lbl lbl)); rewrite /next_lbl => lblc lc [Lc Vc] /=; split; first lia.
      have lbl_lt_lblc : (lbl <? lblc)%positive by apply/Pos.ltb_lt; lia.
      rewrite valid_add_align /= valid_cat /= /valid_labels /= Pos.leb_refl lbl_lt_lblc /= andbT.
      apply: valid_le_min _ Vc; apply/Pos.leb_le; lia.
    rewrite linear_c_nil.
    case: linear_c (hc fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc lc [Lc Vc].
    rewrite linear_c_nil.
    case: linear_c (hc' fn lblc) => lblc' lc' [Lc' Vc'] /=; split; first lia.
    have lbl_lt_lblc' : (lbl <? lblc')%positive by apply/Pos.ltb_lt; lia.
    have lbl_le_lblp1 : (lbl <=? lbl + 1)%positive by apply/Pos.leb_le; lia.
    have lblp1_lt_lblc' : (lbl + 1 <? lblc')%positive by apply/Pos.ltb_lt; lia.
    rewrite valid_add_align /= valid_cat /= valid_cat /= /valid_labels /= eqxx Pos.leb_refl lbl_lt_lblc' lbl_le_lblp1 lblp1_lt_lblc' /= andbT.
    apply/andP; split.
    - apply: valid_le_min _ Vc'; apply/Pos.leb_le; lia.
    apply: valid_le_min; last apply: valid_le_max _ Vc.
    all: apply/Pos.leb_le; lia.
  Qed.

  Remark valid_allocate_stack_frame fn lbl b ii z rastack :
    valid fn lbl (lbl + 1)%positive (allocate_stack_frame liparams p b ii z rastack).
  Proof. by rewrite /allocate_stack_frame; case: eqP. Qed.

  Let Hcall (i : inline_info) (xs : lvals) (f : funname) (es : pexprs) : Pr (Ccall i xs f es).
  Proof.
    move => ii fn lbl /=.
    case: get_fundef => [ fd | ]; last by split => //; lia.
    case: eqP; first by split => //; lia.
    have lbl_lt_lblp1 : (lbl <? lbl + 1)%positive by apply/Pos.ltb_lt; lia.
    rewrite /next_lbl; split; first lia.
    rewrite valid_cat /= valid_cat !valid_allocate_stack_frame /= /valid_labels /= Pos.leb_refl lbl_lt_lblp1 /= andbT.
    case: eqP => _ //.
    by rewrite Pos.leb_refl lbl_lt_lblp1.
  Qed.

  Definition linear_has_valid_labels : ∀ c, Pc c :=
    @cmd_rect _ _ Pr Pi Pc HMkI Hnil Hcons Hassign Hopn Hsyscall Hif Hfor Hwhile Hcall.

  Definition linear_has_valid_labels_instr : ∀ i, Pi i :=
    @instr_Rect _ _ Pr Pi Pc HMkI Hnil Hcons Hassign Hopn Hsyscall Hif Hfor Hwhile Hcall.

End VALIDITY.

Section NUMBER_OF_LABELS.
  Context
    (p : sprog)
    (extra_free_registers : instr_info -> option var)
    (lp : lprog)
    (liparams : linearization_params)
    (hliparams : h_linearization_params liparams).

  Let Pr (i: instr_r) : Prop :=
    ∀ ii fn lbl,
      let: (lbli, li) :=
         linear_i liparams p fn (MkI ii i) lbl [::] in
      (Z.of_nat (size (label_in_lcmd li)) + lbl <= lbli)%Z.

  Let Pi (i: instr) : Prop :=
    ∀ fn lbl,
      let: (lbli, li) :=
         linear_i liparams p fn i lbl [::] in
      (Z.of_nat (size (label_in_lcmd li)) + lbl <= lbli)%Z.

  Let Pc (c: cmd) : Prop :=
    ∀ fn lbl,
      let: (lblc, lc) :=
         linear_c (linear_i liparams p fn) c lbl [::] in
      (Z.of_nat (size (label_in_lcmd lc)) + lbl <= lblc)%Z.

  Lemma label_in_lcmd_cat lc1 lc2 :
    label_in_lcmd (lc1 ++ lc2) = label_in_lcmd lc1 ++ label_in_lcmd lc2.
  Proof. by rewrite /label_in_lcmd pmap_cat. Qed.

  Let HMkI i ii : Pr i → Pi (MkI ii i).
  Proof. exact. Qed.

  Let Hnil : Pc [::].
  Proof. by move => fn lbl; apply Z.le_refl. Qed.

  Let Hcons (i : instr) (c : cmd) : Pi i → Pc c → Pc (i :: c).
  Proof.
    move => hi hc fn lbl /=.
    case: linear_c (hc fn lbl) => lblc lc Lc; rewrite linear_i_nil.
    case: linear_i (hi fn lblc) => lbli li Li.
    rewrite label_in_lcmd_cat size_cat Nat2Z.inj_add.
    lia.
  Qed.

  Lemma get_label_lassign ii x ws e :
    get_label (of_olinstr_r ii (lassign liparams x ws e)) = None.
  Proof.
    rewrite /of_olinstr_r /lassign.
    by case: lip_lassign => [[[??]?]|].
  Qed.

  Let Hassign (x : lval) (tg : assgn_tag) (ty : stype) (e : pexpr) : Pr (Cassgn x tg ty e).
  Proof.
    move => ii fn lbl /=.
    case: ty => /=; try lia.
    move=> ws.
    by rewrite get_label_lassign /=; apply Z.le_refl.
  Qed.

  Let Hopn (xs : lvals) (t : assgn_tag) (o : sopn) (es : pexprs) : Pr (Copn xs t o es).
  Proof. by move=> ii fn lbl /=; apply Z.le_refl. Qed.

  Let Hsyscall (xs : lvals) (o : syscall_t) (es : pexprs) : Pr (Csyscall xs o es).
  Proof. by move=> ii fn lbl /=; apply Z.le_refl. Qed.

  Let Hif (e : pexpr) (c1 c2 : cmd) : Pc c1 → Pc c2 → Pr (Cif e c1 c2).
  Proof.
    move=> hc1 hc2 ii fn lbl /=.
    case: c1 hc1 => [ | i1 c1 ] hc1.
    - rewrite linear_c_nil.
      case: linear_c (hc2 fn (next_lbl lbl)); rewrite /next_lbl => lblc2 lc2 L2.
      rewrite /= label_in_lcmd_cat /= cats0.
      lia.
    case: c2 hc2 => [ | i2 c2 ] hc2.
    - rewrite linear_c_nil.
      case: linear_c (hc1 fn (next_lbl lbl)); rewrite /next_lbl => lblc1 lc1 L1.
      rewrite /= label_in_lcmd_cat /= cats0.
      lia.
    rewrite linear_c_nil.
    case: linear_c (hc1 fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc1 lc1 l1.
    rewrite linear_c_nil.
    case: linear_c (hc2 fn lblc1) => lblc2 lc2 L2.
    rewrite /= label_in_lcmd_cat size_cat Nat2Z.inj_add /=.
    rewrite label_in_lcmd_cat /= cats0.
    lia.
  Qed.

  Let Hfor (v : var_i) (d: dir) (lo hi : pexpr) (c : cmd) : Pc c → Pr (Cfor v (d, lo, hi) c).
  Proof. by move=> hc ii fn lbl /=; apply Z.le_refl. Qed.

  Lemma label_in_lcmd_add_align ii al lc :
    label_in_lcmd (add_align ii al lc) = label_in_lcmd lc.
  Proof. by case: al. Qed.

  Let Hwhile (a : expr.align) (c : cmd) (e : pexpr) (c' : cmd) : Pc c → Pc c' → Pr (Cwhile a c e c').
  Proof.
    move => hc hc' ii fn lbl /=.
    case: is_boolP => [ [] | {e} e ].
    - rewrite linear_c_nil.
      case: linear_c (hc' fn (next_lbl lbl)); rewrite /next_lbl => lblc' lc' Lc'.
      rewrite linear_c_nil.
      case: linear_c (hc fn lblc') => lblc lc Lc /=.
      rewrite label_in_lcmd_add_align /=.
      rewrite label_in_lcmd_cat size_cat Nat2Z.inj_add /=.
      rewrite label_in_lcmd_cat /= cats0.
      lia.
    - by case: linear_c (hc fn lbl).
    case: c' hc' => [ | i' c' ] hc'.
    - rewrite linear_c_nil.
      case: linear_c (hc fn (next_lbl lbl)); rewrite /next_lbl => lblc lc Lc /=.
      rewrite label_in_lcmd_add_align /=.
      rewrite label_in_lcmd_cat /= cats0.
      lia.
    rewrite linear_c_nil.
    case: linear_c (hc fn (next_lbl (next_lbl lbl))); rewrite /next_lbl => lblc lc Lc.
    rewrite linear_c_nil.
    case: linear_c (hc' fn lblc) => lblc' lc' Lc'.
    rewrite /= label_in_lcmd_add_align /=.
    rewrite label_in_lcmd_cat size_cat Nat2Z.inj_add /=.
    rewrite label_in_lcmd_cat /= cats0.
    lia.
  Qed.

  Remark label_in_lcmd_allocate_stack_frame b ii z rastack :
    label_in_lcmd (allocate_stack_frame liparams p b ii z rastack) = [::].
  Proof. by rewrite /allocate_stack_frame; case: eqP. Qed.

  Remark label_in_lcmd_push_to_save ii to_save :
    label_in_lcmd (push_to_save liparams p ii to_save) = [::].
  Proof.
    elim: to_save => [|[x ofs] to_save ih] //=.
    case: is_word_type => [ws|] //=.
    by rewrite /lstore get_label_lassign /=.
  Qed.

  Remark label_in_lcmd_pop_to_save ii to_save :
    label_in_lcmd (pop_to_save liparams p ii to_save) = [::].
  Proof.
    elim: to_save => [|[x ofs] to_save ih] //=.
    case: is_word_type => [ws|] //=.
    by rewrite /lload get_label_lassign /=.
  Qed.

  Let Hcall (i : inline_info) (xs : lvals) (f : funname) (es : pexprs) : Pr (Ccall i xs f es).
  Proof.
    move => ii fn lbl /=.
    case: get_fundef => [ fd | ]; last by apply Z.le_refl.
    case: eqP => /=; first by lia.
    rewrite /next_lbl label_in_lcmd_cat label_in_lcmd_allocate_stack_frame.
    rewrite [size _]/= Nat2Z.inj_succ.
    rewrite label_in_lcmd_cat label_in_lcmd_allocate_stack_frame.
    rewrite [Z.of_nat _]/=; lia.
  Qed.

  Definition linear_c_nb_labels : ∀ c, Pc c :=
    @cmd_rect _ _ Pr Pi Pc HMkI Hnil Hcons Hassign Hopn Hsyscall Hif Hfor Hwhile Hcall.

  Definition linear_i_nb_labels : ∀ i, Pi i :=
    @instr_Rect _ _ Pr Pi Pc HMkI Hnil Hcons Hassign Hopn Hsyscall Hif Hfor Hwhile Hcall.

  Lemma linear_body_nb_labels fn e body :
    let: (lbl, lc) := linear_body liparams p fn e body in
    (Z.of_nat (size (label_in_lcmd lc)) <= lbl)%Z.
  Proof.
    rewrite /linear_body.
    case h: match _ with | RAnone => _ | _ => _ end => [[tail head] lbl0].
    rewrite linear_c_nil.
    have := linear_c_nb_labels body fn lbl0.
    case: linear_c => [lbl lc] /=.
    rewrite !label_in_lcmd_cat !size_cat !Nat2Z.inj_add.
    suff: (Z.of_nat (size (label_in_lcmd head)) + Z.of_nat (size (label_in_lcmd tail)) <= lbl0)%Z
      by lia.
    move: h.
    case: sf_return_address => [|x|ra z].
    + case: sf_save_stack => [|x|z] [<- <- <-] //=.
      + rewrite set_up_sp_register_label_in_lcmd /=.
        by rewrite /lmove get_label_lassign.

      rewrite !label_in_lcmd_cat.
      rewrite set_up_sp_stack_label_in_lcmd /=.
      rewrite label_in_lcmd_push_to_save /=.
      rewrite label_in_lcmd_pop_to_save /=.
      by rewrite get_label_lassign.

    + by move=> [<- <- <-] /=.
    by move=> [<- <- <-] /=; case: ra => //= r; case: get_label.
  Qed.

End NUMBER_OF_LABELS.

Section PROOF.

  Context
    (liparams : linearization_params)
    (hliparams : h_linearization_params liparams)
    (p : sprog)
    (extra_free_registers : instr_info -> option var)
    (p' : lprog).

  Let vgd : var := Var (sword Uptr) (sp_rip (p_extra p)).
  Let vrsp : var := Var (sword Uptr) (sp_rsp (p_extra p)).
  Let vrspi : var_i := {| v_var := vrsp; v_info := dummy_var_info; |}.
  Let vrspg : gvar := {| gv := vrspi; gs := Slocal; |}.

  Let var_tmp : var_i := vid (lip_tmp liparams).
  Let var_tmpg := {| gv := var_tmp; gs := Slocal; |}.

  Hypothesis var_tmp_not_magic : ~~ Sv.mem var_tmp (magic_variables p).

  Hypothesis linear_ok : linear_prog liparams p = ok p'.

  Notation is_linear_of := (is_linear_of p').
  Notation check_i := (check_i liparams p).
  Notation check_fd := (check_fd liparams p).
  Notation linear_i := (linear_i liparams p).
  Notation linear_c fn := (linear_c (linear_i fn)).
  Notation linear_fd := (linear_fd liparams p).

  Notation sem_I := (sem_one_varmap.sem_I p var_tmp).
  Notation sem_i := (sem_one_varmap.sem_i p var_tmp).
  Notation sem := (sem_one_varmap.sem p var_tmp).

  Notation valid_c fn c :=
    (linear_has_valid_labels p liparams c fn).
  Notation valid_i fn i :=
    (linear_has_valid_labels_instr p liparams i fn).

  Notation set_up_sp_register := (set_up_sp_register liparams).
  Notation set_up_sp_stack := (set_up_sp_stack liparams).

  Lemma hneq_vtmp_vrsp :
    v_var var_tmp <> vrsp.
  Proof.
    move: var_tmp_not_magic.
    move=> /Sv_memP.
    t_notin_add.
    by move=> /Sv.singleton_spec.
  Qed.

  Definition checked_i fn i : bool :=
    if get_fundef (p_funcs p) fn is Some fd
    then
      if check_i fn fd.(f_extra).(sf_align) i is Ok tt
      then true
      else false
    else false.

  Lemma checked_iE fn i :
    checked_i fn i →
    exists2 fd, get_fundef (p_funcs p) fn = Some fd & check_i fn fd.(f_extra).(sf_align) i = ok tt.
    Proof.
      rewrite /checked_i; case: get_fundef => // fd h; exists fd; first by [].
      by case: check_i h => // - [].
    Qed.

  Definition checked_c fn c : bool :=
    if get_fundef (p_funcs p) fn is Some fd
    then
      if check_c (check_i fn fd.(f_extra).(sf_align)) c is Ok tt
      then true
      else false
    else false.

  Lemma checked_cE fn c :
    checked_c fn c →
    exists2 fd, get_fundef (p_funcs p) fn = Some fd & check_c (check_i fn fd.(f_extra).(sf_align)) c = ok tt.
    Proof.
      rewrite /checked_c; case: get_fundef => // fd h; exists fd; first by [].
      by case: check_c h => // - [].
    Qed.

    Lemma checked_cI fn i c :
      checked_c fn (i :: c) →
      checked_i fn i ∧ checked_c fn c.
    Proof.
      by case/checked_cE => fd ok_fd; rewrite /checked_c /checked_i ok_fd /= ; t_xrbindP => -> ->.
    Qed.

  Local Lemma p_globs_nil : p_globs p = [::].
  Proof.
    by move: linear_ok; rewrite /linear_prog; t_xrbindP => _ /eqP /size0nil.
  Qed.

  Local Lemma checked_prog fn fd :
    get_fundef (p_funcs p) fn = Some fd →
    check_fd fn fd = ok tt.
  Proof.
    move: linear_ok; rewrite /linear_prog; t_xrbindP => ok_p _ _ _.
    move: ok_p; rewrite /check_prog; t_xrbindP => r C _ M.
    by have [[]]:= get_map_cfprog_name_gen C M.
  Qed.

  Lemma get_fundef_p' f fd :
    get_fundef (p_funcs p) f = Some fd →
    get_fundef (lp_funcs p') f
    = Some (linear_fd f fd).2.
  Proof.
    move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ <- /=.
    elim: (p_funcs p) 1%positive => [|[f' fd'] funcs ih] nb_lbl //=.
    set nb_lbl' := (nb_lbl + _)%positive.
    move: (ih nb_lbl').
    case hfmap: fmap => [nb_lbl'' funcs''] /= {}ih.
    case: eqP => [|_ //].
    by move=> <- [->].
  Qed.

  Lemma lp_ripE : lp_rip p' = sp_rip p.(p_extra).
  Proof. by move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ <-. Qed.

  Lemma lp_rspE : lp_rsp p' = sp_rsp p.(p_extra).
  Proof. by move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ <-. Qed.

  Lemma lp_globsE : lp_globs p' = sp_globs p.(p_extra).
  Proof. by move: linear_ok; rewrite /linear_prog; t_xrbindP => _ _ _ <-. Qed.

  Lemma fmap_linear_fd_acc lbl funcs :
    let (nb_lbl, funcs') :=
      fmap (fun nb_lbl '(f,fd) =>
        let fd := linear_fd f fd in
        ((nb_lbl + fd.1)%positive, (f, fd.2))) 1%positive funcs
    in
    fmap (fun nb_lbl '(f,fd) =>
      let fd := linear_fd f fd in
      ((nb_lbl + fd.1)%positive, (f, fd.2))) (1+lbl)%positive funcs = ((nb_lbl + lbl)%positive, funcs').
  Proof.
    elim: funcs lbl => [|[f fd] funcs ih] lbl //=.
    set linear_f := (fun _ => _).
    have := ih ((linear_body liparams p f (f_extra fd) (f_body fd)).1)%positive.
    have := ih (lbl + (linear_body liparams p f (f_extra fd) (f_body fd)).1)%positive.
    case: fmap => [nb_lbl' funcs'].
    rewrite Pos.add_assoc => -> ->.
    by rewrite (Pos.add_comm lbl) Pos.add_assoc.
  Qed.

  Lemma small_dom_p' : small_dom (label_in_lprog p').
  Proof.
    move: linear_ok; rewrite /linear_prog.
    t_xrbindP=> _ _ /ZleP hle <-.
    rewrite /small_dom /label_in_lprog; apply /ZleP.
    apply: Z.le_trans hle.

    elim: (p_funcs p) => [|[fn f'] funcs ih] //=.
    have := fmap_linear_fd_acc ((linear_fd fn f').1)%positive funcs.
    case: fmap ih => [nb_lbl funcs'] /= ih -> /=.
    rewrite size_cat size_map Nat2Z.inj_add.
    have := linear_body_nb_labels p liparams fn (f_extra f') (f_body f').
    case: linear_body => [nb_lbl' lc] /=.
    lia.
  Qed.

  Local Coercion emem : estate >-> mem.
  Local Coercion evm : estate >-> vmap.

  (** Relation between source and target memories
      - There is a well-aligned valid block in the target
   *)
  Record match_mem (m m': mem) : Prop :=
    MM {
       read_incl  : ∀ p w, read m p U8 = ok w → read m' p U8 = ok w
     ; valid_incl : ∀ p, validw m p U8 → validw m' p U8
     ; valid_stk  : ∀ p,
         (wunsigned (stack_limit m) <= wunsigned p < wunsigned(stack_root m))%Z
       → validw m' p U8
      }.

  Lemma mm_free m1 m1' :
    match_mem m1 m1' →
    match_mem (free_stack m1) m1'.
  Proof.
  case => Hrm Hvm Hsm; split.
  (* read *)
  + move=> p1 w1 Hr.
    apply: Hrm. rewrite -Hr. apply: fss_read_old; [ exact: free_stackP | exact: readV Hr ].
  (* valid *)
  + move=> p1 Hv.
    assert (Hs := free_stackP). move: (Hs m1)=> Hm1. move: (Hs m1')=> Hm1'.
    have Heq := (fss_valid Hm1). have Heq' := (fss_valid Hm1').
    apply Hvm. rewrite Heq in Hv. move: Hv. move=>/andP [] Hv1 Hv2.
    apply Hv1.
  (* stack *)
  assert (Hs := free_stackP). move: (Hs m1)=> Hm1. move: (Hs m1')=> Hm1'.
  have Heq := (fss_valid Hm1).
  move=> p1 Hs'. apply Hsm. have <- := fss_root Hm1. by have <- := fss_limit Hm1.
  Qed.

  Lemma mm_read_ok : ∀ m m' a s v,
  match_mem m m' →
  read m a s = ok v →
  read m' a s = ok v.
  Proof.
  move=> m m' p'' s v [] Hrm Hvm Hsm Hr.
  have := read_read8 Hr. move=> [] Ha Hi.
  have : validw m' p'' s. apply /validwP.
  split=>//. move=> i Hi'. apply Hvm. move: (Hi i Hi')=> Hr'.
  by have Hv := readV Hr'. move=> Hv. rewrite -Hr.
  apply eq_read. move=> i Hi'. move: (Hi i Hi')=> Hr'.
  move: (Hrm (add p'' i) (LE.wread8 v i) Hr'). move=> Hr''.
  by rewrite Hr' Hr''.
  Qed.

  Lemma mm_write : ∀ m1 m1' p s (w:word s) m2,
  match_mem m1 m1' →
  write m1 p w = ok m2 →
  exists2 m2', write m1' p w = ok m2' & match_mem m2 m2'.
  Proof.
  move=> m1 m1' p'' sz w m2 Hm Hw.
  case: Hm=> H1 H2 H3. have /validwP := (write_validw Hw).
  move=> [] Ha Hi.
  have /writeV : validw m1' p'' sz. apply /validwP. split=> //. move=> i Hi'.
  move: (Hi i Hi')=> Hv. by move: (H2 (add p'' i) Hv). move=> Hw'.
  move: (Hw' w). move=> [] m2' Hw''. exists m2'.
  + by apply Hw''.
  constructor.
  (* read *)
  + move=> p1 w1 Hr2. have hr1:= write_read8 Hw p1.
    have hr2 := write_read8 Hw'' p1. move: Hr2. rewrite hr2 hr1 /=.
    case: ifP=> // _. by apply H1.
  (* valid *)
  + move=> p1 Hv. have Hv1 := (CoreMem.write_validw_eq Hw).
    have Hv2 := (CoreMem.write_validw_eq Hw''). rewrite Hv2.
    apply H2. by rewrite -Hv1.
  (* stack *)
  move=> p1 H. have Hv1 := (CoreMem.write_validw_eq Hw).
  have Hv2 := (CoreMem.write_validw_eq Hw''). rewrite Hv2.
  apply H3. have Hst := write_mem_stable Hw. case: Hst.
  by move=> -> -> _.
  Qed.

  Lemma mm_alloc m1 m1' al sz ioff es' m2 :
    match_mem m1 m1' →
    alloc_stack m1 al sz ioff es' = ok m2 →
    match_mem m2 m1'.
  Proof.
    case => Hvm Hrm Hs /alloc_stackP ass.
    have ? := ass_add_ioff ass; case: ass => Hvr Hve Hveq Ha Hs' hioff Hs'' Hsr Hsl Hf.
    constructor.
    (* read *)
    + move=> p1 w1 /dup[] Hr1.
      move: (Hve p1) (Hvr p1).
      have -> := readV Hr1.
      case: validw.
      * by move => _ <- // /Hvm.
      by move => ->.
    (* valid *)
    + move => p1; rewrite Hveq => /orP[]; first exact: Hrm.
      move => range; apply: Hs; move: range; rewrite !zify => - [] lo.
      change (wsize_size U8) with 1%Z.
      generalize (top_stack_below_root _ m1); rewrite -/(top_stack m1).
      lia.
    (* stack *)
    move=> p1 Hs'''. apply Hs. by rewrite -Hsr -Hsl.
  Qed.

  Lemma mm_write_invalid m m1' a s (w: word s) :
    match_mem m m1' →
    (wunsigned (stack_limit m) <= wunsigned a ∧ wunsigned a + wsize_size s <= wunsigned (top_stack m))%Z →
    is_align a s →
    exists2 m2', write m1' a w = ok m2' & match_mem m m2'.
  Proof.
    case => Hrm Hvm Hs Hs' al.
    have /writeV : validw m1' a s.
    - apply/validwP; split; first exact: al.
      move => k [] klo khi; apply: Hs.
      have a_range := wunsigned_range a.
      assert (r_range := wunsigned_range (stack_root m)).
      generalize (top_stack_below_root _ m); rewrite -/(top_stack m) => R.
      rewrite wunsigned_add; lia.
    move => /(_ w) [] m' ok_m'; exists m'; first exact: ok_m'.
    split.
    - move => x y ok_y.
      rewrite (CoreMem.writeP_neq ok_m'); first exact: Hrm.
      move => i j [] i_low i_hi; change (wsize_size U8) with 1%Z => j_range.
      have ? : j = 0%Z by lia.
      subst j => { j_range }.
      rewrite add_0 => ?; subst x.
      apply/negP: (readV ok_y).
      apply: stack_region_is_free.
      rewrite -/(top_stack m) wunsigned_add; first lia.
      have := wunsigned_range a.
      generalize (wunsigned_range (top_stack m)).
      lia.
    1-2: move => b; rewrite (CoreMem.write_validw_eq ok_m').
    - exact/Hvm.
    exact/Hs.
  Qed.

  Section MATCH_MEM_SEM_PEXPR.
    Context (scs: syscall_state_t) (m m': mem) (vm: vmap) (M: match_mem m m').
    Let P (e: pexpr) : Prop :=
      ∀ v,
        sem_pexpr [::] {| escs := scs; emem := m ; evm := vm |} e = ok v →
        sem_pexpr [::] {| escs := scs; emem := m' ; evm := vm |} e = ok v.

    Let Q (es: pexprs) : Prop :=
      ∀ vs,
        sem_pexprs [::] {| escs := scs; emem := m ; evm := vm |} es = ok vs →
        sem_pexprs [::] {| escs := scs; emem := m' ; evm := vm |} es = ok vs.

    Lemma match_mem_sem_pexpr_pair : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; split.
      - by [].
      - by move => e ihe es ihes vs /=; t_xrbindP => ? /ihe -> /= ? /ihes -> /= ->.
      1-4: by rewrite /P /=.
      - move => aa sz x e ihe vs /=.
        by apply: on_arr_gvarP => ??? -> /=; t_xrbindP => ?? /ihe -> /= -> /= ? -> /= ->.
      - move => aa sz len x e ihe v /=.
        by apply: on_arr_gvarP => ??? -> /=; t_xrbindP => ?? /ihe -> /= -> /= ? -> /= ->.
      - by move => sz x e ihe v /=; t_xrbindP => ?? -> /= -> /= ?? /ihe -> /= -> /= ? /(mm_read_ok M) -> /= ->.
      - by move => op e ihe v /=; t_xrbindP => ? /ihe ->.
      - by move => op e1 ih1 e2 ih2 v /=; t_xrbindP => ? /ih1 -> ? /ih2 ->.
      - by move => op es ih vs /=; t_xrbindP => ? /ih; rewrite -/(sem_pexprs [::] _ es) => ->.
      by move => ty e ihe e1 ih1 e2 ih2 v /=; t_xrbindP => ?? /ihe -> /= -> ?? /ih1 -> /= -> ?? /ih2 -> /= -> /= ->.
    Qed.

  Lemma match_mem_sem_pexpr e : P e.
  Proof. exact: (proj1 match_mem_sem_pexpr_pair). Qed.

  Lemma match_mem_sem_pexprs es : Q es.
  Proof. exact: (proj2 match_mem_sem_pexpr_pair). Qed.

  End MATCH_MEM_SEM_PEXPR.

  Lemma match_mem_write_lval scs1 m1 vm1 m1' scs2 m2 vm2 x v :
    match_mem m1 m1' →
    write_lval [::] x v {| escs := scs1; emem := m1 ; evm := vm1 |} = ok {| escs := scs2; emem := m2 ; evm := vm2 |} →
    exists2 m2',
    write_lval [::] x v {| escs := scs1; emem := m1' ; evm := vm1 |} = ok {| escs := scs2; emem := m2' ; evm := vm2 |} &
    match_mem m2 m2'.
  Proof.
    move => M; case: x => /= [ _ ty | x | ws x e | aa ws x e | aa ws n x e ].
    - case/write_noneP => - [] -> -> -> h; exists m1'; last exact: M.
      rewrite /write_none.
      by case: h => [ [u ->] | [ -> -> ] ].
    - rewrite /write_var /=; t_xrbindP =>_ -> -> <- -> /=.
      by exists m1'.
    - t_xrbindP => ?? -> /= -> /= ?? /(match_mem_sem_pexpr M) -> /= -> /= ? -> /= ? /(mm_write M)[] ? -> /= M' <- <- <-.
      eexists; first reflexivity; exact: M'.
    all: apply: on_arr_varP; rewrite /write_var; t_xrbindP => ??? -> /= ?? /(match_mem_sem_pexpr M) -> /= -> /= ? -> /= ? -> /= ? -> /= <- <- <-.
    all: by exists m1'.
  Qed.

  Lemma match_mem_write_lvals scs1 m1 vm1 m1' scs2 m2 vm2 xs vs :
    match_mem m1 m1' →
    write_lvals [::] {| escs := scs1; emem := m1 ; evm := vm1 |} xs vs = ok {| escs := scs2; emem := m2 ; evm := vm2 |} →
    exists2 m2',
    write_lvals [::] {| escs := scs1; emem := m1' ; evm := vm1 |} xs vs = ok {| escs := scs2; emem := m2' ; evm := vm2 |} &
    match_mem m2 m2'.
  Proof.
    elim: xs vs scs1 vm1 m1 m1'.
    - by case => // scs1 vm1 m1 m1' M [] <- <- <-; exists m1'.
    by move => x xs ih [] // v vs scs1 vm1 m1 m1' M /=; t_xrbindP => - [] ??? /(match_mem_write_lval M)[] m2' -> M2 /ih - /(_ _ M2).
  Qed.

  Definition is_ra_of (fn: funname) (ra: return_address_location) : Prop :=
    exists2 fd, get_fundef (p_funcs p) fn = Some fd & fd.(f_extra).(sf_return_address) = ra.

  (** Export functions allocate their own stack frames
  * whereas internal functions have their frame allocated by the caller *)
  Definition is_sp_for_call (fn: funname) (m: mem) (ptr: pointer) : Prop :=
    exists2 fd,
    get_fundef (p_funcs p) fn = Some fd &
    let e := fd.(f_extra) in
    if e.(sf_return_address) is RAnone
    then ptr = top_stack m
    else
      is_align (top_stack m) e.(sf_align) ∧
      let sz := stack_frame_allocation_size e in ptr = (top_stack m - wrepr Uptr sz)%R.

  (* Define where/how the return address is pass by the caller to the callee *)
  Definition value_of_ra
    (m: mem)
    (vm: vmap)
    (ra: return_address_location)
    (target: option (remote_label * lcmd * nat))
    : Prop :=
    match ra, target with
    | RAnone, None => True
    | RAreg (Var (sword ws) _ as ra), Some ((caller, lbl), cbody, pc) =>
      if (ws == Uptr)%CMP
      then [/\ is_linear_of caller cbody,
            find_label lbl cbody = ok pc,
            (caller, lbl) \in label_in_lprog p' &
            exists2 ptr,
              encode_label (label_in_lprog p') (caller, lbl) = Some ptr &
              vm.[ra] = ok (pword_of_word (zero_extend ws ptr))
           ]
      else False

   | RAstack (Some (Var (sword ws) _ as ra)) _, Some ((caller, lbl), cbody, pc) =>
      if (ws == Uptr)%CMP
      then [/\ is_linear_of caller cbody,
            find_label lbl cbody = ok pc, 
            (caller, lbl) \in label_in_lprog p' &
            exists2 ptr,
              encode_label (label_in_lprog p') (caller, lbl) = Some ptr &
              vm.[ra] = ok (pword_of_word (zero_extend ws ptr))
           ]
      else False

    | RAstack None ofs, Some ((caller, lbl), cbody, pc) =>
      [/\ is_linear_of caller cbody,
          find_label lbl cbody = ok pc,
          (caller, lbl) \in label_in_lprog p' &
          exists2 ptr, encode_label (label_in_lprog p') (caller, lbl) = Some ptr &
          exists2 sp, vm.[ vrsp ] = ok (pword_of_word sp) & read m (sp + wrepr Uptr ofs)%R Uptr = ok ptr
      ]

 
    | _, _ => False
    end%vmap.

  (* Export functions save and restore the contents of “to-save” registers. *)
  Definition is_callee_saved_of (fn: funname) (s: seq var) : Prop :=
    exists2 fd,
    get_fundef (p_funcs p) fn = Some fd &
    let e := f_extra fd in
    if sf_return_address e is RAnone then
      s = map fst (sf_to_save e)
    else s = [::].

  (* Execution of linear programs preserve meta-data stored in the stack memory *)
  Definition preserved_metadata (m m1 m2: mem) : Prop :=
    ∀ p : pointer,
      (wunsigned (top_stack m) <= wunsigned p < wunsigned (stack_root m))%Z →
      ~~ validw m p U8 →
      read m1 p U8 = read m2 p U8.

  Instance preserved_metadata_equiv m : Equivalence (preserved_metadata m).
  Proof.
    split; first by [].
    - by move => x y xy ptr r nv; rewrite xy.
    move => x y z xy yz ptr r nv.
    by rewrite xy; first exact: yz.
  Qed.

  Lemma preserved_metadataE (m m' m1 m2: mem) :
    stack_stable m m' →
    validw m =2 validw m' →
    preserved_metadata m' m1 m2 →
    preserved_metadata m m1 m2.
  Proof.
    move => ss e h ptr r nv.
    apply: h.
    - by rewrite -(ss_top_stack ss) -(ss_root ss).
    by rewrite -e.
  Qed.

  Lemma write_lval_preserves_metadata x v v' s s' t t' :
    write_lval [::] x v s = ok s' →
    write_lval [::] x v' t = ok t' →
    escs s = escs t →
    vm_uincl s t →
    match_mem s t →
    preserved_metadata (emem s) (emem t) (emem t').
  Proof.
    case: x.
    - move => /= _ ty /write_noneP[] <- _ /write_noneP[] -> _; reflexivity.
    - move => x /write_var_emem -> /write_var_emem ->; reflexivity.
    - case: s t => scs m vm [] tscs tv tvm /=.
      move => sz x e ok_s' ok_t' E X M; subst tscs.
      move: ok_s' => /=; t_xrbindP => a xv ok_xv ok_a ofs ev ok_ev ok_ofs w ok_w m' ok_m' _{s'}.
      move: ok_t' => /=.
      have [ xv' -> /= /of_value_uincl_te h ] := get_var_uincl X ok_xv.
      have {h} /= -> /= := (h (sword _) _ ok_a).
      have /= ok_ev' := match_mem_sem_pexpr M ok_ev.
      have /(_ _ X) := sem_pexpr_uincl _ ok_ev'.
      case => ev' -> /of_value_uincl_te h /=.
      have {h} /= -> /= := (h (sword _) _ ok_ofs).
      t_xrbindP => w' ok_w' tm' ok_tm' <-{t'} /=.
      move => ptr ptr_range /negP ptr_not_valid.
      rewrite (CoreMem.writeP_neq ok_tm'); first reflexivity.
      apply: disjoint_range_U8 => i i_range ?; subst ptr.
      apply: ptr_not_valid.
      rewrite -valid8_validw.
      have /andP[ _ /allP ] := write_validw ok_m'.
      apply.
      rewrite in_ziota !zify; Lia.lia.
    - move => aa sz x e; apply: on_arr_varP; rewrite /write_var; t_xrbindP => ???????????????.
      apply: on_arr_varP; rewrite /write_var; t_xrbindP => ???????????????.
      subst; reflexivity.
    move => aa sz k x e; apply: on_arr_varP; rewrite /write_var; t_xrbindP => ???????????????.
    apply: on_arr_varP; rewrite /write_var; t_xrbindP => ???????????????.
    subst; reflexivity.
  Qed.

  Lemma write_lvals_preserves_metadata xs vs vs' s s' t t' :
    List.Forall2 value_uincl vs vs' →
    write_lvals [::] s xs vs = ok s' →
    write_lvals [::] t xs vs' = ok t' →
    escs s = escs t →
    vm_uincl s t →
    match_mem s t →
    preserved_metadata (emem s) (emem t) (emem t').
  Proof.
    move => h; elim: h xs s t => {vs vs'}.
    - case => // ?? [] -> [] -> _ _; reflexivity.
    move => v v' vs vs' v_v' vs_vs' ih [] // x xs s t /=.
    apply: rbindP => s1 ok_s1 ok_s' ok_t' E X M.
    have [ vm ok_vm X' ] := write_uincl X v_v' ok_s1.
    have [ m' ok_t1 M' ] := match_mem_write_lval M ok_vm.
    move: ok_t'.
    rewrite (surj_estate t) -E ok_t1 /= => ok_t'.
    etransitivity.
    - exact: write_lval_preserves_metadata ok_s1 ok_t1 erefl X M.
    apply: preserved_metadataE;
      last apply: (ih _ _ _ ok_s' ok_t' erefl).
    - exact: write_lval_stack_stable ok_s1.
    - exact: write_lval_validw ok_s1.
    - exact: X'.
    exact: M'.
  Qed.

  Lemma preserved_metadata_alloc m al sz ioff sz' m' m1 m2 :
    (0 <= sz)%Z →
    alloc_stack m al sz ioff sz' = ok m' →
    preserved_metadata m' m1 m2 →
    preserved_metadata m m1 m2.
  Proof.
    move => sz_pos ok_m' h a [] a_lo a_hi /negbTE a_not_valid.
    have A := alloc_stackP ok_m'.
    have ? := ass_add_ioff A.
    have [_ top_goes_down ] := ass_above_limit A.
    apply: h.
    - split; last by rewrite A.(ass_root).
      apply: Z.le_trans a_lo.
      etransitivity; last apply: top_goes_down.
      lia.
    rewrite A.(ass_valid) a_not_valid /= !zify.
    change (wsize_size U8) with 1%Z.
    lia.
  Qed.

  (* ---------------------------------------------------- *)
  Variant ex2_6 (T1 T2: Type) (A B C D E F : T1 → T2 → Prop) : Prop :=
    Ex2_6 x1 x2 of A x1 x2 & B x1 x2 & C x1 x2 & D x1 x2 & E x1 x2 & F x1 x2.

  Let Pi (k: Sv.t) (s1: estate) (i: instr) (s2: estate) : Prop :=
    ∀ fn lbl,
      checked_i fn i →
      let: (lbli, li) := linear_i fn i lbl [::] in
     ∀ m1 vm1 P Q,
       wf_vm vm1 →
       match_mem s1 m1 →
       vm_uincl s1 vm1 →
       disjoint_labels lbl lbli P →
       is_linear_of fn (P ++ li ++ Q) →
       ex2_6
       (λ m2 vm2, lsem
                    p'
                    (Lstate (escs s1) m1 vm1 fn (size P))
                    (Lstate (escs s2) m2 vm2 fn (size (P ++ li)))
       )
       (λ _ vm2, vm1 = vm2 [\ k ])
       (λ _ vm2, wf_vm vm2)
       (λ _ vm2, vm_uincl s2 vm2)
       (λ m2 _, preserved_metadata s1 m1 m2)
       (λ m2 _, match_mem s2 m2).

  Let Pi_r (ii: instr_info) (k: Sv.t) (s1: estate) (i: instr_r) (s2: estate) : Prop :=
    ∀ fn lbl,
      checked_i fn (MkI ii i) →
      let: (lbli, li) := linear_i fn (MkI ii i) lbl [::] in
      (if extra_free_registers ii is Some fr then
           [/\ fr <> vgd, fr <> vrsp, vtype fr = sword Uptr & s1.[fr]%vmap = Error ErrAddrUndef]
       else True) →
     ∀ m1 vm1 P Q,
       wf_vm vm1 →
       match_mem s1 m1 →
       vm_uincl s1 vm1 →
       disjoint_labels lbl lbli P →
       is_linear_of fn (P ++ li ++ Q) →
       ex2_6
       (λ m2 vm2, lsem
                    p'
                    (Lstate (escs s1) m1 vm1 fn (size P))
                    (Lstate (escs s2) m2 vm2 fn (size (P ++ li)))
       )
       (λ _ vm2, vm1 = vm2 [\  Sv.union k (extra_free_registers_at extra_free_registers ii) ])
       (λ _ vm2, wf_vm vm2)
       (λ _ vm2, vm_uincl s2 vm2)
       (λ m2 _, preserved_metadata s1 m1 m2)
       (λ m2 _, match_mem s2 m2).

  Let Pc (k: Sv.t) (s1: estate) (c: cmd) (s2: estate) : Prop :=
    ∀ fn lbl,
      checked_c fn c →
      let: (lblc, lc) := linear_c fn c lbl [::] in
     ∀ m1 vm1 P Q,
       wf_vm vm1 →
       match_mem s1 m1 →
       vm_uincl s1 vm1 →
       disjoint_labels lbl lblc P →
       is_linear_of fn (P ++ lc ++ Q) →
       ex2_6
       (λ m2 vm2, lsem
                    p'
                    (Lstate (escs s1) m1 vm1 fn (size P))
                    (Lstate (escs s2) m2 vm2 fn (size (P ++ lc)))
       )
       (λ _ vm2, vm1 = vm2 [\ k ])
       (λ _ vm2, wf_vm vm2)
       (λ _ vm2, vm_uincl s2 vm2)
       (λ m2 _, preserved_metadata s1 m1 m2)
       (λ m2 _, match_mem s2 m2).

  Let Pfun (ii: instr_info) (k: Sv.t) (s1: estate) (fn: funname) (s2: estate) : Prop :=
    ∀ m1 vm1 body ra lret sp callee_saved,
       wf_vm vm1 →
      match_mem s1 m1 →
      vm_uincl
        (kill_vars match ra with
        | RAnone => Sv.singleton var_tmp
        | RAreg x => Sv.singleton x
        | RAstack (Some x) _ => Sv.singleton x
        | RAstack None _ => Sv.empty
        end s1).[vrsp <- ok (pword_of_word sp)]%vmap vm1 →
      is_linear_of fn body →
      (* RA contains a safe return address “lret” *)
      is_ra_of fn ra →
      value_of_ra m1 vm1 ra lret →
      (* RSP points to the top of the stack according to the calling convention *)
      is_sp_for_call fn s1 sp →
      (* To-save variables are initialized in the initial linear state *)
      is_callee_saved_of fn callee_saved →
      vm_initialized_on vm1 callee_saved →
      ex2_6
      (λ m2 vm2,
      if lret is Some ((caller, lbl), _cbody, pc)
      then lsem p' (Lstate (escs s1) m1 vm1 fn 1) (Lstate (escs s2) m2 vm2 caller pc.+1)
      else lsem p' (Lstate (escs s1) m1 vm1 fn 0) (Lstate (escs s2) m2 vm2 fn (size body)))
      (λ _ vm2, vm1 = vm2 [\ match ra with
                             | RAnone => Sv.diff k (sv_of_list id callee_saved)
                             | RAreg _ => Sv.union k (extra_free_registers_at extra_free_registers ii)
                             | RAstack _ _ => Sv.add vrsp (Sv.union k (extra_free_registers_at extra_free_registers ii))
                             end ])
      (λ _ vm2, wf_vm vm2)
      (λ _ vm2, s2.[vrsp <- ok (pword_of_word (if ra is RAstack _ _ then sp + wrepr _ (wsize_size Uptr)
                                               else sp))] <=[\ sv_of_list id callee_saved ] vm2)
      (λ m2 _, preserved_metadata s1 m1 m2)
      (λ m2 _, match_mem s2 m2).

  Lemma label_in_lfundef fn body (lbl: label) :
    lbl \in label_in_lcmd body →
    is_linear_of fn body →
    (fn, lbl) \in label_in_lprog p'.
  Proof.
    clear.
    rewrite /label_in_lprog => X [] fd ok_fd ?; subst body.
    apply/flattenP => /=.
    exists [seq (fn, lbl) | lbl <- label_in_lcmd (lfd_body fd) ];
      last by apply/map_f: X.
    apply/in_map.
    by exists (fn, fd); first exact: get_fundef_in'.
  Qed.

  Local Lemma Hnil : sem_Ind_nil Pc.
  Proof.
    move => s1 fn lbl _ m1 vm1 P Q M X D C; rewrite cats0; exists m1 vm1 => //; exact: rt_refl.
  Qed.

  Local Lemma Hcons : sem_Ind_cons p extra_free_registers var_tmp Pc Pi.
  Proof.
    move => ki kc s1 s2 s3 i c exec_i hi _ hc.
    move => fn lbl /checked_cI[] chk_i chk_c /=.
    case: (linear_c fn) (valid_c fn c lbl) (hc fn lbl chk_c) => lblc lc [Lc Vc] Sc.
    rewrite linear_i_nil.
    case: linear_i (valid_i fn i lblc) (hi fn lblc chk_i) => lbli li [Li Vi] Si.
    move => m1 vm1 P Q Wc Mc Xc Dc C.
    have D : disjoint_labels lblc lbli P.
    + apply: (disjoint_labels_wL _ Dc); exact: Lc.
    have C' : is_linear_of fn (P ++ li ++ lc ++ Q).
    + by move: C; rewrite !catA.
    have [ m2 vm2 Ei Ki Wi Xi Hi Mi ] := Si m1 vm1 P (lc ++ Q) Wc Mc Xc D C'.
    have Di : disjoint_labels lbl lblc (P ++ li).
    + apply: disjoint_labels_cat.
      * apply: (disjoint_labels_wH _ Dc); exact: Li.
      apply: (valid_disjoint_labels Vi); lia.
    have Ci : is_linear_of fn ((P ++ li) ++ lc ++ Q).
    + by move: C; rewrite !catA.
    have [ m3 vm3 ] := Sc m2 vm2 (P ++ li) Q Wi Mi Xi Di Ci.
    rewrite -!catA => E K W X H M.
    exists m3 vm3; [ | | exact: W | exact: X | | exact: M ]; cycle 2.
    + etransitivity; first exact: Hi.
      apply: preserved_metadataE H.
      + exact: sem_I_stack_stable exec_i.
      exact: sem_I_validw_stable exec_i.
    + exact: lsem_trans Ei E.
    apply: vmap_eq_exceptT; apply: vmap_eq_exceptI.
    2: exact: Ki.
    3: exact: K.
    all: SvD.fsetdec.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p extra_free_registers var_tmp Pi Pi_r.
  Proof.
    move => ii k i s1 s2 ok_fr _ h _ fn lbl chk.
    move: h => /(_ fn lbl chk); case: linear_i (valid_i fn (MkI ii i) lbl) => lbli li [L V] S.
    move => m1 vm1 P Q W M X D C.
    have E :
      match extra_free_registers ii return Prop with
      | Some fr =>
          [/\ fr ≠ vgd, fr ≠ vrsp, vtype fr = spointer
            & ((kill_extra_register extra_free_registers ii s1).[fr])%vmap = Error ErrAddrUndef]
      | None => True
      end.
    + rewrite /kill_extra_register /kill_extra_register_vmap.
      rewrite /efr_valid in ok_fr.
      case: extra_free_registers ok_fr
      => // fr /and3P [] /eqP hrip /eqP hrsp /andP[] /eqP hty not_while;
        split => //=.
      rewrite /=; case heq: s1.[fr]%vmap (W fr) (X fr) => [vfr | efr /=].
      + by move=> _ _; rewrite Fv.setP_eq hty.
      rewrite heq; case: vm1.[fr]%vmap.
      + by move=> _ _; case efr.
      by move=> [] // _; case: (efr).
    have {S E} S := S E.
    have [ | {W M X} ] := S _ vm1 _ _ W M _ D C.
    - by apply: vm_uincl_trans; first exact: kill_extra_register_vm_uincl.
    move => m2 vm2 E K W X H M.
    exists m2 vm2.
    - exact: E.
    - apply: vmap_eq_exceptI K; SvD.fsetdec.
    - exact: W.
    - exact: X.
    - exact: preserved_metadataE H.
    exact: M.
  Qed.

  Lemma find_instrE fn body :
    is_linear_of fn body →
    ∀ scs m vm n,
    find_instr p' (Lstate scs m vm fn n) = oseq.onth body n.
  Proof. by rewrite /find_instr => - [] fd /= -> ->. Qed.

  Lemma find_instr_skip fn P Q :
    is_linear_of fn (P ++ Q) →
    ∀ scs m vm n,
    find_instr p' (Lstate scs m vm fn (size P + n)) = oseq.onth Q n.
  Proof.
    move => h scs m vm n; rewrite (find_instrE h).
    rewrite !oseq.onth_nth map_cat nth_cat size_map.
    rewrite ltnNge leq_addr /=;f_equal;rewrite -minusE -plusE; lia.
  Qed.

  Local Lemma Hasgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => ii s1 s2 x tg ty e v v'; rewrite p_globs_nil => ok_v ok_v' ok_s2.
    move => fn lbl /checked_iE[] fd ok_fd.
    case: ty ok_v' ok_s2 => // sz.
    move=> /truncate_val_typeE [w0 [sz' [w' [htw ??]]]]; subst v v' => ok_s2 chk.

    move: chk.
    rewrite /check_i.
    case: ifP => // hchk _.

    move => fr_undef m1 vm1 P Q W1 M1 X1 D1 C1.
    have [ v' ok_v' ] := sem_pexpr_uincl X1 ok_v.
    case/value_uinclE => [sz''] [w] [?]; subst v' => /andP[] hle' /eqP ?; subst w'.
    have [ vm2 /(match_mem_write_lval M1) [ m2 ok_s2' M2 ] ok_vm2 ] := write_uincl X1 (value_uincl_refl _) ok_s2.
    exists m2 vm2; [ | | | exact: ok_vm2 | | exact: M2]; last first.
    + exact: write_lval_preserves_metadata ok_s2 ok_s2' _ X1 M1.
    + exact: wf_write_lval ok_s2'.
    + apply: vmap_eq_exceptI; first exact: SvP.MP.union_subset_1.
      by have := vrvP ok_s2'.
    apply: LSem_step.
    rewrite -(addn0 (size P)) /lsem1 /step /= (find_instr_skip C1) /=.
    rewrite /of_estate size_cat addn1 addn0.
    apply:
      (spec_lassign
         hliparams
         _ _ _ _
         hchk
         (match_mem_sem_pexpr M1 ok_v')
         _
         ok_s2').
    move: htw => /truncate_wordP [hle ->].
    by rewrite (zero_extend_idem _ hle) /truncate_word (ifT _ _ (cmp_le_trans hle hle')).
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => ii s1 s2 tg op xs es; rewrite /sem_sopn; t_xrbindP => rs vs.
    rewrite p_globs_nil => ok_vs ok_rs ok_s2.
    move => fn lbl /checked_iE[] fd ok_fd chk.
    move => fr_undef m1 vm1 P Q W1 M1 X1 D1 C1.
    have [ vs' /(match_mem_sem_pexprs M1) ok_vs' vs_vs' ] := sem_pexprs_uincl X1 ok_vs.
    have [ rs' ok_rs' rs_rs' ] := vuincl_exec_opn vs_vs' ok_rs.
    have [ vm2 /(match_mem_write_lvals M1) [ m2 ok_s2' M2 ] ok_vm2 ] := writes_uincl X1 rs_rs' ok_s2.
    exists m2 vm2; [ | | | exact: ok_vm2 | | exact: M2 ]; last first.
    + exact: write_lvals_preserves_metadata ok_s2 ok_s2' _ X1 M1.
    + exact: wf_write_lvals ok_s2'.
    + apply: vmap_eq_exceptI; first exact: SvP.MP.union_subset_1.
      by have := vrvsP ok_s2'.
    apply: LSem_step.
    rewrite -(addn0 (size P)) /lsem1 /step /= (find_instr_skip C1) /= /eval_instr /to_estate /=.
    by rewrite /sem_sopn ok_vs' /= ok_rs' /= ok_s2' /= size_cat addn0 addn1.
  Qed.

  (* FIXME syscall: move this, rename get_vars_uincl -> get_vars_i_uincl
                                      get_vars_uincl_ -> get_vars_uincl
     introduce get_vars and get_vars_i
  *)

  Lemma get_vars_uincl_ (xs : seq var) (vm1 vm2 : vmap) (vs1 : seq value) :
    vm_uincl vm1 vm2 →
    mapM (get_var vm1) xs = ok vs1 →
    exists2 vs2 : seq value,
      mapM (get_var vm2) xs = ok vs2 & List.Forall2 value_uincl vs1 vs2.
  Proof.
    move=> h1 h2;
    have := get_vars_uincl (xs := map (fun x => {| v_var := x; v_info := dummy_var_info |}) xs) h1.
    by rewrite !mapM_map => /(_ _ h2).
  Qed.

  Lemma vm_after_syscall_uincl vm1 vm2 :
    vm_uincl vm1 vm2 ->
    vm_uincl (vm_after_syscall vm1) (vm_after_syscall vm2).
  Proof.
    by move=> h x; rewrite /vm_after_syscall !kill_varsE; case: ifP.
  Qed.

  Lemma match_mem_fill_mem m1 m1' m2 ptr bytes:
    match_mem m1 m1' → fill_mem m1 ptr bytes = ok m2 →
    exists2 m2', fill_mem m1' ptr bytes = ok m2' & match_mem m2 m2'.
  Proof.
    rewrite /fill_mem; t_xrbindP => mm [z m2'] /= hf ?; subst m2' => /=.
    elim: bytes 0%Z m1 m1' mm hf => [ | b bytes ih] z1 m1 m1' mm /=.
    + by move=> [_ <-]; exists m1'.
    by t_xrbindP => _ m3  /(mm_write mm) [m3' -> mm3 /=] <- /ih -/(_ _ mm3).
  Qed.

  Lemma match_mem_exec_syscall o scs1 m1 m1' scs2 m2 ves vs:
    match_mem m1 m1' → exec_syscall_s scs1 m1 o ves = ok (scs2, m2, vs) →
    exists2 m2', exec_syscall_s scs1 m1' o ves = ok (scs2, m2', vs) & match_mem m2 m2'.
  Proof.
    move=> mm; rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [<- <- <-].
    have h: mk_forall_ex (fun e1 e2 => [/\ e1.1.1 = e2.1.1, e1.2 = e2.2 &  match_mem e1.1.2 e2.1.2])
                             (sem_syscall o scs1 m1) (sem_syscall o scs1 m1').
    + case: (o) => _ /= wp len [[scs_ rm] t_].
      rewrite /exec_getrandom_s_core; t_xrbindP => ? /(match_mem_fill_mem mm) [] rm' -> ? -> <- <- /=; by eexists.
    have [[[ _ rm' ] _ ] -> /= [] <- <-]:= mk_forall_exP h happ; by eexists.
  Qed.

  Lemma syscall_killP vm : vm = vm_after_syscall vm [\syscall_kill].
  Proof. by move=> x /Sv_memP /negPf; rewrite /vm_after_syscall kill_varsE => ->. Qed.

  Lemma preserved_metadata_fill_mem m0 m1 m2 m m' ptr bytes :
    fill_mem m0 ptr bytes = ok m ->
    fill_mem m1 ptr bytes = ok m' ->
    preserved_metadata m m' m2 → preserved_metadata m0 m1 m2.
  Proof.
    rewrite /fill_mem; t_xrbindP => -[z m2'] /= hf ? -[z' m2''] /= hf' ?; subst m2' m2''.
    elim: bytes 0%Z m0 m1 hf hf' => [ | b bytes ih] z1 m0 m1 /=.
    + by move=> [_ <-] [_ <-].
    t_xrbindP=> _ m4 hw1 <- /ih{ih}ih _ m5 hw2 <- /ih{ih}ih /ih h ptr'.
    (* FIXME: this is a subcase of write_lval_preserves_metadata *)
    have eqv : validw m0 =2 validw m4 by move=> ??; rewrite (write_validw_eq hw1).
    have h1 := preserved_metadataE (write_mem_stable hw1) eqv h.
    move=> /(h1 ptr') h2 h3; rewrite -(h2 h3).
    rewrite (CoreMem.writeP_neq hw2) //.
    apply: disjoint_range_U8 => i i_range ?; subst ptr'.
    case /negP: h3; rewrite -valid8_validw.
    have /andP[ _ /allP ] := write_validw hw1.
    apply; rewrite in_ziota !zify; Lia.lia.
  Qed.

  Lemma preserved_metadata_syscall m0 m1 m2 m m' scs scs' o ves ves' vs vs' :
    List.Forall2 value_uincl ves ves' ->
    exec_syscall_s scs m0 o ves = ok (scs', m, vs) ->
    exec_syscall_s scs m1 o ves' = ok (scs', m', vs') ->
    preserved_metadata m m' m2 → preserved_metadata m0 m1 m2.
  Proof.
    move=> hall hex; have {}:= exec_syscallPs_eq hex hall.
    rewrite /exec_syscall_s; t_xrbindP => -[[scs0 m0'] t0] happ1 [???] -[[scs1 m1'] t1] happ2 [???].
    subst scs1 scs0 m0' m1' vs vs'.
    have h : mk_forall2 (fun o1 o2 => preserved_metadata o1.1.2 o2.1.2 m2 → preserved_metadata m0 m1 m2)
               (sem_syscall o scs m0) (sem_syscall o scs m1).
    + case: (o) => _ /= ptr bytes ??.
      rewrite /exec_getrandom_s_core; t_xrbindP => ? hf1 <- ? hf2 <- /=.
      by apply: preserved_metadata_fill_mem hf1 hf2.
    apply: mk_forall2P h happ1 happ2.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall p Pi_r.
  Proof.
    move=> ii s1 s2 o xs es scs m ves vs hes ho hw fn lbl /checked_iE [] fd ok_fd chk.
    move => fr_undef m1 vm1 P Q W1 M1 X1 D1 C1.
    have [ves' hes' uves]:= get_vars_uincl_ X1 hes.
    have [vs' /= ho' uvs]:= exec_syscallP ho uves.
    have [m' {ho'}ho' mm]:= match_mem_exec_syscall M1 ho'.
    have /(_ _ (vm_after_syscall_uincl X1)) := writes_uincl _ uvs hw.
    rewrite p_globs_nil => -[] vm2 /= /(match_mem_write_lvals mm) [ m2 /= ok_s2' M2 ] ok_vm2 .
    exists m2 vm2 => //.
    + apply: LSem_step.
      rewrite -(addn0 (size P)) /lsem1 /step /= (find_instr_skip C1) /= /eval_instr /to_estate /=.
      by rewrite hes' /= ho' /= ok_s2' /= size_cat addn0 addn1.
    + apply: (vmap_eq_exceptT (vm2 := vm_after_syscall vm1)).
      + by apply: vmap_eq_exceptI (syscall_killP vm1); SvD.fsetdec.
      by apply: vmap_eq_exceptI; last apply: vrvsP ok_s2'; SvD.fsetdec.
    + by apply: wf_write_lvals ok_s2'; apply wf_kill_vars.
    rewrite p_globs_nil in hw ok_s2'.
    have /= := write_lvals_preserves_metadata uvs hw ok_s2' erefl (vm_after_syscall_uincl X1) mm.
    by apply: preserved_metadata_syscall uves ho ho'.
  Qed.

  Remark next_lbl_neq (lbl: label) :
    ((lbl + 1)%positive == lbl) = false.
  Proof.
    apply/eqP => k.
    suff : (lbl < lbl)%positive by lia.
    rewrite -{2}k; lia.
  Qed.

  Lemma eval_jumpE fn body :
    is_linear_of fn body →
    ∀ lbl s,
    eval_jump p' (fn, lbl) s = Let pc := find_label lbl body in ok (setcpc s fn pc.+1).
  Proof. by case => ? /= -> ->. Qed.

  Let Llabel := linear.Llabel InternalLabel.

  Local Lemma Hif_true : sem_Ind_if_true p extra_free_registers var_tmp Pc Pi_r.
  Proof.
    move => ii k s1 s2 e c1 c2; rewrite p_globs_nil => ok_e E1 Hc1 fn lbl /checked_iE[] fd ok_fd /=; apply: rbindP => -[] chk_c1 _.
    case: c1 E1 Hc1 chk_c1 => [ | i1 c1 ] E1 Hc1 chk_c1; last case: c2 => [ | i2 c2 ].
    + case/semE: E1 => hk ?; subst s2.
      rewrite /= linear_c_nil; case: (linear_c fn) (valid_c fn c2 (next_lbl lbl)) => lbl2 lc2.
      rewrite /next_lbl => - [L V].
      move => fr_undef m1 vm1 P Q W1 M1 X1 D C1.
      have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      exists m1 vm1; [ | | exact: W1 | exact: X1 | by [] | exact: M1 ]; last by [].
      apply: LSem_step.
      rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C1) /= /eval_instr /to_estate /li_i (eval_jumpE C1) /to_estate /= ok_e' /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      * apply: (valid_has_not_label V); left; rewrite /next_lbl; lia.
      rewrite /= find_labelE /is_label /= eqxx /= /setcpc /= addn0.
      by rewrite size_cat /= size_cat /= -addn1 -addnA.
    + rewrite linear_c_nil.
      case: (linear_c fn) (Hc1 fn (next_lbl lbl)) => lbl1 lc1.
      rewrite /checked_c ok_fd chk_c1 => /(_ erefl) S.
      move => fr_undef m1 vm1 P Q W1 M1 X1 D C1.
      set P' := rcons P (MkLI ii (Lcond (snot e) lbl)).
      have D' : disjoint_labels (next_lbl lbl) lbl1 P'.
      - rewrite /P' -cats1; apply: disjoint_labels_cat; last by [].
        apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
      set Q' := MkLI ii (Llabel lbl) :: Q.
      have C' : is_linear_of fn (P' ++ lc1 ++ Q').
      - by move: C1; rewrite /P' /Q' -cats1 /= -!catA.
      have {S} [ m2 vm2 E K2 W2 X2 H2 M2 ] := S m1 vm1 P' Q' W1 M1 X1 D' C'.
      have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      have K2' := vmap_eq_exceptI (@SvP.MP.union_subset_1 _ _) K2.
      exists m2 vm2; [ | exact: K2' | exact: W2 | exact: X2 | exact: H2 | exact: M2 ].
      apply: lsem_step; last apply: lsem_trans.
      2: exact: E.
      - by rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C1) /= /eval_instr /li_i (eval_jumpE C1) /to_estate /= (snot_spec ok_e') /= ok_e' /= /setpc /= addn0 /P' /Q' size_rcons.
      apply: LSem_step.
      rewrite catA in C'.
      rewrite /lsem1 /step -(addn0 (size (P' ++ lc1))) (find_instr_skip C') /= /eval_instr /= /setpc /=.
      by rewrite /P' /Q' -cats1 -!catA !size_cat addn0 /= size_cat /= !addnS addn0.
    rewrite linear_c_nil.
    case: (linear_c fn) (valid_c fn (i1 :: c1) (next_lbl (next_lbl lbl))) (Hc1 fn (next_lbl (next_lbl lbl))) => lbl1 lc1.
    rewrite /next_lbl => -[L V].
    rewrite /checked_c ok_fd chk_c1 => /(_ erefl) E.
    rewrite linear_c_nil.
    case: (linear_c fn) (valid_c fn (i2 :: c2) lbl1) => lbl2 lc2 [L2 V2].
    move => fr_undef m1 vm1 P Q W1 M1 X1 D C.
    have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
    set P' := P ++ {| li_ii := ii; li_i := Lcond e lbl |} :: lc2 ++ [:: {| li_ii := ii; li_i := Lgoto (fn, (lbl + 1)%positive) |}; {| li_ii := ii; li_i := Llabel lbl |} ].
    have D' : disjoint_labels (lbl + 1 + 1) lbl1 P'.
    + apply: disjoint_labels_cat; first by apply: disjoint_labels_w _ _ D; lia.
      apply: disjoint_labels_cat; first by apply: (valid_disjoint_labels V2); lia.
      move => lbl' [A B]; rewrite /= orbF /is_label /=; apply/eqP => ?; subst lbl'; lia.
    set Q' := {| li_ii := ii; li_i := Llabel (lbl + 1) |} :: Q.
    have C' : is_linear_of fn (P' ++ lc1 ++ Q').
    + by move: C; rewrite /P' /Q' /= -!catA /= -!catA.
    have {E} [ m2 vm2 E K2 W2 X2 H2 M2 ] := E m1 vm1 P' Q' W1 M1 X1 D' C'.
      have K2' := vmap_eq_exceptI (@SvP.MP.union_subset_1 _ _) K2.
    exists m2 vm2; [ | exact: K2' | exact: W2 | exact: X2 | exact: H2 | exact: M2 ].
    apply: lsem_step; last apply: lsem_trans.
    2: exact: E.
    - rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /li_i  (eval_jumpE C) /to_estate /= ok_e' /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      * apply: (valid_has_not_label V2); lia.
      by rewrite /= find_labelE /= find_labelE /is_label /= eqxx /= /setcpc /= /P' /Q' size_cat /= size_cat /= !addnS.
    apply: LSem_step.
    rewrite catA in C'.
    rewrite /lsem1 /step -(addn0 (size (P' ++ lc1))) (find_instr_skip C') /= /eval_instr /= /setpc /=.
    by rewrite /P' /Q' -!catA /= -!catA; repeat rewrite !size_cat /=; rewrite !addnS !addn0.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p extra_free_registers var_tmp Pc Pi_r.
  Proof.
    move => ii k s1 s2 e c1 c2; rewrite p_globs_nil => ok_e E2 Hc2 fn lbl /checked_iE[] fd ok_fd /=; apply: rbindP => -[] _ chk_c2.
    case: c1 => [ | i1 c1 ]; last case: c2 E2 Hc2 chk_c2 => [ | i2 c2 ].
    + rewrite linear_c_nil.
      case: (linear_c fn) (Hc2 fn (next_lbl lbl)) => lbl2 lc2.
      rewrite /checked_c ok_fd chk_c2 => /(_ erefl) S.
      move => fr_undef m1 vm1 P Q W1 M1 X1 D C.
      set P' := rcons P (MkLI ii (Lcond e lbl)).
      have D' : disjoint_labels (next_lbl lbl) lbl2 P'.
      - rewrite /P' -cats1; apply: disjoint_labels_cat; last by [].
        apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
      set Q' := MkLI ii (Llabel lbl) :: Q.
      have C' : is_linear_of fn (P' ++ lc2 ++ Q').
      - by move: C; rewrite /P' /Q' -cats1 /= -!catA.
      have {S} [ m2 vm2 E K2 W2 X2 H2 M2 ] := S m1 vm1 P' Q' W1 M1 X1 D' C'.
      have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      have K2' := vmap_eq_exceptI (@SvP.MP.union_subset_1 _ _) K2.
      exists m2 vm2; [ | exact: K2' | exact: W2 | exact: X2 | exact: H2 | exact: M2 ].
      apply: lsem_step; last apply: lsem_trans.
      2: exact: E.
      - by rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /li_i (eval_jumpE C) /to_estate /= ok_e' /= /setpc /= addn0 /P' /Q' size_rcons.
      apply: LSem_step.
      rewrite catA in C'.
      rewrite /lsem1 /step -(addn0 (size (P' ++ lc2))) (find_instr_skip C') /= /eval_instr /= /setpc /=.
      by rewrite /P' /Q' -cats1 -!catA !size_cat addn0 /= size_cat /= !addnS addn0.
    + case/semE => hk ? _ _; subst s2.
      rewrite linear_c_nil; case: (linear_c fn) (valid_c fn (i1 :: c1) (next_lbl lbl)) => lbl1 lc1.
      rewrite /next_lbl => - [L V].
      move => fr_undef m1 vm1 P Q W1 M1 X1 D C.
      have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      exists m1 vm1; [ | | exact: W1 | exact: X1 | by [] | exact: M1 ]; last by [].
      apply: LSem_step.
      rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /li_i (eval_jumpE C) /to_estate /= (snot_spec ok_e') /= ok_e' /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= -catA find_label_cat_hd; last first.
      - apply: (valid_has_not_label V); left; rewrite /next_lbl; lia.
      rewrite /= find_labelE /is_label /= eqxx /= /setcpc /= addn0.
      by rewrite size_cat /= size_cat /= -addn1 -addnA.
    rewrite linear_c_nil => _ Hc2 chk_c2.
    case: (linear_c fn) (valid_c fn (i1 :: c1) (next_lbl (next_lbl lbl))) => lbl1 lc1.
    rewrite /next_lbl => -[L V].
    rewrite linear_c_nil.
    case: (linear_c fn) (valid_c fn (i2 :: c2) lbl1) (Hc2 fn lbl1) => lbl2 lc2 [L2 V2].
    rewrite /checked_c ok_fd chk_c2 => /(_ erefl) E.
    move => fr_undef m1 vm1 P Q W1 M1 X1 D C.
    have [ b /(match_mem_sem_pexpr M1) ok_e' /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
    set P' := rcons P {| li_ii := ii; li_i := Lcond e lbl |}.
    have D' : disjoint_labels lbl1 lbl2 P'.
    + rewrite /P' -cats1; apply: disjoint_labels_cat; last by [].
      apply: disjoint_labels_wL _ D; lia.
    set Q' := {| li_ii := ii; li_i := Lgoto (fn, (lbl + 1)%positive) |} :: {| li_ii := ii; li_i := Llabel lbl |} :: lc1 ++ [:: {| li_ii := ii; li_i := Llabel (lbl + 1) |}].
    have C' : is_linear_of fn (P' ++ lc2 ++ Q' ++ Q).
    + by move: C; rewrite /P' /Q' /= -cats1 /= -!catA /= -!catA.
    have {E} [ m2 vm2 E K2 W2 X2 H2 M2 ] := E m1 vm1 P' (Q' ++ Q) W1 M1 X1 D' C'.
    have K2' := vmap_eq_exceptI (@SvP.MP.union_subset_1 _ _) K2.
    exists m2 vm2; [ | exact: K2' | exact: W2 | exact: X2 | exact: H2 | exact: M2 ].
    apply: lsem_step; last apply: lsem_trans.
    2: exact: E.
    + rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= /eval_instr /li_i (eval_jumpE C) /to_estate /= ok_e' /= /setpc /=.
      by rewrite /P' /Q' /= size_rcons addn0.
    apply: LSem_step.
    rewrite catA in C'.
    rewrite /lsem1 /step -(addn0 (size (P' ++ lc2))) (find_instr_skip C') /= /eval_instr /li_i (eval_jumpE C') /= /setcpc /=.
    rewrite /P' -cats1.
    rewrite -!catA find_label_cat_hd; last by apply: D; lia.
    rewrite find_labelE /= find_label_cat_hd; last by apply: (valid_has_not_label V2); lia.
    rewrite find_labelE /= find_labelE /is_label /= next_lbl_neq find_label_cat_hd; last by apply: (valid_has_not_label V); lia.
    by rewrite find_labelE /is_label /= eqxx /= /setcpc /Q' !size_cat /= size_cat /= size_cat /= !addnS !addnA.
  Qed.

  (* Inversion lemmas about lsem: can skip align and label instructions *)
  Lemma lsem_skip_align scs m vm fn P scs' m' vm' n ii a Q :
    is_linear_of fn (P ++ add_align ii a [::] ++ Q) →
    lsem p' {| lscs := scs; lmem := m ; lvm := vm ; lfn := fn ; lpc := size P |} {| lscs := scs'; lmem := m' ; lvm := vm' ; lfn := fn ; lpc := size (P ++ add_align ii a [::]) + n |} →
    lsem p' {| lscs := scs; lmem := m ; lvm := vm ; lfn := fn ; lpc := size (P ++ add_align ii a [::]) |} {| lscs := scs'; lmem := m' ; lvm := vm' ; lfn := fn ; lpc := size (P ++ add_align ii a [::]) + n |}.
  Proof.
    case: a; last by rewrite cats0.
    move => C /lsem_split_start[].
    - rewrite size_cat => - [] _ _ _ K; exfalso; move: K; clear.
      rewrite /addn /addn_rec; lia.
    case => s h E; apply: lsem_trans E.
    move: C h; rewrite /lsem1 /step -{1}(addn0 (size _)) => /find_instr_skip ->.
    rewrite /eval_instr /= /setpc => /ok_inj <-{s} /=.
    rewrite size_cat /= addn1.
    exact: rt_refl.
  Qed.

  Lemma lsem_skip_label scs m vm fn P scs' m' vm' n ii lbl Q :
    is_linear_of fn (P ++ [:: {| li_ii := ii ; li_i := Llabel lbl |} ] ++ Q) →
    lsem p' {| lscs := scs; lmem := m ; lvm := vm ; lfn := fn ; lpc := size P |} {| lscs := scs'; lmem := m' ; lvm := vm' ; lfn := fn ; lpc := size P + n.+1 |} →
    lsem p' {| lscs := scs; lmem := m ; lvm := vm ; lfn := fn ; lpc := (size P).+1 |} {| lscs := scs'; lmem := m' ; lvm := vm' ; lfn := fn ; lpc := size P + n.+1 |}.
  Proof.
    move => C /lsem_split_start[].
    - case => _ _ _ K; exfalso; move: K; clear.
      rewrite /addn /addn_rec; lia.
    case => s h E; apply: lsem_trans E.
    move: C h; rewrite /lsem1 /step -{1}(addn0 (size _)) => /find_instr_skip ->.
    rewrite /eval_instr /= /setpc => /ok_inj <-{s} /=.
    exact: rt_refl.
  Qed.

   Lemma lsem_skip_goto scs m vm fn P scs' m' vm' n ii jj lbl Q R :
    is_linear_of fn (P ++ [:: {| li_ii := ii ; li_i := Lgoto (fn, lbl) |} ] ++ Q ++ [:: {| li_ii := jj ; li_i := Llabel lbl |} ] ++ R ) →
    ~~ has (is_label lbl) P →
    ~~ has (is_label lbl) Q →
    lsem p' {| lscs := scs; lmem := m ; lvm := vm ; lfn := fn ; lpc := size P |} {| lscs := scs'; lmem := m' ; lvm := vm' ; lfn := fn ; lpc := size P + n.+1 |} →
    lsem p' {| lscs := scs; lmem := m ; lvm := vm ; lfn := fn ; lpc := (size P + size Q).+2 |} {| lscs := scs'; lmem := m' ; lvm := vm' ; lfn := fn ; lpc := size P + n.+1 |}.
  Proof.
    move => C Dp Dq /lsem_split_start[].
    - case => _ _ _ K; exfalso; move: K; clear.
      rewrite /addn /addn_rec; lia.
    case => s h E; apply: lsem_trans E.
    move: (C) h; rewrite /lsem1 /step -{1}(addn0 (size _)) => /find_instr_skip ->.
    rewrite /eval_instr /=.
    case: C => fd -> -> /=.
    rewrite find_label_cat_hd; last exact: Dp.
    rewrite find_labelE /= find_label_cat_hd; last exact: Dq.
    rewrite find_labelE /is_label /= eqxx /setcpc /= addn0 addnS => /ok_inj <-{s} /=.
    exact: rt_refl.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p extra_free_registers var_tmp Pc Pi Pi_r.
  Proof.
    red. clear Pfun.
    move => ii k k' krec s1 s2 s3 s4 a c e c' Ec Hc ok_e Ec' Hc' Ew Hw.
    move => fn lbl /checked_iE[] fd ok_fd /=.
    set ι := λ i, {| li_ii := ii ; li_i := i |}.
    have {Hw} := Hw fn lbl.
    rewrite /checked_i ok_fd /=.
    case: is_falseP.
    - by move => ?; subst e.
    t_xrbindP => e_neq_false Hw ok_c ok_c'.
    move: Hw.
    rewrite ok_c ok_c' => /(_ erefl).
    move: ok_e Ew e_neq_false.
    rewrite p_globs_nil.
    case: is_boolP.
    { (* expression is the “true” literal *)
      (* The context is inconsistent, but well, do the proof nonetheless *)
      case => // _ Ew _.
      rewrite linear_c_nil.
      move: {Hc'} (Hc' fn (next_lbl lbl)).
      rewrite /checked_c ok_fd ok_c' => /(_ erefl).
      case: (linear_c fn c' (next_lbl lbl) [::]) (valid_c fn c' (next_lbl lbl)) => lblc' lc'.
      rewrite /next_lbl => - [L' V'] Hc'.
      rewrite linear_c_nil.
      move: {Hc} (Hc fn lblc').
      rewrite /checked_c ok_fd ok_c => /(_ erefl).
      case: (linear_c fn c lblc' [::]) (valid_c fn c lblc') => lblc lc [L V] Hc /= Hw _.
      rewrite add_align_nil.
      move => m vm P Q W M X D C.
      have {Hc} := Hc m vm (P ++ add_align ii a [::] ++ [:: ι (Llabel lbl) ]) (lc' ++ [:: ι (Lgoto (fn, lbl)) ] ++ Q) W M X.
      case.
      - apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
        + apply: disjoint_labels_wL D; lia.
        + by case: (a).
        move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
      - by move: C; rewrite -!/(ι _) /= -!catA /= -!catA cat1s.
      move => m1 vm1 E1 K1 W1 X1 H1 M1.
      have {Hc'} := Hc' m1 vm1 ((P ++ add_align ii a [::] ++ [:: ι (Llabel lbl) ]) ++ lc) ([:: ι (Lgoto (fn, lbl)) ] ++ Q) W1 M1 X1.
      case.
      - repeat apply: disjoint_labels_cat.
        + apply: disjoint_labels_w D; lia.
        + by case: (a).
        + move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
        apply: (valid_disjoint_labels V); left; lia.
      - by move: C; rewrite /= -!catA /= -!catA.
      move => m2 vm2 E2 K2 W2 X2 H2 M2.
      have {Hw} := Hw m2 vm2 P Q W2 M2 X2 D.
      case.
      - by rewrite add_align_nil.
      move => m3 vm3 E3 K3 W3 X3 H3 M3.
      exists m3 vm3; [ | | exact: W3 | exact: X3 | | exact: M3 ]; cycle 1.
      - transitivity vm2; last (apply: vmap_eq_exceptI K3; SvD.fsetdec).
        transitivity vm1; last (apply: vmap_eq_exceptI K2; SvD.fsetdec).
        apply: vmap_eq_exceptI K1; SvD.fsetdec.
      - etransitivity; first exact: H1.
        apply: preserved_metadataE; last (etransitivity; first exact: H2); last first.
        + apply: preserved_metadataE; last exact: H3.
          * exact: sem_stack_stable Ec'.
          exact: sem_validw_stable Ec'.
        + exact: sem_validw_stable Ec.
        exact: sem_stack_stable Ec.
      apply: lsem_trans; last apply: (lsem_trans E1); last apply: (lsem_trans E2).
      - (* align; label *)
        apply: (@lsem_step_end _ _ _ _ p' {| lfn := fn; lpc := size (P ++ add_align ii a [::]) |}); last first.
        + move: C.
          rewrite -!catA catA -{1}(addn0 (size _)) /lsem1 /step => /find_instr_skip ->.
          rewrite /eval_instr /= /setpc /= addn0 !size_cat addnA addn1.
          reflexivity.
        case: a C {Ew E1 E2 E3} => C; last first.
        + rewrite cats0; exact: rt_refl.
        apply: LSem_step.
        move: C.
        rewrite -catA /lsem1 /step -{1}(addn0 (size _)) => /find_instr_skip ->.
        by rewrite /eval_instr /= /setpc /= size_cat /= addn1.
      apply: lsem_step.
      - move: (C).
        rewrite -cat1s !catA -catA.
        rewrite /lsem1 /step -{1}(addn0 (size _)) => /find_instr_skip ->.
        rewrite /eval_instr /= (get_fundef_p' ok_fd) /= /setcpc /=.
        case: C; rewrite (get_fundef_p' ok_fd) => _ /Some_inj <- /= ->.
        rewrite find_label_cat_hd; last by apply: D; lia.
        rewrite -!catA find_label_cat_hd; last by case: (a).
        rewrite find_labelE /= /is_label /= eqxx /= addn0.
        reflexivity.
      rewrite add_align_nil catA size_cat in E3.
      rewrite -!catA in C.
      have {} E3 := lsem_skip_align C E3.
      rewrite !catA -cat1s -!catA catA in C.
      have := lsem_skip_label C E3.
      rewrite -/(size _) !size_cat /= !size_cat /= !addnA.
      exact.
    }
    (* arbitrary expression *)
    move => {} e ok_e Ew e_neq_false.
    case: c' Ec' Hc' ok_c' Ew => [ | i c' ].
    { (* second body is empty *)
      move => /semE[] ??; subst k' s2 => _ _ Ew.
      rewrite linear_c_nil.
      move: {Hc} (Hc fn (next_lbl lbl)).
      rewrite /checked_c ok_fd ok_c => /(_ erefl).
      case: (linear_c fn c (next_lbl lbl) [::]) (valid_c fn c (next_lbl lbl)) => lblc lc.
      rewrite /next_lbl => - [L V] Hc /= Hw _.
      rewrite add_align_nil.
      move => m vm P Q W M X D C.
      have {Hc} := Hc m vm (P ++ add_align ii a [::] ++ [:: ι (Llabel lbl) ]) ([:: ι (Lcond e lbl) ] ++ Q) W M X.
      case.
      - apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
        + apply: disjoint_labels_wL D; rewrite /next_lbl; lia.
        + by case: (a).
        rewrite /next_lbl => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
      - by move: C; rewrite -!/(ι _) /= -!catA /= -!catA.
      move => m1 vm1 E1 K1 W1 X1 H1 M1.
      have [ b /(match_mem_sem_pexpr M1) {} ok_e /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
      have {Hw} := Hw m1 vm1 P Q W1 M1 X1 D.
      case.
      - by rewrite add_align_nil.
      move => m3 vm3 E3 K3 W3 X3 H3 M3.
      exists m3 vm3; [ | | exact: W3 | exact: X3 | | exact: M3 ]; cycle 1.
      - transitivity vm1; last (apply: vmap_eq_exceptI K3; SvD.fsetdec).
        apply: vmap_eq_exceptI K1; SvD.fsetdec.
      - etransitivity; first exact: H1.
        apply: preserved_metadataE; last exact: H3.
        + exact: sem_stack_stable Ec.
        exact: sem_validw_stable Ec.
      apply: lsem_trans; last apply: (lsem_trans E1).
      - (* align; label *)
        apply: (@lsem_step_end _ _ _ _ p' {| lfn := fn; lpc := size (P ++ add_align ii a [::]) |}); last first.
        + move: C.
          rewrite -!catA catA -{1}(addn0 (size _)) /lsem1 /step => /find_instr_skip ->.
          rewrite /eval_instr /= /setpc /= addn0 !size_cat addnA addn1.
          reflexivity.
        case: a C {Ew E1 E3} => C; last first.
        + rewrite cats0; exact: rt_refl.
        apply: LSem_step.
        move: C.
        rewrite -catA /lsem1 /step -{1}(addn0 (size _)) => /find_instr_skip ->.
        by rewrite /eval_instr /= /setpc /= size_cat /= addn1.
      apply: lsem_step.
      - move: (C).
        rewrite /lsem1 /step -{1}(addn0 (size _)) -cat1s !catA -catA => /find_instr_skip ->.
        rewrite /eval_instr /= /to_estate ok_e /= (get_fundef_p' ok_fd) /=.
        case: C; rewrite (get_fundef_p' ok_fd) => _ /Some_inj <- /= ->.
        rewrite -!catA  find_label_cat_hd; last by apply: D; lia.
        rewrite find_label_cat_hd; last by case: (a).
        rewrite find_labelE /= /is_label /= eqxx /= addn0 /setcpc /=.
        reflexivity.
      rewrite add_align_nil catA size_cat in E3.
      rewrite -!catA in C.
      have {} E3 := lsem_skip_align C E3.
      rewrite !catA -cat1s -!catA catA in C.
      have := lsem_skip_label C E3.
      rewrite -/(size _) !size_cat /= !size_cat /= !addnA.
      exact.
    }
    (* General case *)
    clear Pi Pi_r => Ec' Hc' ok_c' Ew.
    rewrite linear_c_nil.
    move: {Hc} (Hc fn (next_lbl (next_lbl lbl))).
    rewrite /checked_c ok_fd ok_c => /(_ erefl).
    case: (linear_c fn c (next_lbl (next_lbl lbl)) [::]) (valid_c fn c (next_lbl (next_lbl lbl))) => lblc lc.
    rewrite /next_lbl => - [L V] Hc.
    rewrite linear_c_nil.
    move: {Hc'} (Hc' fn lblc).
    rewrite /checked_c ok_fd ok_c' => /(_ erefl).
    case: (linear_c fn (i :: c') lblc [::]) (valid_c fn (i :: c') lblc) => lblc' lc' [L' V'] Hc' /= Hw _.
    rewrite add_align_nil.
    move => m vm P Q W M X D C.
    have {Hc} := Hc m vm (P ++ ι (Lgoto (fn, lbl)) :: add_align ii a [::] ++ [:: ι (Llabel (lbl + 1)) ] ++ lc' ++ [:: ι (Llabel lbl) ]) ([:: ι (Lcond e (lbl + 1)) ] ++ Q) W M X.
    case.
    - apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
      + apply: disjoint_labels_w D; lia.
      + by case: (a).
      apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
      + move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
      + apply: (valid_disjoint_labels V'); left; lia.
      move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
    - move: C; rewrite -!/(ι _) /= -!catA -!cat_cons -!catA -(cat1s _ lc) -(cat1s _ Q); exact.
    move => m1 vm1 E1 K1 W1 X1 H1 M1.
    have [ b /(match_mem_sem_pexpr M1) {} ok_e /value_uinclE ? ] := sem_pexpr_uincl X1 ok_e; subst b.
    have {Hc'} := Hc' m1 vm1 (P ++ ι (Lgoto (fn, lbl)) :: add_align ii a [::] ++ [:: ι (Llabel (lbl + 1)) ]) (ι (Llabel lbl) :: lc ++ ι (Lcond e (lbl + 1)) :: Q) W1 M1 X1.
    case.
    - apply: disjoint_labels_cat; last apply: disjoint_labels_cat.
      + apply: disjoint_labels_wL D; lia.
      + by case: (a).
      move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
    - move: C; rewrite -!/(ι _) /= -!catA -!cat_cons -(cat1s _ Q) -(cat1s _ lc') -!catA; exact.
    move => m2 vm2 E2 K2 W2 X2 H2 M2.
    have {Hw} := Hw m2 vm2 P Q W2 M2 X2 D.
    case.
    - by rewrite add_align_nil.
    move => m3 vm3 E3 K3 W3 X3 H3 M3.
    exists m3 vm3; [ | | exact: W3 | exact: X3 | | exact: M3 ]; cycle 1.
    - transitivity vm2; last (apply: vmap_eq_exceptI K3; SvD.fsetdec).
      transitivity vm1; last (apply: vmap_eq_exceptI K2; SvD.fsetdec).
      apply: vmap_eq_exceptI K1; SvD.fsetdec.
    - etransitivity; first exact: H1.
      apply: preserved_metadataE; last (etransitivity; first exact: H2); last first.
      + apply: preserved_metadataE; last exact: H3.
        * exact: sem_stack_stable Ec'.
        exact: sem_validw_stable Ec'.
      + exact: sem_validw_stable Ec.
      exact: sem_stack_stable Ec.
    apply: lsem_step; last apply: (lsem_trans E1).
    - move: (C).
      rewrite /lsem1 /step -{1}(addn0 (size _)) => /find_instr_skip ->.
      rewrite /eval_instr /= (get_fundef_p' ok_fd) /=.
      case: C; rewrite (get_fundef_p' ok_fd) => _ /Some_inj <- /= ->.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite -!catA find_labelE /= find_label_cat_hd; last by case: (a).
      rewrite find_labelE /is_label /= eq_sym next_lbl_neq -!catA find_label_cat_hd; last first.
      + apply: (valid_has_not_label V'); left; lia.
      rewrite find_labelE /= /is_label /= eqxx /= /setcpc /=.
      by repeat rewrite size_cat /= !addnS.
    apply: lsem_step; last apply: (lsem_trans E2).
    - move: (C).
      rewrite -!cat_cons !catA -(cat1s _ lc') -(cat1s _ lc) !catA -catA.
      rewrite /lsem1 /step -{1}(addn0 (size _)) => /find_instr_skip ->.
      rewrite /eval_instr /= (get_fundef_p' ok_fd) /=.
      case: C; rewrite (get_fundef_p' ok_fd) => _ /Some_inj <- /= ->.
      rewrite /to_estate ok_e /= /setcpc /=.
      rewrite find_label_cat_hd; last by apply: D; lia.
      rewrite -!catA find_labelE /= find_label_cat_hd; last by case: (a).
      rewrite find_labelE /= /is_label /= eqxx /=.
      by repeat rewrite size_cat /= !addnS.
    apply: lsem_step.
    - move: C.
      rewrite -!cat_cons -(cat1s _ lc) -(cat1s _ lc') !catA -catA -catA -catA.
      rewrite /lsem1 /step -{1}(addn0 (size _)) => /find_instr_skip ->.
      rewrite /eval_instr /= /setpc /=.
      reflexivity.
    have {} C : is_linear_of fn (P ++ [:: ι (Lgoto (fn, lbl)) ] ++ (add_align ii a [::] ++ ι (Llabel (lbl + 1)) :: lc') ++ [:: ι (Llabel lbl)] ++ lc ++ ι (Lcond e (lbl + 1)) :: Q).
    - move: C; clear.
      rewrite -!cat_cons -!catA -(cat1s _ (add_align _ _ _)) -(cat1s _ lc) -(cat1s _ Q) -!catA.
      exact.
    rewrite size_cat add_align_nil in E3.
    have := lsem_skip_goto C _ _ E3.
    rewrite -/(size _); repeat rewrite size_cat /=.
    rewrite !addnA !addnS !addn0 addSn.
    apply.
    - apply: D; lia.
    have h : (lbl < lblc)%positive by lia.
    have := @valid_has_not_label _ _ _ _ lbl V' (or_introl h).
    rewrite has_cat /is_label /= eq_sym next_lbl_neq negb_or => ->.
    by case: (a).
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p extra_free_registers var_tmp Pc Pi_r.
  Proof.
    move => ii k s1 s2 a c e c' Ec Hc; rewrite p_globs_nil => ok_e fn lbl /checked_iE[] fd ok_fd /=.
    case: is_falseP.
    { (* expression is the “false” literal *)
      move => ?; subst e.
      move => ok_c /=.
      move: {Hc} (Hc fn lbl).
      rewrite /checked_c ok_fd ok_c => /(_ erefl).
      case: (linear_c fn c lbl [::]) => lblc lc.
      move => Hc _.
      move => m vm P Q W M X D C.
      have {Hc} [ m' vm' E K W' X' H' M' ] := Hc m vm P Q W M X D C.
      exists m' vm'; [ exact: E | | exact: W' | exact: X' | exact: H' | exact: M' ].
      apply: vmap_eq_exceptI K; SvD.fsetdec.
    }
    (* arbitrary expression *)
    t_xrbindP => e_not_trivial ok_c ok_c'.
    replace (is_bool e) with (@None bool);
      last by case: is_boolP ok_e e_not_trivial => // - [].
    case: c' ok_c' => [ | i c' ] ok_c'.
    { (* second body is empty *)
      rewrite linear_c_nil.
      move: {Hc} (Hc fn (next_lbl lbl)).
      rewrite /checked_c ok_fd ok_c => /(_ erefl).
      case: (linear_c fn c (next_lbl lbl) [::]) => lblc lc.
      move => Hc _.
      rewrite /= add_align_nil.
      move => m vm P Q W M X D.
      rewrite -cat1s !catA.
      set prefix := (X in X ++ lc).
      do 2 rewrite -catA.
      set suffix := (X in lc ++ X).
      move => C.
      have {Hc} [ | m' vm' E  K W' X' H' M' ] := Hc m vm prefix suffix W M X _ C.
      - apply: disjoint_labels_cat; first apply: disjoint_labels_cat.
        + apply: disjoint_labels_wL _ D; rewrite /next_lbl; lia.
        + by case: (a).
        clear.
        rewrite /next_lbl => lbl' range.
        rewrite /is_label /= orbF; apply/eqP; lia.
      have [ ] := sem_pexpr_uincl X' ok_e.
      case => // - [] // /(match_mem_sem_pexpr M') {} ok_e _.
      exists m' vm'; [ | | exact: W' | exact: X' | exact: H' | exact: M' ]; last first.
      - apply: vmap_eq_exceptI K; SvD.fsetdec.
      apply: lsem_trans; last apply: (lsem_trans E).
      - apply: (@lsem_trans _ _ _ _ _ {| lmem := m ; lvm := vm ; lfn := fn ; lpc := size (P ++ add_align ii a [::]) |}).
        + subst prefix; case: a C {E} => C; last by rewrite cats0; exact: rt_refl.
          apply: LSem_step.
          move: C.
          rewrite /lsem1 /step -!catA -(addn0 (size _)) => /find_instr_skip ->.
          by rewrite /eval_instr /= size_cat addn0 addn1.
        apply: LSem_step.
        move: C.
        rewrite /lsem1 /step -catA -(addn0 (size _)) => /find_instr_skip ->.
        by rewrite /eval_instr /= (size_cat _ [:: _]) addn0 addn1.
      apply: LSem_step.
      move: C.
      rewrite /lsem1 /step catA -(addn0 (size _)) => /find_instr_skip ->.
      by rewrite /eval_instr /= /to_estate /= ok_e /= (size_cat _ [:: _]) addn0 addn1.
    }
    (* general case *)
    rewrite linear_c_nil.
    move: {Hc} (Hc fn (next_lbl (next_lbl lbl))).
    rewrite /checked_c ok_fd ok_c => /(_ erefl).
    case: (linear_c fn c (next_lbl (next_lbl lbl)) [::]) (valid_c fn c (next_lbl (next_lbl lbl))) => lblc lc.
    rewrite /next_lbl => -[L V] Hc _.
    rewrite linear_c_nil.
    case: (linear_c fn (i :: c') lblc [::]) (valid_c fn (i :: c') lblc) => lblc' lc' [L' V'].
    rewrite /= add_align_nil.
    move => m vm P Q W M X D.
    rewrite -cat1s -(cat1s _ (lc' ++ _)) -(cat1s _ (lc ++ _)) !catA.
    set prefix := (X in X ++ lc).
    do 2 rewrite -catA.
    set suffix := (X in lc ++ X).
    move => C.
    have {Hc} [ | m' vm' E  K W' X' H' M' ] := Hc m vm prefix suffix W M X _ C.
    - subst prefix; move: L' V' D; clear.
      rewrite /next_lbl => L' V' D.
      repeat apply: disjoint_labels_cat; try by [].
      + apply: disjoint_labels_w _ D; lia.
      + by case: (a).
      + move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
      + apply: (valid_disjoint_labels V'); left; lia.
      move => lbl' range; rewrite /is_label /= orbF; apply/eqP; lia.
    have [ ] := sem_pexpr_uincl X' ok_e.
    case => // - [] // /(match_mem_sem_pexpr M') {} ok_e _.
    exists m' vm'; [ | | exact: W' | exact: X' | exact: H' | exact: M' ]; last first.
    - apply: vmap_eq_exceptI K; SvD.fsetdec.
    apply: lsem_trans; last apply: (lsem_trans E).
    - (* goto *)
      apply: LSem_step.
      move: (C).
      rewrite /lsem1 /step -!catA -{1}(addn0 (size _)) => /find_instr_skip ->.
      rewrite /eval_instr /= (get_fundef_p' ok_fd) /=.
      case: C; rewrite (get_fundef_p' ok_fd) => _ /Some_inj <- /= ->.
      rewrite -!catA find_label_cat_hd; last by apply: D; lia.
      rewrite find_labelE /= find_label_cat_hd; last by case: (a).
      rewrite find_labelE /is_label /= eq_sym next_lbl_neq.
      rewrite find_label_cat_hd; last by apply: (valid_has_not_label V'); lia.
      rewrite find_labelE /is_label /= eqxx /= /setcpc /=.
      by rewrite !size_cat /= !addnS !addn0 !addnA !addSn.
    (* cond false *)
    apply: LSem_step.
    move: (C).
    rewrite /lsem1 /step -(addn0 (size _)) catA => /find_instr_skip ->.
    rewrite /eval_instr /= ok_e /=.
    by rewrite !size_cat /= !size_cat /= !addnS !addnA !addn0 !addSn.
  Qed.

  Lemma find_entry_label fn fd :
    sf_return_address (f_extra fd) ≠ RAnone →
    find_label xH (lfd_body (linear_fd fn fd).2) = ok 0.
  Proof. by rewrite /linear_fd /linear_body; case: sf_return_address. Qed.

  Lemma is_label_lmove lbl ii x ws y :
    is_label lbl (of_olinstr_r ii (lmove liparams x ws y)) = false.
  Proof.
    rewrite /lmove /lassign.
    by case: lip_lassign => [[[? ?] ?]|].
  Qed.

  Lemma is_label_lstore lbl ii x ofs ws y :
    is_label lbl (of_olinstr_r ii (lstore liparams x ofs ws y)) = false.
  Proof.
    rewrite /lstore /lassign.
    by case: lip_lassign => [[[? ?] ?]|].
  Qed.

  Lemma preserved_meta_store_top_stack s1 m1 fd' (ptr : word Uptr) m m' : 
    alloc_stack s1 (sf_align (f_extra fd')) (sf_stk_sz (f_extra fd')) (sf_stk_ioff (f_extra fd')) (sf_stk_extra_sz (f_extra fd')) = ok m
    → write m1 (top_stack_after_alloc (top_stack s1) (sf_align (f_extra fd')) (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd'))) ptr = ok m'
    → [&& (0 <=? sf_stk_sz (f_extra fd'))%Z, (0 <=? sf_stk_extra_sz (f_extra fd'))%Z & (stack_frame_allocation_size (f_extra fd') <? wbase Uptr)%Z]
    → is_align (top_stack s1) (sf_align (f_extra fd')) 
    → wsize_size Uptr = sf_stk_ioff (f_extra fd') 
    → preserved_metadata s1 m1 m'.
  Proof.
    move=> ok_m ok_m' ok_stk_sz sp_aligned hioff a [] a_lo a_hi.
    have A := alloc_stackP ok_m.
    have top_range := ass_above_limit A.
    rewrite (CoreMem.writeP_neq ok_m'); first reflexivity.
    apply: disjoint_range_U8 => i i_range ? {ok_m'}; subst a.
    move: a_lo {a_hi}.
    rewrite (top_stack_after_aligned_alloc _ sp_aligned) -/(stack_frame_allocation_size (f_extra fd')).
    rewrite addE -!GRing.addrA.
    replace (wrepr _ _ + _)%R with (- wrepr Uptr (stack_frame_allocation_size (f_extra fd') - i))%R; last first.
    + by rewrite !wrepr_add !wrepr_opp; ssring.
    have := round_ws_range (sf_align (f_extra fd')) (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd')).
    have :=  ass_ioff A; case/and3P: ok_stk_sz; rewrite !zify -hioff /stack_frame_allocation_size.
    move=> h1 h2 h3 h4.
    have := aligned_alloc_no_overflow h1 h2 h3 sp_aligned ok_m.
    move: (sf_stk_extra_sz _) (sf_stk_sz _) (round_ws _ _) h1 h2 h3 h4 top_range.
    move=> extra_sz sz round h1 h2 h3 h4 top_range h5 h6.
    rewrite wunsigned_sub; first lia.
    assert (X := wunsigned_range (top_stack s1)); lia.
  Qed.

  Local Lemma Hcall : sem_Ind_call p extra_free_registers var_tmp Pi_r Pfun.
  Proof.
    move => ii k s1 s2 ini res fn' args xargs xres ok_xargs ok_xres exec_call ih fn lbl /checked_iE[] fd ok_fd chk_call.
    case linear_eq: linear_i => [lbli li].
    move => fr_undef m1 vm2 P Q W M X D C.
    move: chk_call => /=.
    t_xrbindP => /negbTE fn'_neq_fn.
    case ok_fd': (get_fundef _ fn') => [ fd' | ] //; t_xrbindP => ok_ra ok_align _.
    have := get_fundef_p' ok_fd'.
    set lfd' := linear_fd _ fd'.
    move => ok_lfd'.
    move: linear_eq; rewrite /= ok_fd' fn'_neq_fn.
    move: (checked_prog ok_fd') => /=; rewrite /check_fd.
    t_xrbindP => chk_body ok_to_save ok_stk_sz ok_ret_addr ok_save_stack _.
    have ok_body' : is_linear_of fn' (lfd_body lfd'.2).
    - by rewrite /is_linear_of; eauto.
    move: ih; rewrite /Pfun; move => /(_ _ _ _ _ _ _ _ _ _ _ ok_body') ih A.
    have lbl_valid : (fn, lbl) \in (label_in_lprog p').
    - clear -A C ok_ra hliparams.
      apply: (label_in_lfundef _ C).
      case: sf_return_address A ok_ra => [ | ra | ra z ] //=.
      1-2: case => _ <- _.
      1-2: rewrite /label_in_lcmd /=.
      1-2: by rewrite !pmap_cat !mem_cat inE eqxx !orbT.

    assert (h := encode_label_dom small_dom_p' lbl_valid).
    case ok_ptr: encode_label h => [ ptr | // ] _.
    case/sem_callE: (exec_call) => ? m s' k' args' res'; rewrite ok_fd' => /Some_inj <- ra_sem ok_ss sp_aligned T ok_m ok_args' wt_args' exec_cbody ok_res' wt_res' T' s2_eq.
    rewrite /ra_valid in ra_sem.
    rewrite /top_stack_aligned in sp_aligned.
    rewrite /ra_vm. 
    move: A; rewrite (negbTE ok_ra) => {ok_save_stack} -[] ??; subst lbli li.
    set rastack_before := is_rastack_none _.
    set rastack_after  := is_rastack _.
    set sz := stack_frame_allocation_size _.
    set sz_before := if rastack_before then (sz - wsize_size Uptr)%Z else sz.
    set sz_after := if rastack_after then (sz - wsize_size Uptr)%Z else sz.
    set before :=  allocate_stack_frame _ _ _ _ _ rastack_before.
    set after :=  allocate_stack_frame _ _ _ _ _ rastack_after.
    move: C; set P' := P ++ _ => C.
    set vm2_b := 
      if sz_before == 0%Z then vm2 else (vm2.[vrsp <- ok (pword_of_word (top_stack (emem s1) -  wrepr Uptr sz_before))])%vmap.
    move: (X vrsp); rewrite T.
    case vm2_rsp: vm2.[_]%vmap => [ top_ptr | // ] /= /pword_of_word_uincl[].
    case: top_ptr vm2_rsp => ? ? le_refl vm2_rsp /= ? ?; subst.
    have h1 : 
      lsem p' (Lstate (escs s1) m1 vm2 fn (size P))
              (Lstate (escs s1) m1 vm2_b fn (size P + size before)).
    + move: C ; rewrite /P' /vm2_b /before /sz_before /rastack_before /allocate_stack_frame /sz; case: eqP => _ C /=.
      + by rewrite addn0; apply rt_refl.
      apply LSem_step; rewrite /lsem1 /step -(addn0 (size P)) (find_instr_skip C) /= addn0 addn1.
      apply (spec_lip_allocate_stack_frame
               hliparams
               _ _
               (s := {| emem := _; evm := _; |})).
      by rewrite /= vm2_rsp pword_of_wordE.
    set r := sf_return_address (f_extra fd').
    set o := Some ((fn, lbl), P', (size P + size before).+1).
    set s := (top_stack (emem s1) - wrepr Uptr sz)%R.
    set ra := 
      match r with
      | RAnone => None
      | RAreg ra => Some (mk_var_i ra)
      | RAstack ra _ => mk_ovar_i ra
      end.
    have vm2_b_upd : Fv.ext_eq vm2_b vm2.[vrsp <- ok (pword_of_word (top_stack (emem s1) -  wrepr Uptr sz_before))]%vmap.
    + move=> x; rewrite /vm2_b Fv.setP; case: eqP => [ | /eqP] *.
      + subst x; case: eqP => [-> | ?]; last by rewrite Fv.setP_eq.
        by rewrite wrepr0 GRing.subr0 vm2_rsp pword_of_wordE.
      by case: eqP => // _; rewrite Fv.setP_neq.       
    have [m' [vm' [hwf_vm hmatch [hvm'_rsp heq_vm'] [hvalue_of hpres_m1_m'] h2]]] : exists m' vm',
      [/\ wf_vm vm', match_mem s1 m',
          vm'.[vrsp]%vmap = ok (pword_of_word s) /\ 
          vm2 = vm' [\ Sv.add vrsp (if ra is Some x then Sv.singleton x else Sv.empty)],
          value_of_ra m' vm' r o /\ preserved_metadata s1 m1 m' &
          eval_instr p' {| li_ii := ii; li_i := Lcall ra (fn', 1%positive) |} 
             {| lscs := escs s1; lmem := m1; lvm := vm2_b; lfn := fn; lpc := size P + size before |} = 
          ok {| lscs := escs s1; lmem := m'; lvm := vm'; lfn := fn'; lpc := 1 |}].
    + rewrite /eval_instr /= /ra /r /get_label_after_pc /setpc /=.
      have -> /= : find_instr p' {| lscs := escs s1; lmem := m1; lvm := vm2_b; lfn := fn; lpc := (size P + size before).+1 |} = 
              Some {| li_ii := ii; li_i := linear.Llabel ExternalLabel lbl |}.
      + by rewrite -addn1 -addnA (find_instr_skip C) -/before -catA oseq.onth_cat ltnNge addn1 leqnSn /= subSnn.
      rewrite ok_ptr ok_lfd' /= find_entry_label /=; last by apply/eqP.
      have wf_vm2_b : wf_vm vm2_b.
      + by rewrite /vm2_b; case: eqP => // _; apply wf_vm_set.
      have wf_set_vm : forall x, vtype x == sword Uptr -> wf_vm (vm2_b.[x <- pof_val (vtype x) (Vword ptr)])%vmap.
      + move=> x hx y; rewrite Fv.setP; case: eqP => ?; last by apply wf_vm2_b.
        by subst; move/eqP: hx => ->.
      rewrite sumbool_of_boolET.
      have hfind : find_label lbl P' = ok (size P + size before).+1.
      + rewrite /P' find_label_cat_hd; last by apply: D; rewrite /next_lbl; Psatz.lia.
        rewrite -catA find_label_cat_hd; last by rewrite /allocate_stack_frame; case: eqP => //.
        by rewrite /find_label /is_label /= eqxx /= addn1 addnS.
      case eq_ra : sf_return_address ok_ra ok_ret_addr ra_sem sp_aligned => [ | x | [ x | ] ofs] // _ ok_ret_addr ra_sem sp_aligned.
      (* RAreg x *)
      + exists m1,  vm2_b.[x <- pof_val (vtype x) (Vword ptr)]%vmap; split => //.
        + by apply wf_set_vm.
        + split.
          + rewrite Fv.setP_neq; last by case/and3P : ra_sem.
            by rewrite vm2_b_upd Fv.setP_eq /sz_before /rastack_before eq_ra. 
          move=> /= y hy; rewrite Fv.setP_neq; last by apply/eqP; move: hy; clear; SvD.fsetdec.
          by rewrite vm2_b_upd Fv.setP_neq //; apply/eqP; move: hy; clear; SvD.fsetdec.
        + split => //. 
          rewrite /value_of_ra.
          case: (x) ok_ret_addr => /= ? vra /eqP ->; rewrite eq_refl; split => //.
          by rewrite ok_ptr; exists ptr => //; rewrite Fv.setP_eq /pof_val to_pword_u zero_extend_u.
        by rewrite set_well_typed_var //=; apply/eqP.
      (* RAstack (Some x) ofs *)
      + case/and4P: ok_ret_addr => /andP [] ok_ret_addr _ _ _ _.
        exists m1, vm2_b.[x <- pof_val (vtype x) (Vword ptr)]%vmap; split => //.
        + by apply wf_set_vm.
        + split.
          + rewrite Fv.setP_neq; last by case/andP : ra_sem.
            by rewrite vm2_b_upd Fv.setP_eq /sz_before /rastack_before eq_ra. 
          move=> /= y hy; rewrite Fv.setP_neq; last by apply/eqP; move: hy; clear; SvD.fsetdec.
          by rewrite vm2_b_upd Fv.setP_neq //; apply/eqP; move: hy; clear; SvD.fsetdec.
        + split => //.
          rewrite /value_of_ra.
          case: (x) ok_ret_addr => /= ? vra /eqP ->; rewrite eq_refl; split => //.
          by rewrite ok_ptr; exists ptr => //; rewrite Fv.setP_eq /pof_val to_pword_u zero_extend_u.
        by rewrite /= set_well_typed_var //=; apply/eqP.
      (* RAstack None ofs *)
      move: ok_ret_addr => /and4P [] _ /eqP ? /eqP hioff sf_align_for_ptr; subst ofs.
      have [m' ok_m' M']: 
         exists2 m1', write m1 (top_stack_after_alloc (top_stack (emem s1)) (sf_align (f_extra fd'))
                   (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd')))%R ptr = ok m1' &
                         match_mem s1 m1'.
      + apply: mm_write_invalid; first exact: M; last first.
        * apply: (is_align_m sf_align_for_ptr); exact: do_align_is_align.
        have := (Memory.alloc_stackP ok_m).(ass_above_limit).
        rewrite (alloc_stack_top_stack ok_m).
        rewrite top_stack_after_aligned_alloc // wrepr_opp.
        have := ass_ioff (alloc_stackP ok_m); rewrite -hioff.
        move: ok_stk_sz. clear.
        have := round_ws_range (sf_align (f_extra fd')) (sf_stk_sz (f_extra fd') + sf_stk_extra_sz (f_extra fd')).
        rewrite !zify -/(stack_frame_allocation_size (f_extra fd')) => hround - [] sz_pos [] extra_pos sz_noof uptr_sz.
        set L := stack_limit (emem s1).
        have L_range := wunsigned_range L.
        move: (stack_frame_allocation_size _) hround sz_noof => S hround sz_noof.
        move: (top_stack (emem s1)) => T above_limit.
        have S_range : (0 <= S < wbase Uptr)%Z.
        - by move: ( sf_stk_sz (f_extra fd')) (sf_stk_extra_sz (f_extra fd')) sz_pos extra_pos hround; lia.
        have X : (wunsigned (T - wrepr Uptr S) <= wunsigned T)%Z.
        * move: (sf_stk_sz _) sz_pos above_limit => n; lia.
        have {X} TmS := wunsigned_sub_small S_range X.
        rewrite TmS in above_limit.
        lia.
      exists m', vm2_b.[vrsp <- ok (pword_of_word s)]%vmap; split => //.
      + by apply wf_vm_set. 
      + split; first by rewrite Fv.setP_eq.
        move=> /= y hy; rewrite Fv.setP_neq; last by apply/eqP; move: hy; clear; SvD.fsetdec.
        by rewrite vm2_b_upd Fv.setP_neq //; apply/eqP; move: hy; clear; SvD.fsetdec.
      + split.
        + rewrite /value_of_ra /=; split => //.
          rewrite ok_ptr; exists ptr => //; exists s; first by rewrite Fv.setP_eq.
          move: ok_m'; rewrite /=  wrepr0 GRing.addr0 top_stack_after_aligned_alloc // wrepr_opp.
          by apply writeP_eq.
        by apply: preserved_meta_store_top_stack ok_m ok_m' ok_stk_sz sp_aligned hioff.
      set s_ := (top_stack (emem s1) - wrepr Uptr sz_before)%R; rewrite lp_rspE.
      have -> /= : Let x := get_var vm2_b vrsp in to_pointer x = ok s_.
      + rewrite /vm2_b /s_; case: eqP => [-> | _].
        + by rewrite GRing.subr0 /get_var /= vm2_rsp /= truncate_word_u. 
        by rewrite /get_var /= Fv.setP_eq /= truncate_word_u. 
      move: ok_m'; rewrite /s_ /sz_before /rastack_before eq_ra /= wrepr_sub.
      set ts := top_stack _.
      have -> : 
        (ts - (wrepr Uptr sz - wrepr Uptr (wsize_size Uptr)) - wrepr Uptr (wsize_size Uptr))%R = 
        (ts - wrepr Uptr sz)%R 
        by ssrring.ssring.
      by rewrite top_stack_after_aligned_alloc // wrepr_opp => -> /=; rewrite pword_of_wordE.
    have huincl : vm_uincl
                (kill_vars
                   match r with
                   | RAnone => Sv.singleton var_tmp
                   | RAreg x | RAstack (Some x) _ => Sv.singleton x
                   | RAstack None _ => Sv.empty
                   end s1).[vrsp <- ok (pword_of_word s)] vm'.
    + move=> y; rewrite Fv.setP; case: eqP => heq; first by subst y; rewrite hvm'_rsp.
      rewrite /r kill_varsE; case: Sv_memP => hin.
      + case: (vm'.[y])%vmap (hwf_vm y) => //.
        + by move=> *; apply eval_uincl_undef.
        by case => //; case: (vtype y).
      rewrite -heq_vm' // /ra /r; move: heq hin; clear.
      by case: sf_return_address => [ | x | [x | ] ofs] /=; SvD.fsetdec.
    have his_ra: is_ra_of fn' r by exists fd'.
    case (ih _ _ _ _ _ [::] hwf_vm hmatch huincl his_ra hvalue_of) => //.
    + by rewrite /is_sp_for_call; exists fd' => //; case: sf_return_address sp_aligned ok_ra.
    + by rewrite /is_callee_saved_of; exists fd' => //; case: sf_return_address ok_ra.
    move=> m2' vm2' /= h3 heq_vm hwf_vm' hsub_vm' hpres hmatch' hk.
    set ts := top_stack (M := Memory.M) s1.
    set vm2'_b := if sz_after == 0%Z then vm2' else vm2'.[vrsp <- ok (pword_of_word ts)]%vmap.
    have vm2'_rsp: 
       vm2'.[vrsp]%vmap = ok (pword_of_word (s + wrepr Uptr (if rastack_after then wsize_size Uptr else 0%Z))).
      + have /hsub_vm': ¬ Sv.In vrsp (sv_of_list id [::]).
        + by rewrite /sv_of_list /=; SvD.fsetdec.
        rewrite Fv.setP_eq /=; case: Fv.get => //= -[? ? le_refl'] /pword_of_word_uincl /= [e] ?; subst.
        rewrite /rastack_after /r pword_of_wordE.
        by case sf_return_address => //= *; rewrite wrepr0 GRing.addr0. 
    have vm2'_b_upd : Fv.ext_eq vm2'_b vm2'.[vrsp <- ok (pword_of_word ts)].
    + move=> y; rewrite Fv.setP; case: eqP => [ | /eqP] heq;
        last by rewrite /vm2'_b; case: eqP => // _; rewrite Fv.setP_neq.
      subst y; rewrite /vm2'_b; case: eqP => heq; last by rewrite Fv.setP_eq.
      rewrite vm2'_rsp  /s -/ts; do 2! f_equal.
      have -> : (ts - wrepr Uptr sz + wrepr Uptr (if rastack_after then wsize_size Uptr else 0%Z))%R = 
                (ts - (wrepr Uptr sz_after))%R.
      + by rewrite /sz_after; case: (rastack_after); rewrite ?wrepr0 ?wrepr_sub; ssrring.ssring.
      by rewrite heq wrepr0; ssrring.ssring.
    apply (Ex2_6 (x1:=m2')(x2:=vm2'_b)).
    + apply/(lsem_trans h1)/lsem_step.
      + by rewrite /lsem1 /step (find_instr_skip C) -/before -catA oseq.onth_cat ltnn subnn /= h2.
      apply/(lsem_trans h3).
      rewrite /after /vm2'_b /allocate_stack_frame -/sz_after; case: ifP => heq.
      + by rewrite !size_cat /= addnA addn2; apply rt_refl.
      apply /LSem_step.
      rewrite /lsem1/step -addn2 -addnA (find_instr_skip C) -/before.
      rewrite cats0 -catA oseq.onth_cat ltnNge leq_addr /= addKn /allocate_stack_frame -/sz_after heq.
      rewrite !size_cat /= !addnA (addnS _ 2).
      have := (spec_lip_free_stack_frame
                hliparams
                p' fn _  
                (s := {| emem := _; evm := _; |})).
      move=> /(_  (sp_rsp (p_extra p)) (escs s2) m2' vm2' (size P + size before + 2) ii _ sz_after vm2'_rsp) /= ->.
      rewrite /of_estate /with_vm /=; do 5!f_equal.
      by rewrite /s /sz_after; case rastack_after; rewrite ?wrepr0 ?wrepr_sub; ssrring.ssring. 
    + move => x x_notin_k.
      rewrite vm2'_b_upd Fv.setP; case: eqP => x_neq_rsp.
      * by subst; rewrite vm2_rsp pword_of_wordE.
      rewrite -heq_vm.
      + apply heq_vm'. move: x_notin_k x_neq_rsp; rewrite hk /ra /r /=; clear.
        by case: sf_return_address => [ | r | [ r | ] ?] /=; SvD.fsetdec. 
      by move: x_notin_k x_neq_rsp; clear; case: (r) => * //; rewrite /sv_of_list /=; SvD.fsetdec.
    + by rewrite /vm2'_b; case: ifP => _ //; apply wf_vm_set.   
    + have := sem_one_varmap_facts.sem_call_valid_RSP exec_call.
      rewrite /= /valid_RSP /set_RSP => h x /=.
      rewrite vm2'_b_upd Fv.setP; case: eqP => [ | /eqP] *; first by subst x; rewrite h.
      have := hsub_vm' x; rewrite Fv.setP_neq //; apply; rewrite /sv_of_list /=; clear; SvD.fsetdec.
    + by etransitivity; eauto.
    exact hmatch'.
   Qed.

  Lemma RSP_in_magic :
    Sv.In vrsp (magic_variables p).
  Proof. by rewrite Sv.add_spec Sv.singleton_spec; right. Qed.

  Lemma push_to_save_has_no_label ii lbl m :
    ~~ has (is_label lbl) (push_to_save liparams p ii m).
  Proof.
    elim: m => // - [] x ofs m /= /negbTE ->.
    case: is_word_type => // ws.
    by rewrite is_label_lstore.
  Qed.

  Lemma not_magic_neq_rsp x :
    ~~ Sv.mem x (magic_variables p) →
    (x == vrsp) = false.
  Proof.
    rewrite /magic_variables => /Sv_memP H.
    apply/eqP => Hvrsp.
    clear -H Hvrsp.
    apply H.
    rewrite Hvrsp.
    exact: in_add_singleton.
  Qed.

  Lemma all_disjoint_aligned_betweenP (lo hi: Z) (al: wsize) A (m: seq A) (slot: A → cexec (Z * wsize)) :
    all_disjoint_aligned_between lo hi al m slot = ok tt →
    if m is a :: m' then
      exists ofs ws,
        [/\ slot a = ok (ofs, ws),
         (lo <= ofs)%Z,
         (ws ≤ al)%CMP,
         is_align (wrepr Uptr ofs) ws &
         all_disjoint_aligned_between (ofs + wsize_size ws) hi al m' slot = ok tt
        ]
    else
      (lo <= hi)%Z.
  Proof.
    case: m lo => [ | a m ] lo.
    - by apply: rbindP => _ /ok_inj <- /assertP /lezP.
    apply: rbindP => last /=.
    apply: rbindP => mid.
    case: (slot a) => // - [] ofs ws /=.
    t_xrbindP => /lezP lo_le_ofs ok_ws aligned_ofs <-{mid} ih last_le_hi.
    exists ofs, ws; split => //.
    by rewrite /all_disjoint_aligned_between ih /= /assert ifT.
  Qed.

  Lemma all_disjoint_aligned_between_range (lo hi: Z) (al: wsize) A (m: seq A) (slot: A → cexec (Z * wsize)) :
    all_disjoint_aligned_between lo hi al m slot = ok tt →
    (lo <= hi)%Z.
  Proof.
    rewrite /all_disjoint_aligned_between; t_xrbindP => last h /lezP last_le_hi.
    apply: Z.le_trans last_le_hi.
    elim: m lo h.
    - by move => ? /ok_inj ->; reflexivity.
    move => a m ih lo /=; t_xrbindP => mid [] ofs x _; t_xrbindP => /lezP lo_le_ofs _ _ <-{mid} /ih.
    have := wsize_size_pos x.
    lia.
  Qed.

  (* Convenient weaker form of preserved-metatada *)
  Lemma preserved_metadata_w m al sz ioff sz' m' m1 m2:
    alloc_stack m al sz ioff sz' = ok m' →
    (0 <= sz)%Z →
    preserved_metadata m' m1 m2 →
    ∀ p,
      (wunsigned (top_stack m') <= wunsigned p < wunsigned (top_stack m))%Z →
      ~~ validw m' p U8 → read m1 p U8 = read m2 p U8.
  Proof.
    move => ok_m' sz_pos M a [] a_lo a_hi; apply: M; split; first exact: a_lo.
    have A := alloc_stackP ok_m'.
    rewrite A.(ass_root).
    apply: Z.lt_le_trans; first exact: a_hi.
    exact: top_stack_below_root.
  Qed.

  Lemma stack_slot_in_bounds m al sz ioff  sz' m' ofs ws i :
    alloc_stack m al sz ioff sz' = ok m' →
    (0 <= sz)%Z →
    (0 <= sz')%Z →
    (sz <= ofs)%Z →
    (ofs + wsize_size ws <= sz + sz')%Z →
    (0 <= i < wsize_size ws)%Z →
    (wunsigned (top_stack m') + sz <= wunsigned (add (top_stack m' + wrepr Uptr ofs)%R i)
     ∧ wunsigned (add (top_stack m' + wrepr Uptr ofs)%R i) < wunsigned (top_stack m))%Z.
  Proof.
    move => ok_m' sz_pos sz'_pos ofs_lo ofs_hi i_range.
    have A := alloc_stackP ok_m'.
    have below_old_top : (wunsigned (top_stack m') + ofs + i < wunsigned (top_stack m))%Z.
    - apply: Z.lt_le_trans; last exact: proj2 (ass_above_limit A).
      rewrite -!Z.add_assoc -Z.add_lt_mono_l Z.max_r //.
      have := wsize_size_pos ws.
      lia.
    have ofs_no_overflow : (0 <= wunsigned (top_stack m') + ofs)%Z ∧ (wunsigned (top_stack m') + ofs + i < wbase Uptr)%Z.
    - split; first by generalize (wunsigned_range (top_stack m')); lia.
      apply: Z.lt_trans; last exact: proj2 (wunsigned_range (top_stack m)).
      exact: below_old_top.
    rewrite !wunsigned_add; lia.
  Qed.

  Lemma mm_can_write_after_alloc m al sz ioff sz' m' m1 ofs ws (v: word ws) :
    alloc_stack m al sz ioff sz' = ok m' →
    (0 <= sz)%Z →
    (0 <= sz')%Z →
    (ws ≤ al)%CMP →
    is_align (wrepr Uptr ofs) ws →
    (sz <= ofs)%Z →
    (ofs + wsize_size ws <= sz + sz')%Z →
    match_mem m m1 →
    ∃ m2,
      [/\
       write m1 (top_stack m' + wrepr Uptr ofs)%R v = ok m2,
       preserved_metadata m m1 m2 &
       match_mem m m2
      ].
  Proof.
    move => ok_m' sz_pos extra_pos frame_aligned ofs_aligned ofs_lo ofs_hi M.
    have A := alloc_stackP ok_m'.
    have ofs_no_overflow : (0 <= wunsigned (top_stack m') + ofs)%Z ∧ (wunsigned (top_stack m') + ofs < wbase Uptr)%Z.
    - split; first by generalize (wunsigned_range (top_stack m')); lia.
      apply: Z.le_lt_trans; last exact: proj2 (wunsigned_range (top_stack m)).
      apply: Z.le_trans; last exact: proj2 (ass_above_limit A).
      rewrite -Z.add_assoc -Z.add_le_mono_l Z.max_r //.
      have := wsize_size_pos ws.
      lia.
    have ofs_below : (wunsigned (top_stack m') + ofs + wsize_size ws <= wunsigned (top_stack m))%Z.
    - apply: Z.le_trans; last exact: proj2 (ass_above_limit A).
      by rewrite -!Z.add_assoc -Z.add_le_mono_l Z.max_r.
    cut (exists2 m2, write m1 (top_stack m' + wrepr Uptr ofs)%R v = ok m2 & match_mem m m2).
    - case => m2 ok_m2 M2; exists m2; split; [ exact: ok_m2 | | exact: M2 ].
      move => a [] a_lo a_hi _.
      rewrite (write_read8 ok_m2) /=.
      case: andP; last by [].
      case => _ /ltzP a_below; exfalso.
      move: a_below.
      rewrite subE wunsigned_add -/(wunsigned (_ + _)) wunsigned_add //; first lia.
      split; last by generalize (wunsigned_range a); lia.
      have := wsize_size_pos ws; lia.
    apply: mm_write_invalid; first exact: M; last first.
    - apply: is_align_add ofs_aligned.
      apply: is_align_m; first exact: frame_aligned.
      rewrite (alloc_stack_top_stack ok_m').
      exact: do_align_is_align.
    rewrite wunsigned_add; last exact: ofs_no_overflow.
    split; last exact: ofs_below.
    apply: Z.le_trans; first exact: proj1 (ass_above_limit A).
    lia.
  Qed.

  Lemma pword_uincl ws (w: word ws) (z: pword ws) :
    word_uincl w z.(pw_word) →
    z = pword_of_word w.
  Proof.
    case: z => ws' w' ws'_le_ws /= /andP[] ws_le_ws' /eqP ->{w}.
    have ? := cmp_le_antisym ws'_le_ws ws_le_ws'.
    subst ws'.
    by rewrite pword_of_wordE zero_extend_u.
  Qed.

  Lemma check_to_save_slotP x ofs ofs' ws :
    check_to_save_slot liparams p (x, ofs) = ok (ofs', ws)
    -> let: xi := {| v_var := x; v_info := dummy_var_info; |} in
       let: xg := {| gv := xi; gs := Slocal; |} in
       exists xname,
         [/\ x = {| vtype := sword ws; vname := xname; |}
           , isSome (lload liparams xi ws vrspi ofs)
           , isSome (lstore liparams vrspi ofs ws xg)
           & ofs = ofs'
         ].
  Proof.
    rewrite /check_to_save_slot /=.
    move: x => [[|||ws'] xname] //=.
    t_xrbindP=> /andP [hlload hlstore] ? ?; subst ofs' ws'.
    by eexists.
  Qed.

  Lemma read_after_spill top al vm m1 to_spill m2 lo hi :
    (wunsigned top + hi < wbase Uptr)%Z →
    (0 <= lo)%Z →
    all_disjoint_aligned_between
      lo
      hi
      al
      to_spill
      (check_to_save_slot liparams p)
    = ok tt →
    foldM (λ '(x, ofs) m,
           Let: ws := if vtype x is sword ws then ok ws else Error ErrType in
           Let: v := get_var vm x >>= to_word ws in
           write m (top + wrepr Uptr ofs)%R v)
          m1 to_spill = ok m2 →
    [/\
     ∀ ofs ws, ((0 <= ofs)%Z /\ (ofs + wsize_size ws <= lo)%Z) \/ (hi <= ofs /\ wunsigned top + ofs + wsize_size ws <= wbase Uptr)%Z → read m2 (top + wrepr Uptr ofs)%R ws = read m1 (top + wrepr Uptr ofs)%R ws
     & 
     ∀ x ofs, (x, ofs) \in to_spill → exists2 ws, is_word_type x.(vtype) = Some ws & exists2 v, get_var vm x >>= to_word ws = ok v & read m2 (top + wrepr Uptr ofs)%R ws = ok v
    ].
  Proof.
    move => no_overflow.
    elim: to_spill m1 lo.
    - by move => _ lo _ _ [->].
    case => - [] xt x ofs to_spill ih m0 lo lo_pos /all_disjoint_aligned_betweenP[] y [] ws [] /=.
    move=> /check_to_save_slotP /= [xname [[? ?] _ _ ?]]; subst x xt y.
    move=> lo_le_ofs ws_aligned ofs_aligned ok_to_spill.
    have ofs_below_hi := all_disjoint_aligned_between_range ok_to_spill.
    t_xrbindP => m1 _ <- w v ok_v ok_w ok_m1 rec.
    have ws_pos := wsize_size_pos ws.
    have lo'_pos : (0 <= ofs + wsize_size ws)%Z by lia.
    have {ih} [ih1 ih2] := ih _ _ lo'_pos ok_to_spill rec.
    split.
    - move => ofs' ws' hofs'.
      rewrite ih1; last lia.
      have n_pos := wsize_size_pos ws.
      have n_pos' := wsize_size_pos ws'.
      have [top_lo _] := wunsigned_range top.
      rewrite (writeP_neq ok_m1) //; split.
      1-2: rewrite !zify !wunsigned_add; lia. 
      rewrite !wunsigned_add; lia.
    move => y ofs_y; rewrite inE; case: eqP.
    - case => ->{y} ->{ofs_y} _ /=.
      eexists; first reflexivity.
      exists w; first by rewrite ok_v.
      rewrite ih1; first by exact: (writeP_eq ok_m1). 
      lia.
    by move => _ /ih2.
  Qed.

  Lemma Sv_diff_empty (s: Sv.t) :
    Sv.Equal (Sv.diff s Sv.empty) s.
  Proof. SvD.fsetdec. Qed.

  Lemma wf_vm_eval_uincl_pundef vm z:
    wf_vm vm -> eval_uincl (pundef_addr (vtype z)) (vm.[z])%vmap.
  Proof.
    move=> /(_ z); case: (vm.[z])%vmap => //.
    + by move=> ??; apply eval_uincl_undef.
    by case => //; case: vtype.
  Qed.

  Lemma eval_uincl_kill_vars_incl X1 X2 vm1 vm2 z:
    wf_vm vm2 ->
    Sv.Subset X1 X2 ->
    (eval_uincl (kill_vars X1 vm1).[z] vm2.[z] ->
     eval_uincl (kill_vars X2 vm1).[z] vm2.[z])%vmap.
  Proof.
    move=> hwf S;
    rewrite !kill_varsE; case:Sv_memP => hin1; case: Sv_memP => hin2 // _; first by SvD.fsetdec.
    by apply wf_vm_eval_uincl_pundef.
  Qed.

  Lemma vm_uincl_kill_vars_set_incl X1 X2 vm1 vm2 x v1 v2:
    wf_vm vm2 ->
    Sv.Subset X1 X2 ->
    eval_uincl v2 v1 ->
    vm_uincl ((kill_vars X1 vm1).[x <- v1])%vmap vm2 ->
    vm_uincl ((kill_vars X2 vm1).[x <- v2])%vmap vm2.
  Proof.
    move=> hwf S huv huvm z.
    case: (x =P z) (huvm z) => [<- | /eqP ?].
    + by rewrite !Fv.setP_eq; apply: (eval_uincl_trans huv).
    by rewrite !Fv.setP_neq //; apply eval_uincl_kill_vars_incl.
  Qed.

  Lemma vm_uincl_after_alloc_stack fd m m' vm0 vm1 vm2 :
    let: ts := top_stack m in
    let: sf_sz := (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z in
    let: al := sf_align (f_extra fd) in
    let: ts' := align_word al (ts - wrepr Uptr sf_sz) in
    let: vm3 :=
      (kill_vars (Sv.singleton var_tmp) vm0).[vrsp <- ok (pword_of_word ts)]%vmap
    in
    wf_vm vm2
    -> vm_uincl vm3 vm1
    -> sf_return_address (f_extra fd) = RAnone
    -> let: ssr := savedstackreg (sf_save_stack (f_extra fd)) in
       vm2 = vm1 [\ Sv.union ssr (Sv.add var_tmp (Sv.add vrsp vflags)) ]
    -> get_var vm2 vrsp = ok (Vword ts')
    -> alloc_stack
         m
         al
         (sf_stk_sz (f_extra fd)) 
         (sf_stk_ioff (f_extra fd))
         (sf_stk_extra_sz (f_extra fd))
       = ok m'
    -> vm_uincl (set_RSP p m' (kill_vars (ra_undef fd var_tmp) vm0)) vm2.
  Proof.
    move=> hwfvm2 hvm3 hra hvm2 hgetrsp halloc z.
    set vm4 := kill_vars _ _.
    have := hvm3 z.
    clear hvm3.
    rewrite /set_RSP -/vrspi.
    case: (vrsp =P z) => [<- | hne].

    - t_vm_get.
      move: hgetrsp.
      rewrite /get_var /=.
      case: vm2.[_]%vmap => [|[]] // [???] /=.
      move=> /ok_inj /Vword_inj [?]; subst.
      move=> /= -> _.
      rewrite pword_of_wordE.
      rewrite (alloc_stack_top_stack halloc) /top_stack_after_alloc.
      by rewrite wrepr_opp.

    t_vm_get.
    rewrite !kill_varsE.
    case: (Sv_memP _ (ra_undef _ _)).
    - move=> _ _. by apply: wf_vm_eval_uincl_pundef.

    rewrite /ra_undef /ra_vm hra {hra} /=.
    move=> hnin.
    case: Sv_memP => [? | _]; first by SvD.fsetdec.
    rewrite hvm2 {hvm2}; first done.

    move: hnin.
    rewrite /saved_stack_vm /savedstackreg /=.
    case: sf_save_stack => [| r | ofs] hnin.
    all: rewrite SvP.MP.add_union_singleton || rewrite Sv_union_empty.
    all: repeat (move=> /Sv.add_spec [|] /=; first SvD.fsetdec).
    all: SvD.fsetdec.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p extra_free_registers var_tmp Pc Pfun.
  Proof.
    red => ii k s1 _ fn fd args m1' s2' res ok_fd free_ra ok_ss rsp_aligned valid_rsp ok_m1' ok_args wt_args exec_body ih ok_res wt_res valid_rsp' -> m1 vm1 _ ra lret sp callee_saved W M X [] fd' ok_fd' <- [].
    rewrite ok_fd => _ /Some_inj <- ?; subst ra.
    rewrite /value_of_ra => ok_lret.
    case; rewrite ok_fd => _ /Some_inj <- /= ok_sp.
    case; rewrite ok_fd => _ /Some_inj <- /= ok_callee_saved.
    move: (checked_prog ok_fd); rewrite /check_fd /=.
    t_xrbindP => chk_body ok_to_save ok_stk_sz ok_ret_addr ok_save_stack _.
    have ? : fd' = (linear_fd fn fd).2.
    - have := get_fundef_p' ok_fd.
      by rewrite ok_fd' => /Some_inj.
    subst fd'.
    move: ok_fd'; rewrite /linear_fd /linear_body /=.
    rewrite /ra_valid in free_ra.
    rewrite /check_to_save in ok_to_save.
    rewrite /ra_undef_vm in exec_body.
    rewrite /ra_undef_vm in ih.
    rewrite /saved_stack_valid in ok_ss.
    rewrite /ra_vm.
    rewrite /saved_stack_vm.
    case EQ: sf_return_address free_ra ok_to_save ok_callee_saved ok_save_stack ok_ret_addr X ok_lret exec_body ih ok_sp
 =>
      /= [ | ra | ora rastack ] free_ra ok_to_save ok_callee_saved ok_save_stack ok_ret_addr X ok_lret exec_body ih.
    2-3: case => sp_aligned.
    all: move => ?; subst sp.
    - (* Export function *)
    { case: lret ok_lret => // _.
      subst callee_saved.
      case E1: sf_save_stack ok_save_stack ok_ss ok_to_save exec_body ih =>
      [ | saved_rsp | stack_saved_rsp ] /= ok_save_stack ok_ss ok_to_save exec_body ih ok_fd' wf_to_save.
      + (* No need to save RSP *)
      { have {ih} := ih fn xH.
        rewrite /checked_c ok_fd chk_body => /(_ erefl).
        case: (linear_c fn) ok_fd' => lbl lbody /= ok_fd' E.
        have ok_body : is_linear_of fn (lbody ++ [::]).
        + by rewrite /is_linear_of cats0 ok_fd' /=; eexists; reflexivity.
        have M' := mm_alloc M ok_m1'.
        case/and4P: ok_save_stack => /eqP to_save_nil /eqP sf_align_1 /eqP stk_sz_0 /eqP stk_extra_sz_0.
        have top_stack_preserved : top_stack m1' = top_stack (s1: mem).
        + rewrite (alloc_stack_top_stack ok_m1') sf_align_1.
          rewrite top_stack_after_aligned_alloc.
          2: exact: is_align8.
          by rewrite stk_sz_0 stk_extra_sz_0 -addE add_0.

        have X' :
          vm_uincl (set_RSP p m1' (kill_vars (ra_undef fd var_tmp) s1)) vm1.
        + apply: vm_uincl_kill_vars_set_incl X => //.
          + by rewrite /ra_undef /ra_vm EQ /=; clear; SvD.fsetdec.
          by rewrite top_stack_preserved.

        have {E} [m2 vm2] := E m1 vm1 [::] [::] W M' X' (λ _ _, erefl) ok_body.
        rewrite /= => E K2 W2 X2 H2 M2.
        eexists m2 _; [ exact: E | | exact: W2 | | | exact: mm_free M2 ]; cycle 2.
        + move => a a_range /negbTE nv.
          have A := alloc_stackP ok_m1'.
          have [L] := ass_above_limit A.
          rewrite stk_sz_0 => H.
          apply: H2.
          * rewrite (ass_root A); lia.
          rewrite (ass_valid A) nv /= !zify => - [].
          change (wsize_size U8) with 1%Z.
          rewrite (ass_add_ioff A).
          have := ass_ioff A.
          move: (sf_stk_sz _) (sf_stk_extra_sz _) (sf_stk_ioff _) stk_sz_0 stk_extra_sz_0 H.
          lia.
        + apply: vmap_eq_exceptI; last exact: K2.
          rewrite to_save_nil Sv_diff_empty.
          exact: Sv_Subset_union_left.
        have S : stack_stable m1' s2'.
        + exact: sem_one_varmap_facts.sem_stack_stable exec_body.
        move => x; move: (X2 x); rewrite /set_RSP !Fv.setP; case: eqP => // ?; subst.
        by rewrite valid_rsp' -(ss_top_stack S) top_stack_preserved.
      }
      + (* RSP is saved into register “saved_rsp” *)
      { have {ih} := ih fn xH.
        rewrite /checked_c ok_fd chk_body => /(_ erefl).
        move: ok_fd'.
        case: saved_rsp ok_save_stack ok_ss E1 exec_body => stty saved_stack /=.
        set ri := vid saved_stack.
        move=>
          /and5P[]
          /eqP ?
          /eqP to_save_empty
          hnot_saved_stack
          hset_up_sp
          hrestore_rsp;
          subst stty.
        move=>
          /and3P[]
          /eqP saved_stack_not_GD
          /eqP saved_stack_not_RSP
          /Sv_memP saved_stack_not_written.
        move => E1 exec_body.
        rewrite linear_c_nil.
        case: (linear_c fn) => lbl lbody /=.
        set P := (X in X ++ lbody ++ _).
        set Q := (X in lbody ++ X).
        move => ok_fd' E.
        have ok_body : is_linear_of fn (P ++ lbody ++ Q).
        + by rewrite /is_linear_of ok_fd' /=; eauto.
        have ok_rsp : get_var vm1 vrsp = ok (Vword (top_stack (emem s1))).
        + move: (X vrsp). rewrite Fv.setP_eq /get_var /=.
          by case: _.[_]%vmap => //= - [] sz w ? /pword_of_word_uincl[] /= ? -> {w}; subst.
        have [vm [hsem hwf_vm hvm hgetrsp hgetr hflags]] :=
          spec_lip_set_up_sp_register
            hliparams
            (P := [::])
            (s := Estate (escs s1) m1 vm1)
            ok_body
            hset_up_sp
            (erefl (vtype (vid _)))
            hneq_vtmp_vrsp
            hnot_saved_stack
            saved_stack_not_RSP
            ok_rsp
            W.

        have X' :
          vm_uincl (set_RSP p m1' (kill_vars (ra_undef fd var_tmp) s1)) vm.
        + apply: (vm_uincl_after_alloc_stack hwf_vm X EQ _ hgetrsp ok_m1').
          rewrite /= E1 /=.
          rewrite -SvP.MP.add_union_singleton.
          exact: hvm.

        have D : disjoint_labels 1 lbl P.
        + move => lbl' _.
          rewrite /P /=.
          by rewrite set_up_sp_register_has_label.

        move: E => /(_ m1 vm P Q hwf_vm (mm_alloc M ok_m1') X' D ok_body).
        case => m2 vm2.
        rewrite /= !size_cat /= addn1.
        move => E K2 W2 X2 H2 M2.

        eexists.
        - apply: (lsem_trans hsem).
          apply: lsem_step_end; first exact: E.

          (* Exectute R[rsp] := R[r]; *)
          + rewrite /lsem1 /step.
            move: (ok_body).
            replace (size P + size lbody) with (size (P ++ lbody) + 0);
              last by rewrite size_cat addn0.
            rewrite catA.
            move => /find_instr_skip ->.
            rewrite /=.

          set s := {| escs := escs s2'; emem := m2; evm := vm2; |}.
          set ts := @top_stack _ mem _ _ s1.

          have hgetrg :
            get_gvar [::] s (mk_lvar ri) = ok (Vword ts).
          + rewrite /get_gvar /= /get_var /=.
            rewrite -(K2 _ saved_stack_not_written) /=.
            rewrite -/(get_var vm ri).
            by rewrite hgetr.

          have hwrite :
            write_var vrspi (Vword ts) s
            = ok (with_vm s vm2.[vrspi <- ok (pword_of_word ts)]%vmap).
          - by rewrite -to_pword_u.

          rewrite (spec_lmove hliparams _ _ _ _ hrestore_rsp hgetrg hwrite) /=.
          clear hrestore_rsp hgetrg hwrite.
          rewrite /of_estate /=.
          rewrite addn0 !size_cat addnS /=.
          reflexivity.

        + rewrite to_save_empty Sv_diff_empty.
          clear - ok_rsp K2 hvm.
          move => x.
          rewrite !Sv.union_spec !Sv.add_spec Sv.singleton_spec Fv.setP =>
            /Decidable.not_or[] x_not_k /Decidable.not_or[] /Decidable.not_or[] x_not_tmp x_not_flags x_not_saved_stack.
          case: eqP => x_rsp.
          * subst; move: ok_rsp; rewrite /get_var.
            case: _.[_]%vmap; last by case.
            move => [] /= sz w hle /ok_inj /Vword_inj[] ?; subst => /= ->.
            by rewrite pword_of_wordE.
          rewrite -K2; last exact: x_not_k.
          rewrite hvm; first done.
          repeat (move=> /Sv.add_spec [] //).
          by apply: nesym.
        + exact: wf_vm_set.
        + move => x; rewrite Fv.setP; case: eqP => ?.
          * by subst; rewrite Fv.setP_eq.
          rewrite Fv.setP_neq; last by apply/eqP.
          rewrite /set_RSP Fv.setP_neq; last by apply/eqP.
          done.
        + move => a [] a_lo a_hi /negbTE nv.
          have A := alloc_stackP ok_m1'.
          have [L H] := ass_above_limit A.
          apply: H2.
          * rewrite (ass_root A).
            split; last exact: a_hi.
            etransitivity; last exact: a_lo.
            suff : (0 <= sf_stk_sz (f_extra fd))%Z by lia.
            by case/andP: ok_stk_sz => /lezP.
          rewrite (ass_valid A) nv /= !zify => - [].
          rewrite (ass_add_ioff A).
          change (wsize_size U8) with 1%Z.
          have := ass_ioff A.
          move: (sf_stk_sz _) (sf_stk_extra_sz _) (sf_stk_ioff _) H => ???.
          lia.
        exact: mm_free.
      }
      (* RSP is saved in stack at offset “stack_saved_rsp” *)
      { have {ih} := ih fn xH.
        rewrite /checked_c ok_fd chk_body => /(_ erefl).
        move: ok_fd'.
        rewrite (linear_c_nil).
        case: (linear_c fn) => lbl lbody /=.
        case/and3P: ok_stk_sz => /lezP stk_sz_pos /lezP stk_extra_pos /ltzP frame_noof.
        have sz_nz : (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd) == 0)%Z = false.
        + move: ok_save_stack; clear - stk_sz_pos stk_extra_pos; rewrite !zify => - [] [] C [] D _ _.
          apply/eqP.
          move: D; rewrite /stack_frame_allocation_size.
          have := wsize_size_pos (sf_align (f_extra fd)).
          move: (sf_stk_sz _) (sf_stk_extra_sz _) stk_sz_pos stk_extra_pos C => n m A B C.
          have : (0 <= n + m)%Z by lia.
          case: (n + m)%Z.
          2-3: move => ?; lia.
          move => _ _; assert (h := wsize_size_pos Uptr); lia.

        set cmd_set_up_sp := set_up_sp_stack _ _ _ _.
        set cmd_push_to_save := push_to_save _ _ _ _.
        set P := cmd_set_up_sp ++ cmd_push_to_save.
        set Q := (X in lbody ++ X).
        move => ok_fd' E.

        have ok_body :
          is_linear_of fn (cmd_set_up_sp ++ cmd_push_to_save ++ lbody ++ Q).
        + by rewrite catA /is_linear_of ok_fd' /=; eauto.

        have ok_rsp : get_var vm1 vrsp = ok (Vword (top_stack (emem s1))).
        + move: (X vrsp). rewrite Fv.setP_eq /get_var /=.
          by case: _.[_]%vmap => //= - [] sz w ? /pword_of_word_uincl[] /= ? -> {w}; subst.

        have A := alloc_stackP ok_m1'.
        have can_spill := mm_can_write_after_alloc _ ok_m1' stk_sz_pos stk_extra_pos.

        set top := (top_stack_after_alloc (top_stack (emem s1)) (sf_align (f_extra fd)) (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))).
        have topE : top_stack m1' = top.
        + by rewrite (alloc_stack_top_stack ok_m1').

        set ts := top_stack (emem s1).

        move: ok_to_save; t_xrbindP => /ZleP hle_rsp ok_to_save.

        move: ok_save_stack => /and4P [h tmp_not_saved hset_up_sp hrestore_rsp].
        move: h =>
          /and4P []
          /lezP rsp_slot_lo
          /lezP rsp_slot_hi
          aligned_frame
          rsp_slot_aligned.

        have [m2 [ok_m2 H2 M2]] :=
          can_spill
            _ _ _
            ts
            aligned_frame
            rsp_slot_aligned
            rsp_slot_lo
            rsp_slot_hi
            M.

        move: ok_m2.
        rewrite topE /top.
        rewrite /top_stack_after_alloc wrepr_opp /=.
        rewrite -/ts.
        move=> ok_m2.

        have [vm2 [hsem hwf_vm2 hvm2 hgetrsp hflags]] :=
          spec_lip_set_up_sp_stack
            (s := {| escs:= escs s1; evm := vm1; emem := m1; |})
            (P := [::])
            hliparams
            ok_body
            hset_up_sp
            hneq_vtmp_vrsp
            ok_rsp
            W
            ok_m2.

        have X' :
          vm_uincl (set_RSP p m1' (kill_vars (ra_undef fd var_tmp) s1)) vm2.
        + apply: (vm_uincl_after_alloc_stack hwf_vm2 X EQ _ hgetrsp ok_m1').
          rewrite /savedstackreg E1.
          rewrite Sv_union_empty.
          exact: hvm2.

        have D : disjoint_labels 1 lbl P.
        + move => lbl' _.
          rewrite /P has_cat /=.
          rewrite set_up_sp_stack_has_label /=.
          exact: push_to_save_has_no_label.

        have is_ok_vm1_vm2 :
          forall x,
            Sv.mem x (sv_of_list fst (sf_to_save (f_extra fd)))
            -> is_ok (get_var vm1 x >>= of_val (vtype x))
            -> is_ok (get_var vm2 x >>= of_val (vtype x)).
        + move=> x hx ok_x.
          case: (SvP.MP.In_dec x (Sv.add var_tmp (Sv.add vrsp vflags))) => hin.
          {
            move: hin => /Sv.add_spec [? | hin].
            - subst x. by move: tmp_not_saved => /negP.
            move: hin => /Sv.add_spec [? | hin].
            - subst x. rewrite hgetrsp /=. by rewrite truncate_word_u.
            rewrite /get_var.
            have := hflags _ hin.
            case: vm2.[x]%vmap.
            - have := vflagsP hin. by case: (x) => /= _ ? ->.
            by move=> _ <- //.
          }

          rewrite /get_var.
          by rewrite (hvm2 _ hin).

        have :
          ∃ m3,
            let: ls :=
              {|
                lscs := escs s1;
                lmem := m2;
                lvm := vm2;
                lfn := fn;
                lpc := size cmd_set_up_sp;
              |}
            in
            let ls' :=
              {|
                lscs := escs s1;
                lmem := m3;
                lvm := vm2;
                lfn := fn;
                lpc := size P;
              |}
            in
            [/\ foldM (λ '(x, ofs) m,
                        Let: ws := if vtype x is sword ws then ok ws else Error ErrType in
                        Let: v := get_var vm2 x >>= to_word ws in
                        write m (top + wrepr Uptr ofs)%R v) m2 (sf_to_save (f_extra fd)) = ok m3,
                 preserved_metadata s1 m2 m3,
                 match_mem s1 m3 &
                 lsem p' ls ls'
                ].
        + {
          clear hsem ok_m2.
          move: ok_body.
          rewrite /P /=.
          rewrite size_cat /=.
          move: (lbody ++ Q) => suffix.
          move: (cmd_set_up_sp).
          have : (sf_stk_sz (f_extra fd) <= sf_stk_sz (f_extra fd))%Z by lia.
          move: wf_to_save ok_to_save m2 H2 M2 tmp_not_saved is_ok_vm1_vm2.
          rewrite /cmd_push_to_save.
          elim: (sf_to_save (f_extra fd)) {-2}(sf_stk_sz (f_extra fd))
              => [ sz' _ _ | [x ofs] to_save ih lo /= wf_to_save ok_to_save ]
                 m2
                 H2
                 M2
                 tmp_not_saved
                 is_ok_vm1_vm2
                 sz'_le_lo prefix
                 ok_body.
          *  exists m2; split => //. rewrite addn0. exact: rt_refl.
          case/andP: wf_to_save => wf_x wf_to_save.
          case/all_disjoint_aligned_betweenP: ok_to_save => x_ofs [] ws [].
          move=> /check_to_save_slotP [xname [? _ hlstorex ?]]; subst x x_ofs.
          set x := {| vname := xname; |}.
          move=> lo_ofs ok_ws aligned_ofs ok_to_save.
          move: ih => /(_ _ wf_to_save ok_to_save) ih.

          have :
            is_ok (Let x := get_var vm2 x in to_word ws x).
          - apply: (is_ok_vm1_vm2 _ _ wf_x). exact: sv_of_list_mem_head.

          case get_x: get_var => [ v | // ].
          rewrite /=.
          case ok_w: to_word => [ w | // ] _ /=.
          have := can_spill _ ofs _ w ok_ws aligned_ofs _ _ M2.
          case.
          * etransitivity; last exact: lo_ofs.
            etransitivity; last exact: sz'_le_lo.
            assert (h := wsize_size_pos Uptr).
            move: (sf_stk_sz _) => ?; lia.
          * have := all_disjoint_aligned_between_range ok_to_save. 
            move: hle_rsp. assert (H := wsize_size_pos Uptr).
            move: (sf_stk_sz _) (sf_stk_extra_sz _) => ?; lia.
          rewrite topE => acc [] ok_acc Hacc ACC.
          have : preserved_metadata s1 m1 acc.
          * transitivity m2; assumption.
          move: ih => /(_ _ _ ACC) ih /ih {} ih.
          have : (sf_stk_sz (f_extra fd) <= ofs + wsize_size ws)%Z.
          * move: (sf_stk_sz _) sz'_le_lo lo_ofs (wsize_size_pos ws) => /=; lia.

          move => /ih {} ih.
          move: (ok_body).
          rewrite -cat_rcons.
          move=> /ih{ih} [].

          - move: tmp_not_saved.
            rewrite !sv_of_listE -/x.
            rewrite notin_cons.
            by move=> /andP [].

          - move=> z hz.
            apply: is_ok_vm1_vm2.
            by apply: sv_of_list_mem_tail.

          move=> m3 [] ok_m3 H3 M3.
          rewrite size_rcons => exec.
          exists m3; split.
          * rewrite ok_acc; exact: ok_m3.
          * transitivity acc; assumption.
          * exact: M3.
          rewrite -addn1 -(addnC 1) addnA addn1.
          apply: lsem_step; last exact: exec.
          rewrite /lsem1 /step.
          rewrite -{1}(addn0 (size prefix)) (find_instr_skip ok_body).
          move /to_wordI' : ok_w => [ws' [w' [hle ??]]]; subst v w => /=.
          rewrite /lstore.
          apply:
            (spec_lassign
               (s1 := {| emem := _; evm := _; |})
               (s2 := {| emem := _; evm := _; |})
               (w' := w')
               hliparams
               p') => //.
          + by rewrite /truncate_word hle.
          rewrite /= hgetrsp /=.
          rewrite !truncate_word_u /=.
          rewrite -wrepr_opp.
          by rewrite ok_acc.
        }
        case => m3 [] ok_m3 H3 M3' exec_save_to_stack.
        have M3 : match_mem m1' m3 := mm_alloc M3' ok_m1'.
        rewrite catA in ok_body.
        move: E => /(_ m3 vm2 P Q hwf_vm2 M3 X' D ok_body).
        case => m4 vm4 E K4 W4 X4 H4 M4.
        have vm4_get_rsp : get_var vm4 vrsp >>= to_pointer = ok top.
        + rewrite /get_var /= -K4.
          * rewrite -/(get_var vm2 vrsp) hgetrsp /=.
+            by rewrite truncate_word_u -wrepr_opp.
          have /disjointP K := sem_RSP_GD_not_written var_tmp_not_magic exec_body.
          move => /K; apply; exact: RSP_in_magic.
        have top_no_overflow1 : (wunsigned top + stack_saved_rsp + wsize_size Uptr < wbase Uptr)%Z. 
        + apply: Z.le_lt_trans; last exact: proj2 (wunsigned_range (top_stack (emem s1))).
          etransitivity; last exact: (proj2 A.(ass_above_limit)).
          rewrite topE; assert (h :=  wsize_size_pos Uptr). 
          move: (sf_stk_sz _) (sf_stk_extra_sz _) hle_rsp => ?; lia.
        have top_no_overflow : (wunsigned top + stack_saved_rsp < wbase Uptr)%Z. 
        + assert (h := wsize_size_pos Uptr); lia.
        have rsp_slot_pos : (0 <= stack_saved_rsp + wsize_size Uptr)%Z.
        + assert (h := wsize_size_pos Uptr); lia.
        have [read_in_m3 read_spilled] := read_after_spill top_no_overflow stk_sz_pos ok_to_save ok_m3.
        have read_saved_rsp : read m4 (top + wrepr Uptr stack_saved_rsp)%R Uptr = ok (top_stack (emem s1)).
        + rewrite -(@eq_read _ _ _ _ m3); last first.
          * move => i i_range.
            have rsp_range := stack_slot_in_bounds ok_m1' stk_sz_pos stk_extra_pos rsp_slot_lo rsp_slot_hi i_range.
            apply: (preserved_metadata_w ok_m1') => //.
            - rewrite -topE; move: (sf_stk_sz _) stk_sz_pos rsp_range; lia.
            rewrite A.(ass_valid).
            apply/orP => - [].
            - move => /(ass_fresh_alt A); apply.
              rewrite !zify -topE; move: (sf_stk_sz _) stk_sz_pos rsp_range; lia.
            rewrite !zify -topE.
            have [_] := A.(ass_above_limit).
            rewrite Z.max_r //.
            change (wsize_size U8) with 1%Z.
            rewrite (ass_add_ioff A). have := ass_ioff A.
            move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _)  stk_sz_pos stk_extra_pos rsp_range =>
              n ioff n' n_pos n'_pos rsp_range hioff h [] _.
            lia.
          rewrite read_in_m3; last lia.
          rewrite -wrepr_opp in ok_m2.
          by rewrite (writeP_eq ok_m2).

        have :
          let: tail := pop_to_save liparams p dummy_instr_info (sf_to_save (f_extra fd)) in
          exists vm5,
            [/\
               lsem
                 p'
                 {| lscs := escs s2';
                   lmem := m4;
                   lvm := vm4;
                   lfn := fn;
                   lpc := size (P ++ lbody);
                 |}
                 {| lscs := escs s2';
                   lmem := m4;
                   lvm := vm5;
                   lfn := fn;
                   lpc := size (P ++ lbody ++ tail)
                 |},
             wf_vm vm5
             & forall x,
                  vm5.[x] = if x \in (map fst (sf_to_save (f_extra fd)))
                            then vm2.[x]
                            else vm4.[x]
            ]%vmap.
        {
          clear E K4 X4.
          move: ok_body ok_to_save wf_to_save read_spilled.
          rewrite !catA.
          move: [:: _] => suffix.
          move: (P ++ lbody).
          have : (sf_stk_sz (f_extra fd) <= sf_stk_sz (f_extra fd))%Z by lia.
          move: is_ok_vm1_vm2.
          elim: (sf_to_save _) {-1} (sf_stk_sz (f_extra fd))%Z vm4 W4 vm4_get_rsp
          => [ | [ x ofs ] to_save ih ] lo vm4 W4 vm4_get_rsp is_ok_vm1_vm2 sz'_le_lo prefix ok_body /all_disjoint_aligned_betweenP ok_to_save wf_to_save read_spilled.
          * exists vm4; split => //.
            rewrite cats0; exact: rt_refl.
          case: ok_to_save => x_ofs [] ws [].
          move=> /check_to_save_slotP [xname [? hlload _ ?]]; subst x x_ofs.
          set x := {| vname := xname; vtype := sword ws; |}.
          move => lo_ofs ok_ws aligned_ofs ok_to_save.
          move: wf_to_save; rewrite /vm_initialized_on /=.
          case/andP => /is_ok_vm1_vm2.
          move=> get_x wf_to_save.
          have : is_ok (Let x := get_var vm2 x in of_val (sword ws) x).
          - apply: get_x. exact: sv_of_list_mem_head.

          case ok_x: get_var => [ v | // ] /=.
          case ok_v: to_word => [ w | // ] _.
          set vm5 := vm4.[x <- ok (pword_of_word w)]%vmap.
          have W5: wf_vm vm5.
          * exact: wf_vm_set W4.
          have vm5_get_rsp : get_var vm5 vrsp >>= to_pointer = ok top.
          * case: (vrsp =P x) => x_rsp;
              last by rewrite /get_var Fv.setP_neq ?vm4_get_rsp //; apply/eqP => ?; exact: x_rsp.
            have ? : ws = Uptr by case: x_rsp.
            subst.
            rewrite x_rsp /get_var Fv.setP_eq /= truncate_word_u.
            move: ok_x ok_v.
            rewrite -/x -x_rsp hgetrsp.
            move=> /ok_inj <- /=.
            by rewrite truncate_word_u -wrepr_opp.
          move: ih => /(_ _ _ W5 vm5_get_rsp) ih.
          move: (ok_body).
          rewrite -cat_rcons => /ih {} ih.
          have : (sf_stk_sz (f_extra fd) <= ofs + wsize_size ws)%Z. 
          * etransitivity; first exact: sz'_le_lo.
            clear -lo_ofs.
            have := wsize_size_pos ws.
            lia.

          move => {} /ih /(_ ok_to_save wf_to_save) [].

          * move=> z hz.
            apply: is_ok_vm1_vm2.
            by apply: sv_of_list_mem_tail.

          * move => x' ofs' saved'; apply: read_spilled.
            by rewrite inE saved' orbT.

          move => vm6 [] E W6 X6.
          exists vm6; split.
          * apply: lsem_step; last exact: E.
            rewrite /lsem1 /step.
            move: ok_body.
            rewrite -{1}(addn0 (size prefix)) -catA => /find_instr_skip -> /=.
            rewrite /lload.
            rewrite size_rcons.
            apply:
              (spec_lassign
                 (s1 := {| emem := _; evm := _; |})
                 (s2 := {| emem := _; evm := _; |})
                 hliparams
                 p' _ _ _
                 hlload).
            + rewrite /= vm4_get_rsp truncate_word_u /=.
              have :
                read m4 (top + wrepr Uptr ofs)%R ws
                = get_var vm2 x >>= to_word ws.
              * rewrite -(@eq_read _ _ _ _ m3); last first.
                - move=> i i_range.
                  have ofs_lo : (sf_stk_sz (f_extra fd) <= ofs)%Z.
                  + move: (sf_stk_sz _) sz'_le_lo lo_ofs => n.
                    assert (h := wsize_size_pos Uptr).
                    lia.
                  have ofs_hi : (ofs + wsize_size ws <= sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))%Z.
                  + have := all_disjoint_aligned_between_range ok_to_save. 
                    assert (h := wsize_size_pos Uptr). 
                    move: (sf_stk_sz _) (sf_stk_extra_sz _) hle_rsp; lia.
                  have rsp_range := stack_slot_in_bounds ok_m1' stk_sz_pos stk_extra_pos ofs_lo ofs_hi i_range.
                  apply: (preserved_metadata_w ok_m1') => //.
                  - rewrite -topE; move: (sf_stk_sz _) stk_sz_pos rsp_range; lia.
                  rewrite A.(ass_valid).
                  apply/orP => - [].
                  - move => /(ass_fresh_alt A); apply.
                    rewrite !zify -topE; move: (sf_stk_sz _) stk_sz_pos rsp_range; lia.
                  rewrite !zify -topE.
                  have [_] := A.(ass_above_limit).
                  rewrite Z.max_r //.
                  change (wsize_size U8) with 1%Z.
                  rewrite (ass_add_ioff A).
                  move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _) (ass_ioff A) stk_sz_pos stk_extra_pos rsp_range => n ioff n' hioff n_pos n'_pos rsp_range h [] _.
                  lia.
                move: read_spilled => /(_ x ofs).
                by rewrite inE eqxx => /(_ erefl) [] _ /Some_inj <- [] w' ->.
              move => ->.
              by rewrite ok_x /= ok_v.
            + by rewrite truncate_word_u.
            by rewrite /= /write_var /= sumbool_of_boolET.
          * exact: W6.
          move => z; move: (X6 z).
          rewrite inE.
          case: ifP => z_to_save ->; first by rewrite orbT.
          case: eqP => /= z_x; last by rewrite Fv.setP_neq //; apply/eqP => ?; exact: z_x.
          rewrite z_x Fv.setP_eq.
          move: ok_v.
          apply: on_vuP ok_x => // /= w' -> <- /to_word_to_pword <-.
          clear.
          by case: w' => /= ws' w le; rewrite sumbool_of_boolET.
        }
        case => vm5 [] exec_restore_from_stack wf_vm5 ok_vm5.
        have vm5_get_rsp : get_var vm5 {| vtype := sword Uptr; vname := sp_rsp (p_extra p) |} >>= to_pointer = ok top.
        + rewrite /get_var /= ok_vm5.
          case: ifP => _; last rewrite -K4.

          1-2: rewrite -/(get_var vm2 vrsp) hgetrsp.
          1-2: by rewrite -wrepr_opp /= truncate_word_u.

          have /disjointP K := sem_RSP_GD_not_written var_tmp_not_magic exec_body.
          move => /K; apply; exact: RSP_in_magic.

        eexists.
        + apply: (lsem_trans hsem).
          rewrite add0n.
          apply: (lsem_trans exec_save_to_stack).
          apply: (lsem_trans E).
          apply: (lsem_trans exec_restore_from_stack).

          apply: LSem_step.
          rewrite /lsem1 /step -(addn0 (size _)).
          rewrite !catA in ok_body.
          move/find_instr_skip: ok_body; rewrite -catA => -> /=.
          rewrite /lload.
          rewrite !size_cat /= addn0 addn1 !addnS !addnA.
          apply:
            (spec_lassign
               (s1 := {| emem :=_; evm := _; |})
               (s2 := {| emem :=_; evm := _; |})
               hliparams
               p'
               _ _ _
               hrestore_rsp
            ).
          * rewrite /= vm5_get_rsp /= truncate_word_u /=.
            by rewrite read_saved_rsp /=.
          * by rewrite truncate_word_u.
          by rewrite /= /write_var /= sumbool_of_boolET.

        + move => x /Sv_memP H.
          rewrite Fv.setP; case: eqP => x_rsp.
          * move: (X x); subst; rewrite Fv.setP_eq.
            by case: _.[_]%vmap => //= ? /pword_uincl ->.
          move: H.
          rewrite SvP.diff_mem negb_and => /orP[]; last first.
          * move/negbNE/Sv_memP/sv_of_listP; rewrite map_id /= => hx.
            have /eqP {} x_rsp := x_rsp.
            rewrite ok_vm5 hx hvm2; first done.
            - move=> /Sv.add_spec => -[?|].
              + subst x.
                move: tmp_not_saved => /negP.
                apply.
                rewrite sv_of_listE.
                exact: hx.
              move=> /Sv.add_spec => -[?|].
              + subst. by move: x_rsp => /eqP.
              move=> /vflagsP hxty.
              case/in_map: hx => - [] y ofs K ?; subst y.
              elim: (sf_to_save _) K (m2) (m3) ok_m3 => //; move: hxty; clear => hxty.
              case => x' j m ih /= [].
              * by case => ??; subst; rewrite hxty.
              move => /ih{}ih m1 m3; t_xrbindP => m2 ws.
              case: vtype => // ws' /ok_inj ?; subst ws' => ?????; exact: ih.

          rewrite !SvP.union_mem Sv_mem_add SvP.empty_mem !orbA !orbF -!orbA.
          case/norP => x_ni_k /norP[] x_neq_tmp x_not_flag.
          transitivity vm2.[x]%vmap.
          + rewrite hvm2; first done.
            move=> /Sv.add_spec [?|].
            * subst x. by move: x_neq_tmp => /eqP.
            move=> /Sv.add_spec [?|].
            * by subst x.
            by apply/Sv_memP.

          transitivity vm4.[x]%vmap; first by rewrite K4 //; apply/Sv_memP.
          rewrite ok_vm5; case: ifP => // _.
          rewrite K4 //.
          exact/Sv_memP.
        + exact: wf_vm_set wf_vm5.
        + move => x; rewrite !Fv.setP; case: eqP => x_rsp; first by subst.
          move => /sv_of_listP; rewrite map_id => /negbTE x_not_to_save.
          apply: (eval_uincl_trans (X4 x)).
          by rewrite ok_vm5 x_not_to_save.
        + etransitivity; first exact: H2.
          etransitivity; first exact: H3.
          exact: preserved_metadata_alloc ok_m1' H4.
        exact: mm_free M4.
      }
    }
    - (* Internal function, return address in register “ra” *)
    { case: ra EQ ok_ret_addr X free_ra ok_lret exec_body ih => // -[] // ws // ra EQ ra_well_typed X /andP[] _ ra_notin_k.
      case: lret => // - [] [] [] caller lret cbody pc.
      case: (ws =P Uptr) => // E.
      subst ws.
      move=> [] ok_cbody ok_pc mem_lret [] retptr ok_retptr ok_ra exec_body ih.
      have {ih} := ih fn 2%positive.
      rewrite /checked_c ok_fd chk_body => /(_ erefl).
      rewrite (linear_c_nil _ _ _ _ _ [:: _ ]).
      case: (linear_c fn) (valid_c fn (f_body fd) 2%positive) => lbl lbody ok_lbl /= E.
      set P := (P in P :: lbody ++ _).
      set Q := (Q in P :: lbody ++ Q).
      move => ok_fd'.
      have ok_body : is_linear_of fn ([:: P ] ++ lbody ++ Q).
      + by rewrite /is_linear_of ok_fd'; eauto.
      have X1 : vm_uincl (set_RSP p m1' (kill_vars (ra_undef fd var_tmp) s1)) vm1.
      + apply: vm_uincl_kill_vars_set_incl X => //.
        + by rewrite /ra_undef /ra_vm EQ; SvD.fsetdec.
        rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc;  last by exact: sp_aligned.
        by rewrite wrepr_opp -/(stack_frame_allocation_size fd.(f_extra)).
      have D : disjoint_labels 2 lbl [:: P].
      + by move => q [A B]; rewrite /P /is_label /= orbF; apply/eqP => ?; subst; lia.
      have {E} [ m2 vm2 E K2 W2 ok_vm2 H2 M2 ] := E m1 vm1 [:: P] Q W (mm_alloc M ok_m1') X1 D ok_body.
      eexists; [ | | exact: W2 | | | exact: mm_free M2 ]; cycle 3.
      + move => a [] a_lo a_hi /negbTE nv.
        have A := alloc_stackP ok_m1'.
        have [L H] := ass_above_limit A.
        apply: H2.
        * rewrite (ass_root A).
          split; last exact: a_hi.
          etransitivity; last exact: a_lo.
          suff : (0 <= sf_stk_sz (f_extra fd))%Z by lia.
          by case/andP: ok_stk_sz => /lezP.
        rewrite (ass_valid A) nv /= !zify => - [].
        change (wsize_size U8) with 1%Z.
        rewrite (ass_add_ioff A).
        move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _) (ass_ioff A) H => *.
        lia.
      + apply: lsem_trans; first exact: E.
        apply: LSem_step.
        rewrite catA in ok_body.
        rewrite /lsem1 /step -(addn0 (size ([:: P] ++ lbody))) (find_instr_skip ok_body) /= /eval_instr /= /get_gvar /= /get_var /=.
        have ra_not_written : (vm2.[ Var spointer ra ] = vm1.[ Var spointer ra ])%vmap.
        * symmetry; apply: K2.
          have /andP [_ ?] := ra_notin_k.
          by apply/Sv_memP.
        rewrite ra_not_written ok_ra /= zero_extend_u truncate_word_u.
        have := decode_encode_label small_dom_p' mem_lret.
        rewrite ok_retptr /= => -> /=.
        case: ok_cbody => fd' -> -> /=; rewrite ok_pc /setcpc /=; reflexivity.
      + apply: vmap_eq_exceptI K2.
        apply: Sv_Subset_union_left.
        exact: SvP.MP.union_subset_1.
      move => ?; rewrite /set_RSP !Fv.setP; case: eqP => // ?; subst.
      move: (ok_vm2 vrsp).
      have S : stack_stable m1' s2'.
      + exact: sem_one_varmap_facts.sem_stack_stable exec_body.
      rewrite valid_rsp' -(ss_top_stack S) (alloc_stack_top_stack ok_m1').
      rewrite top_stack_after_aligned_alloc;
        last by exact: sp_aligned.
      by rewrite wrepr_opp.
    }
    (* Internal function, return address in stack at offset “rastack” *)
    { 
      case : ora EQ X free_ra ok_ret_addr ok_lret => [ra | ] /= EQ X free_ra ok_ret_addr ok_lret.
      (* Initially path by register and stored on top of the stack, like for ARM *)
      (* TODO : this case and the next one duplicate proof, we should do lemma *)
      + case: ra EQ X free_ra ok_ret_addr ok_lret => // -[] // ws ra EQ X free_ra ok_ret_addr ok_lret.
        case: lret ok_lret => // -[] [] [] caller lret cbody pc.
        case: eqP => // ?; subst ws => - [] ok_cbody ok_pc mem_lret [] retptr ok_retptr ok_ra1.
        have {ih} := ih fn 2%positive.
        rewrite /checked_c ok_fd chk_body => /(_ erefl).
        rewrite (linear_c_nil _ _ _ _ _ [:: _ ]).
        case: (linear_c fn) (valid_c fn (f_body fd) 2%positive) => lbl lbody ok_lbl /= E.
        set P1 := (P in P :: _ :: lbody ++ _).
        set P2 := (P in _ :: P :: lbody ++ _).
        set Q := (Q in P1 :: P2 :: lbody ++ Q).
        move => ok_fd'.
        have ok_body : is_linear_of fn ([:: P1; P2 ] ++ lbody ++ Q).
        + by rewrite /is_linear_of ok_fd'; eauto.
        have := X vrsp; rewrite Fv.setP_eq /=.
        case ok_rsp: (vm1.[_])%vmap => [ [ws rsp hle] | //] /= /andP /= [] h /eqP.
        have ? := cmp_le_antisym hle h; subst ws.
        rewrite pword_of_wordE in ok_rsp; rewrite zero_extend_u => eq_rsp {h hle}.
        case/and4P: ok_ret_addr => /andP [] _ is_store /eqP ? /eqP hioff sf_align_for_ptr; subst rastack.
        have spec_m1' := alloc_stackP ok_m1'.
        have is_align_m1' := ass_align_stk spec_m1'. 
        have ts_rsp : top_stack m1' = rsp.
        + rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc; last by exact: sp_aligned.
          by rewrite wrepr_opp -/(stack_frame_allocation_size fd.(f_extra)).
        have := ass_align_stk spec_m1'.
        (* TODO this should be a lemma it is used elsewhere (above)*)
        have [m1s ok_m1s M']: 
           exists2 m1s, write m1 rsp retptr = ok m1s & match_mem s1 m1s.
        + apply: mm_write_invalid; first exact: M; last first.
          * by rewrite -ts_rsp; apply: is_align_m sf_align_for_ptr is_align_m1'.
          have := (Memory.alloc_stackP ok_m1').(ass_above_limit).
          rewrite -ts_rsp (alloc_stack_top_stack ok_m1').
          rewrite top_stack_after_aligned_alloc // wrepr_opp.
          have := ass_ioff (alloc_stackP ok_m1'); rewrite -hioff.
          move: ok_stk_sz. clear.
          have := round_ws_range (sf_align (f_extra fd)) (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd)).
          rewrite !zify -/(stack_frame_allocation_size (f_extra fd)) => hround - [] sz_pos [] extra_pos sz_noof uptr_sz.
          set L := stack_limit (emem s1).
          have L_range := wunsigned_range L.
          move: (stack_frame_allocation_size _) hround sz_noof => S hround sz_noof.
          move: (top_stack (emem s1)) => T above_limit.
          have S_range : (0 <= S < wbase Uptr)%Z.
          - by move: ( sf_stk_sz (f_extra fd)) (sf_stk_extra_sz (f_extra fd)) sz_pos extra_pos hround; lia.
          have X : (wunsigned (T - wrepr Uptr S) <= wunsigned T)%Z.
          * move: (sf_stk_sz _) sz_pos above_limit => n; lia.
          have {X} TmS := wunsigned_sub_small S_range X.
          rewrite TmS in above_limit.
          lia.
        have X1 : vm_uincl (set_RSP p m1' (kill_vars (ra_undef fd var_tmp) s1)) vm1.
        + apply: vm_uincl_kill_vars_set_incl X => //. 
          + by rewrite /ra_undef /ra_vm EQ; SvD.fsetdec.
          by rewrite eq_rsp ts_rsp.
        have D : disjoint_labels 2 lbl [:: P1; P2].
        + move => q [A B]; rewrite /P1 /P2 /= is_label_lstore /is_label /= orbF; apply/eqP; lia.
        have {E} [ m2 vm2 E K2 W2 ok_vm2 H2 M2 ] := E m1s vm1 [:: P1; P2] Q W (mm_alloc M' ok_m1') X1 D ok_body.
        exists m2 (vm2.[vrsp <- ok
                          {|
                            pw_size := Uptr;
                            pw_word := rsp + wrepr Uptr (wsize_size Uptr);
                            pw_proof := (cmp_le_refl Uptr)
                          |}])%vmap; last exact: mm_free M2.
        + apply: lsem_step.
          + rewrite /lsem1 /step /= /find_instr /= ok_fd' /=.
            apply: (spec_lassign hliparams p' (s1 := {|escs:= escs s1; emem := m1; evm := vm1|}) _ _ _ is_store).
            + by rewrite /= /get_gvar /= get_varE ok_ra1 zero_extend_u /=.
            + by rewrite truncate_word_u.
            by rewrite /write_lval get_varE /= ok_rsp /= !truncate_word_u /= wrepr0 GRing.addr0 ok_m1s.
          apply: lsem_trans; first exact: E.
          apply: LSem_step.
          rewrite catA in ok_body.
          rewrite /lsem1 /step -(addn0 (size ([:: P1; P2] ++ lbody))) (find_instr_skip ok_body) /= /eval_instr /= /get_gvar /= /get_var /=.
          move: (ok_vm2 vrsp).
          rewrite -(sem_preserved_RSP_GD var_tmp_not_magic exec_body); last exact: RSP_in_magic.
          rewrite /= /set_RSP Fv.setP_eq /= lp_rspE -/vrsp.
          case: vm2.[_]%vmap => // - [] ?? pw_proof /pword_of_word_uincl /= [] ??; subst.
          rewrite (sumbool_of_boolET pw_proof) truncate_word_u /=.
          case/and3P: ok_stk_sz; rewrite !zify => stk_sz_pos stk_extra_pos sf_noovf.
          assert (root_range := wunsigned_range (stack_root m1')).
          have A := alloc_stackP ok_m1'.
          have top_range := ass_above_limit A.
          have top_stackE := wunsigned_top_stack_after_aligned_alloc stk_sz_pos stk_extra_pos sf_noovf sp_aligned ok_m1'.
          have sf_large : (wsize_size Uptr <= stack_frame_allocation_size (f_extra fd))%Z.
          - apply: Z.le_trans; last exact: proj1 (round_ws_range _ _).
            have := ass_ioff A.
            rewrite -hioff; move: (sf_stk_sz _) (sf_stk_extra_sz _) stk_sz_pos stk_extra_pos; lia.
          have rastack_no_overflow : (0 <= wunsigned (top_stack m1'))%Z ∧ (wunsigned (top_stack m1') +  wsize_size Uptr <= wunsigned (stack_root m1'))%Z.
          * assert (top_stack_range := wunsigned_range (top_stack m1')).
            assert (old_top_stack_range := wunsigned_range (top_stack (emem s1))).
            assert (h := wsize_size_pos Uptr).
                  split; first lia.
            rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc // wrepr_opp.
            rewrite -/(stack_frame_allocation_size _) wunsigned_sub; last first.
            - split; last lia.
              rewrite top_stackE; move: (stack_frame_allocation_size _) => n; lia.
            rewrite A.(ass_root).
            etransitivity; last exact: top_stack_below_root.
            rewrite -/(top_stack (emem s1)); lia.
          have -> : read m2 (top_stack m1')%R Uptr = read m1s (top_stack m1')%R Uptr.
          * apply: eq_read => i [] i_lo i_hi; symmetry; apply: H2.
            - rewrite addE wunsigned_add; lia.
            rewrite (Memory.alloc_stackP ok_m1').(ass_valid).
            apply/orP; case.
            - apply/negP; apply: stack_region_is_free.
              rewrite -/(top_stack _).
              move: (stack_frame_allocation_size _) top_stackE sf_large => n top_stackE sf_large.
              rewrite addE !wunsigned_add; lia.
            rewrite !zify (ass_add_ioff A) -hioff addE.
            rewrite wunsigned_add; lia.
          rewrite ts_rsp (writeP_eq ok_m1s) /=. 
          have := decode_encode_label small_dom_p' mem_lret.
          rewrite ok_retptr /= => -> /=.
          case: ok_cbody => fd' -> -> /=; rewrite ok_pc /setcpc /=.
          rewrite (Eqdep_dec.UIP_dec Bool.bool_dec pw_proof (cmp_le_refl Uptr)).
          reflexivity.
        + apply vmap_eq_exceptT with vm2.
          + by apply: vmap_eq_exceptI K2; SvD.fsetdec.
          by move=> ? hx; rewrite Fv.setP_neq //; apply/eqP; SvD.fsetdec.
        + by apply wf_vm_set.
        + by move => ?; rewrite /set_RSP !Fv.setP; case: eqP => // ?; subst.
        etransitivity. 
        + apply: (preserved_meta_store_top_stack ok_m1') => //.
          by rewrite top_stack_after_aligned_alloc // wrepr_opp eq_rsp; apply: ok_m1s.
        move => a [] a_lo a_hi /negbTE nv.
        have A := alloc_stackP ok_m1'.
        have [L R] := ass_above_limit A.
        apply: H2.
        * rewrite (ass_root A).
          split; last exact: a_hi.
          etransitivity; last exact: a_lo.
          suff : (0 <= sf_stk_sz (f_extra fd))%Z by lia.
          by case/andP: ok_stk_sz => /lezP.
        rewrite (ass_valid A) nv /= !zify => - [].
        change (wsize_size U8) with 1%Z.
        rewrite (ass_add_ioff A).
        move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _) (ass_ioff A) R; lia.
      (* Directly path on top of the stack *)
      case: lret ok_lret => // - [] [] [] caller lret cbody pc [] ok_cbody ok_pc mem_lret [] retptr ok_retptr [] rsp ok_rsp ok_ra.
      have := X vrsp.
      rewrite Fv.setP_eq ok_rsp => /andP[] _ /eqP /=.
      rewrite zero_extend_u => ?; subst rsp.
      have {ih} := ih fn 2%positive.
      rewrite /checked_c ok_fd chk_body => /(_ erefl).
      rewrite (linear_c_nil _ _ _ _ _ [:: _ ]).
      case: (linear_c fn) (valid_c fn (f_body fd) 2%positive) => lbl lbody ok_lbl /= E.
      set P := (P in P :: lbody ++ _).
      set Q := (Q in P :: lbody ++ Q).
      move => ok_fd'.
      have ok_body : is_linear_of fn ([:: P ] ++ lbody ++ Q).
      + by rewrite /is_linear_of ok_fd'; eauto.
      have X1 : vm_uincl (set_RSP p m1' (kill_vars (ra_undef fd var_tmp) s1)) vm1.
      + apply: vm_uincl_kill_vars_set_incl X => //.
        + by SvD.fsetdec.
        rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc;  last by exact: sp_aligned.
        by rewrite wrepr_opp -/(stack_frame_allocation_size fd.(f_extra)).
      have D : disjoint_labels 2 lbl [:: P].
      + by move => q [A B]; rewrite /P /is_label /= orbF; apply/eqP => ?; subst; lia.
      have {E} [ m2 vm2 E K2 W2 ok_vm2 H2 M2 ] := E m1 vm1 [:: P] Q W (mm_alloc M ok_m1') X1 D ok_body.
      exists m2 (vm2.[vrsp <- ok
                        {|
                          pw_size := Uptr;
                          pw_word := top_stack (emem s1) - wrepr Uptr (round_ws (sf_align (f_extra fd)) (sf_stk_sz (f_extra fd) + sf_stk_extra_sz (f_extra fd))) + wrepr Uptr (wsize_size Uptr);
                          pw_proof := (cmp_le_refl Uptr)
                        |}])%vmap; last exact: mm_free M2.
      + apply: lsem_trans; first exact: E.
        apply: LSem_step.
        rewrite catA in ok_body.
        rewrite /lsem1 /step -(addn0 (size ([:: P] ++ lbody))) (find_instr_skip ok_body) /= /eval_instr /= /get_gvar /= /get_var /=.
        move: (ok_vm2 vrsp).
        rewrite -(sem_preserved_RSP_GD var_tmp_not_magic exec_body); last exact: RSP_in_magic.
        rewrite /= /set_RSP Fv.setP_eq /= lp_rspE -/vrsp.
        case: vm2.[_]%vmap => // - [] ?? pw_proof /pword_of_word_uincl /= [] ??; subst.
        rewrite (sumbool_of_boolET pw_proof) truncate_word_u /=.
        case/and3P: ok_ret_addr => /eqP hrastack /eqP hioff sf_aligned_for_ptr.
        case/and3P: ok_stk_sz; rewrite !zify => stk_sz_pos stk_extra_pos sf_noovf.
        assert (root_range := wunsigned_range (stack_root m1')).
        have A := alloc_stackP ok_m1'.
        have top_range := ass_above_limit A.
        have top_stackE := wunsigned_top_stack_after_aligned_alloc stk_sz_pos stk_extra_pos sf_noovf sp_aligned ok_m1'.
        subst rastack.
        have sf_large : (wsize_size Uptr <= stack_frame_allocation_size (f_extra fd))%Z.
        - apply: Z.le_trans; last exact: proj1 (round_ws_range _ _).
          have := ass_ioff A.
          rewrite -hioff; move: (sf_stk_sz _) (sf_stk_extra_sz _) stk_sz_pos stk_extra_pos; lia.
        have rastack_no_overflow : (0 <= wunsigned (top_stack m1'))%Z ∧ (wunsigned (top_stack m1') +  wsize_size Uptr <= wunsigned (stack_root m1'))%Z.
        * assert (top_stack_range := wunsigned_range (top_stack m1')).
          assert (old_top_stack_range := wunsigned_range (top_stack (emem s1))).
          assert (h := wsize_size_pos Uptr).
                split; first lia.
          rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc // wrepr_opp.
          rewrite -/(stack_frame_allocation_size _) wunsigned_sub; last first.
          - split; last lia.
            rewrite top_stackE; move: (stack_frame_allocation_size _) => n; lia.
          rewrite A.(ass_root).
          etransitivity; last exact: top_stack_below_root.
          rewrite -/(top_stack (emem s1)); lia.
        have -> : read m2 (top_stack m1')%R Uptr = read m1 (top_stack m1')%R Uptr.
        * apply: eq_read => i [] i_lo i_hi; symmetry; apply: H2.
          - rewrite addE wunsigned_add; lia.
          rewrite (Memory.alloc_stackP ok_m1').(ass_valid).
          apply/orP; case.
          - apply/negP; apply: stack_region_is_free.
            rewrite -/(top_stack _).
            move: (stack_frame_allocation_size _) top_stackE sf_large => n top_stackE sf_large.
            rewrite addE !wunsigned_add; lia.
          rewrite !zify (ass_add_ioff A) -hioff addE.
          rewrite wunsigned_add; lia.
        rewrite (alloc_stack_top_stack ok_m1') top_stack_after_aligned_alloc //.
        move: ok_ra; rewrite wrepr0 GRing.addr0 /stack_frame_allocation_size wrepr_opp => -> /=.
        have := decode_encode_label small_dom_p' mem_lret.
        rewrite ok_retptr /= => -> /=.
        case: ok_cbody => fd' -> -> /=; rewrite ok_pc /setcpc /=.
        rewrite (Eqdep_dec.UIP_dec Bool.bool_dec pw_proof (cmp_le_refl Uptr)).
        reflexivity.
      + apply vmap_eq_exceptT with vm2.
        + by apply: vmap_eq_exceptI K2; SvD.fsetdec.
        by move=> x hx; rewrite Fv.setP_neq //; apply/eqP; SvD.fsetdec.
      + by apply wf_vm_set.
      + by move => ?; rewrite /set_RSP !Fv.setP; case: eqP => // ?; subst.
      move => a [] a_lo a_hi /negbTE nv.
      have A := alloc_stackP ok_m1'.
      have [L H] := ass_above_limit A.
      apply: H2.
      * rewrite (ass_root A).
        split; last exact: a_hi.
        etransitivity; last exact: a_lo.
        suff : (0 <= sf_stk_sz (f_extra fd))%Z by lia.
        by case/andP: ok_stk_sz => /lezP.
      rewrite (ass_valid A) nv /= !zify => - [].
      change (wsize_size U8) with 1%Z.
      rewrite (ass_add_ioff A).
      move: (sf_stk_sz _) (sf_stk_ioff _) (sf_stk_extra_sz _) (ass_ioff A) H; lia.
    }
  Qed.

  Lemma linear_fdP ii k s1 fn s2 :
    sem_call p  extra_free_registers var_tmp ii k s1 fn s2 →
    Pfun ii k s1 fn s2.
  Proof.
    apply (@sem_call_Ind _ _ _ _  p extra_free_registers var_tmp Pc Pi Pi_r Pfun Hnil Hcons HmkI Hasgn Hopn Hsyscall Hif_true Hif_false Hwhile_true Hwhile_false Hcall Hproc).
  Qed.

  Lemma linear_exportcallP gd scs m fn args scs' m' res :
    sem_export_call p extra_free_registers var_tmp gd scs m fn args scs' m' res →
    ∃ fd,
      [/\
         get_fundef p'.(lp_funcs) fn = Some fd,
        fd.(lfd_export) &
      ∀ lm vm args',
        wf_vm vm →
        vm.[vid (lp_rsp p')]%vmap = ok (pword_of_word (top_stack m)) →
        match_mem m lm →
        mapM (λ x : var_i, get_var vm x) fd.(lfd_arg) = ok args' →
        List.Forall2 value_uincl args args' →
        vm.[vid p'.(lp_rip)]%vmap = ok (pword_of_word gd) →
        vm_initialized_on vm ((var_tmp : var) :: lfd_callee_saved fd) →
        all2 check_ty_val fd.(lfd_tyin) args' ∧
        ∃ vm' lm' res',
          (* TODO: vm = vm' [\ k ] ; stack_stable m m' ; etc. *)
          [/\
            lsem_exportcall p' scs lm fn vm scs' lm' vm',
            match_mem m' lm',
            mapM (λ x : var_i, get_var vm' x) fd.(lfd_res) = ok res',
            List.Forall2 value_uincl res res' &
            all2 check_ty_val fd.(lfd_tyout) res'
          ]
      ].
  Proof.
    case => fd ok_fd Export to_save_not_result RSP_not_result H.
    exists (linear_fd fn fd).2; split.
    - exact: get_fundef_p' ok_fd.
    - exact: Export.
    rewrite lp_rspE => lm vm args' ok_vm vm_rsp M ok_args' args_args' vm_rip safe_registers.
    have {H}[] := H vm args' ok_vm ok_args' args_args' vm_rsp.
    - by move: vm_rip; rewrite lp_ripE.
    move => m1 k m2 vm2 res' ok_save_stack ok_callee_saved ok_m1 wt_args' sexec ok_res' res_res' wt_res' vm2_rsp ?; subst m'.
    split; first by [].
    set k' := Sv.union k (Sv.union match fd.(f_extra).(sf_return_address) with RAreg ra | RAstack (Some ra) _ => Sv.singleton ra | RAstack _ _ => Sv.empty | RAnone => Sv.add var_tmp vflags end (if fd.(f_extra).(sf_save_stack) is SavedStackReg r then Sv.singleton r else Sv.empty)).
    set s1 := {| escs := scs; emem := m ; evm := vm |}.
    set s2 := {| escs := scs'; emem := free_stack m2 ; evm := set_RSP p (free_stack m2) vm2 |}.
    have {sexec} /linear_fdP : sem_call p extra_free_registers var_tmp dummy_instr_info k' s1 fn s2.
    - econstructor.
      + exact: ok_fd.
      + by rewrite /ra_valid; move/eqP: Export => ->.
      + exact: ok_save_stack.
      + by rewrite /top_stack_aligned; move/eqP: Export => ->.
      + exact: vm_rsp.
      + exact: ok_m1.
      + exact: ok_args'.
      + exact: wt_args'.
      + move: sexec.
        rewrite /ra_undef_vm /ra_undef /ra_undef_vm_none /ra_undef_none /ra_vm.
        move/eqP: Export => ->.
        exact.
      + exact: ok_res'.
      + exact: wt_res'.
      + exact: vm2_rsp.
      reflexivity.
    case/(_ lm vm (linear_body liparams p fn fd.(f_extra) fd.(f_body)).2 RAnone None (top_stack m) (map fst fd.(f_extra).(sf_to_save)) ok_vm M).
    - move => x; rewrite !Fv.setP.
      case: eqP => ?; first by subst; rewrite vm_rsp.
      case: eqP => ?; first subst.
      + move/allP: safe_registers => /(_ var_tmp).
        rewrite inE eqxx => /(_ erefl).
        rewrite /get_var.
        by case: _.[_]%vmap => // - [].
      by [].
    - by eexists; first exact: get_fundef_p' ok_fd.
    - eexists; first exact: ok_fd.
      by apply/eqP: Export.
    - by [].
    - eexists; first exact: ok_fd.
      by move/eqP: Export => /= ->.
    - eexists; first exact: ok_fd.
      by move/eqP: Export => /= ->.
    - by move: safe_registers; rewrite /= Export {1}/vm_initialized_on /= => /andP[] _.
    move => lmo vmo texec vm_eq_vmo ? s2_vmo ? M'.
    have vm2_vmo : ∀ r, List.In r (f_res fd) → (eval_uincl vm2.[r] vmo.[r])%vmap.
    - move => r r_in_result.
      have r_not_saved : ¬ Sv.In r (sv_of_list id (map fst fd.(f_extra).(sf_to_save))).
      + apply/Sv_memP.
        rewrite sv_of_listE map_id -sv_of_listE; apply/Sv_memP => K.
        move/disjointP: to_save_not_result => /(_ _ K).
        by apply; apply/Sv_memP; rewrite sv_of_listE; apply/in_map; exists r.
      apply: eval_uincl_trans (s2_vmo r r_not_saved).
      have r_not_rsp : vrsp != r.
      + apply/eqP => K.
        by move: RSP_not_result; rewrite sv_of_listE; apply/negP/negPn/in_map; exists r.
      by rewrite !Fv.setP_neq.
    have : ∃ lres : values,
        [/\ mapM (λ x : var_i, get_var vmo x) (f_res fd) = ok lres, List.Forall2 value_uincl res lres & all2 check_ty_val (f_tyout fd) lres ].
    {
      move/mapM_Forall2: ok_res' res_res' (f_tyout fd) wt_res' vm2_vmo.
      move: res' res (f_res fd).
      elim => [ | r' res' ih ].
      + move => _ _ /List_Forall2_inv_r-> /List_Forall2_inv_r -> [] // _ _.
        by exists [::].
      move => _ _ /List_Forall2_inv_r[] d [] ds [] -> [] ok_r' ok_res' /List_Forall2_inv_r[] r [] res [] -> [] r_r' res_res'.
      case => // ty tys /= /andP[] wt_r' wt_res' vm2_vmo.
      have := vm2_vmo d (or_introl _ erefl).
      move: ok_r'; rewrite {1 3}/get_var.
      case: vm2.[d]%vmap => [ | [] // ] /= v /ok_inj ?; subst r'.
      case: vmo.[d]%vmap => // v' v_v' /=.
      move: ih => /(_ _ _ ok_res' res_res' _ wt_res')[].
      + by move => x hx; apply: vm2_vmo; right.
      move => lres [] -> /= res_lres wt_lres.
      eexists; split; first reflexivity.
      + constructor; last by [].
        exact: value_uincl_trans v_v'.
      rewrite /= wt_lres andbT.
      exact: check_ty_val_uincl v_v'.
    }
    case => lres [] ok_lres res_lres wt_lres.
    exists vmo, lmo, lres; split.
    - econstructor; first exact: get_fundef_p' ok_fd.
      + exact: Export.
      + exact: texec.
      move => r hr; apply: vm_eq_vmo.
      subst k'.
      move: ok_callee_saved hr; clear.
      rewrite -/(ra_vm _ _) -/(saved_stack_vm _).
      move: (Sv.union k _) => X.
      clear.
      rewrite sv_of_list_map Sv.diff_spec => S hrC [] hrX; apply.
      apply: S.
      by rewrite Sv.inter_spec.
    - exact: M'.
    - move/eqP: Export => /= -> /=.
      exact: ok_lres.
    - exact: res_lres.
    exact: wt_lres.
  Qed.

End PROOF.
End WITH_PARAMS.
