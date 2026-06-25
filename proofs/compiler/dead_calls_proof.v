(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
(* ------- *) Require Import expr compiler_util psem gen_map dead_calls.
Import Utf8 xseq.

Section WITH_PARAMS.

Context
  {wsw : WithSubWord}
  {dc:DirectCall}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}.

(* -------------------------------------------------------------------- *)

Section CALLS.

Fixpoint i_Calls (i : instr) {struct i} : Sf.t :=
  let: MkI _ i := i in i_Calls_r i

with i_Calls_r (i : instr_r) {struct i} : Sf.t :=
  let c_Calls (cmd : cmd) :=
    foldr Sf.union Sf.empty [seq i_Calls c | c <- cmd]
  in

  match i with
  | Cassgn _ _ _ _
  | Copn   _ _ _ _
  | Csyscall _ _ _
  | Cassert _
    => Sf.empty
  | Cif    _  c1 c2   => Sf.union (c_Calls c1) (c_Calls c2)
  | Cfor   _  _  c1   => c_Calls c1
  | Cwhile _ c1 _ _ c2 => Sf.union (c_Calls c1) (c_Calls c2)
  | Ccall _ f _ => Sf.singleton f
  end.

Definition c_Calls (cmd : cmd) :=
  foldr Sf.union Sf.empty [seq i_Calls c | c <- cmd].

(* -------------------------------------------------------------------- *)
Lemma i_Calls_MkI ii i :
  i_Calls (MkI ii i) = i_Calls_r i.
Proof. by []. Qed.

Lemma i_Calls_asgn lv tg ty e :
  i_Calls_r (Cassgn lv tg ty e) = Sf.empty.
Proof. by []. Qed.

Lemma i_Calls_opn lv t op es :
  i_Calls_r (Copn lv t op es) = Sf.empty.
Proof. by []. Qed.

Lemma i_Calls_syscall lv op es :
  i_Calls_r (Csyscall lv op es) = Sf.empty.
Proof. by []. Qed.

Lemma i_Calls_if e c1 c2 :
  i_Calls_r (Cif e c1 c2) = Sf.union (c_Calls c1) (c_Calls c2).
Proof. by []. Qed.

Lemma i_Calls_for v rg c1 :
  i_Calls_r (Cfor v rg c1) = c_Calls c1.
Proof. by []. Qed.

Lemma i_Calls_while a c1 e ei c2 :
  i_Calls_r (Cwhile a c1 e ei c2) = Sf.union (c_Calls c1) (c_Calls c2).
Proof. by []. Qed.

Lemma i_Calls_call lv f es :
  i_Calls_r (Ccall lv f es) = Sf.singleton f.
Proof. by []. Qed.

Lemma c_Calls_nil : c_Calls [::] = Sf.empty.
Proof. by []. Qed.

Lemma c_Calls_cons i c : c_Calls (i :: c) = Sf.union (i_Calls i) (c_Calls c).
Proof. by []. Qed.

Hint Rewrite i_Calls_MkI  i_Calls_asgn i_Calls_opn  i_Calls_syscall : calls.
Hint Rewrite i_Calls_if   i_Calls_for  i_Calls_while : calls.
Hint Rewrite i_Calls_call c_Calls_nil  c_Calls_cons  : calls.

Definition CallsE :=
  (i_Calls_MkI , i_Calls_asgn, i_Calls_opn  , i_Calls_syscall,
   i_Calls_if  , i_Calls_for , i_Calls_while,
   i_Calls_call, c_Calls_nil , c_Calls_cons ).

(* -------------------------------------------------------------------- *)

Let Pr i := forall c, Sf.Equal (i_calls_r c i) (Sf.union c (i_Calls_r i)).
Let Pi i := forall c, Sf.Equal (i_calls c i) (Sf.union c (i_Calls i)).
Let Pc i := forall c, Sf.Equal (c_calls c i) (Sf.union c (c_Calls i)).

Lemma c_callsE c i : Sf.Equal (c_calls c i) (Sf.union c (c_Calls i)).
Proof.
move: c.
apply: (cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)) => /=
  [ i0 ii Hi | | i0 c0 Hi Hc | x t ty e | xs t o es | xs o es | a | e c1 c2 Hc1 Hc2
    | v dir lo hi c0 Hc | a c0 e ei c' Hc Hc' | ii xs f es ] c /=.
+ by apply Hi.
+ rewrite CallsE; SfD.fsetdec.
+ rewrite CallsE Hc Hi; SfD.fsetdec.
1-4: SfD.fsetdec.
+ rewrite /i_calls_r  -/(foldl _ _) -/(foldl _ _) -/(c_calls _ _) -/(c_calls _ _)
    Hc2 Hc1 -/(c_Calls _) -/(c_Calls _); SfD.fsetdec.
+ by apply Hc.
+ rewrite /i_calls_r  -/(foldl _ _) -/(foldl _ _) -/(c_calls _ _) -/(c_calls _ _)
    Hc' Hc -/(c_Calls _) -/(c_Calls _); SfD.fsetdec.
rewrite /i_calls_r; SfD.fsetdec.
Qed.

End CALLS.

Section Section.

Context {pT: progT} {sCP: semCallParams}.

#[local]
Instance live_calls_m : Proper (Sf.Equal ==> eq ==> Sf.Equal) live_calls.
Proof.
  move=> x y le p p' <- {p'}.
  elim: p x y le => // [[n d] p] ih x y le /=.
  rewrite <- le.
  case: Sf.mem. 2: auto.
  apply: ih.
  rewrite ! c_callsE. SfD.fsetdec.
Qed.

#[local]
Instance live_calls_mono : Proper (Sf.Subset ==> eq ==> Sf.Subset) live_calls.
Proof.
  move=> x y le p p' <- {p'}.
  elim: p x y le => // [[n d] p] ih x y le /=.
  case hm: Sf.mem. apply Sf.mem_spec in hm.
  rewrite (SfD.F.mem_1 (le _ hm)). apply: ih. rewrite ! c_callsE. SfD.fsetdec.
  case: Sf.mem. apply: ih. rewrite c_callsE. SfD.fsetdec.
  auto.
Qed.

Lemma live_calls_subset c p :
  Sf.Subset c (live_calls c p).
Proof.
  elim: p c => /=. SfD.fsetdec.
  move=> [n d] p ih c.
  case: Sf.mem => //.
  etransitivity. 2: apply: ih.
  rewrite c_callsE. SfD.fsetdec.
Qed.

Lemma live_calls_in K p fn fd :
  Sf.In fn K →
  get_fundef p fn = Some fd →
  Sf.Subset (c_Calls (f_body fd)) (live_calls K p).
Proof.
  elim: p K fn fd => // [[n d] p] ih K fn fd hn /=.
  case: eqP.
  - move <- => {n} /Some_inj ->.
    rewrite (SfD.F.mem_1 hn) c_callsE.
    etransitivity. 2: apply: live_calls_subset. SfD.fsetdec.
  - move => ne rec. specialize (ih _ _ _ hn rec).
    case hm: Sf.mem => //.
    etransitivity. exact: ih.
    apply: live_calls_mono => //.
    rewrite c_callsE. SfD.fsetdec.
Qed.

(* -------------------------------------------------------------------- *)
Lemma get_dead_calls K p n d:
  Sf.In n K →
  get_fundef p n = Some d →
  get_fundef (dead_calls K p) n = Some d.
Proof.
  move=> k a.
  rewrite /get_fundef.
  rewrite (assoc_filter (p:= λ x, Sf.mem x K)) => //.
  apply SfD.F.mem_1, k.
Qed.

Section PROOF.

  Variables (K : Sf.t) (p: prog) (ev:extra_val_t).
  Notation gd := (p_globs p).

  Let p' := {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := dead_calls K (p_funcs p) |}.

  Context (pfxp: Sf.Subset (live_calls K (p_funcs p)) K).

  Definition def_incl sv : Prop := Sf.Subset sv K.

  Lemma def_incl_union a b :
    def_incl (Sf.union a b) → def_incl a ∧ def_incl b.
  Proof.
    rewrite /def_incl; intuition SfD.fsetdec.
  Qed.

  Section IT.

  Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

  Definition dc_spec :=
   {|
     rpreF_ := λ (fn1 fn2 : funname) (fs1 fs2 : fstate), [/\ fn1 = fn2, fs1 = fs2 & Sf.In fn1 K] ;
     rpostF_ := λ (_ _ : funname) (_ _ fr1 fr2 : fstate), fr1 = fr2
  |}.

  Let Pi (i:instr) :=
    def_incl (i_Calls i) ->
    wequiv_rec p p' ev ev dc_spec (st_eq tt) [::i] [::i] (st_eq tt).

  Let Pi_r i := forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    def_incl (c_Calls c) ->
    wequiv_rec p p' ev ev dc_spec (st_eq tt) c c (st_eq tt).

  #[local] Lemma _checker_st_eqP : Checker_eq p p' checker_st_eq.
  Proof. by apply checker_st_eqP. Qed.

  #[local] Hint Resolve _checker_st_eqP : core.

  Lemma it_dead_calls_callP fn :
    wiequiv_f p p' ev ev (rpreF (eS:= dc_spec)) fn fn (rpostF (eS:=dc_spec)).
  Proof.
    apply wequiv_fun_ind => {}fn _ fs _ [<- <- hin] fd hfd; exists fd => //.
    + by apply get_dead_calls.
    move=> s hinit.
    exists s=> //; exists (st_eq tt), (st_eq tt); split => //; last by apply st_eq_finalize.
    apply (cmd_rect (Pi:=Pi) (Pr:=Pi_r) (Pc:=Pc)) => //; rewrite /Pi_r /Pi /Pc.
    + by move=> ??; apply wequiv_nil.
    + move=> > hi hc; rewrite CallsE => /def_incl_union [??].
      by apply wequiv_cons with (st_eq tt); [apply hi | apply hc].
    + by move=> > _; apply wequiv_assgn_rel_eq with checker_st_eq tt.
    + by move=> > _; apply wequiv_opn_rel_eq with checker_st_eq tt.
    + by move=> > _; apply wequiv_syscall_rel_eq with checker_st_eq tt.
    + by move=> > _; apply wequiv_noassert.
    + move=> > hc1 hc2 ii; rewrite !CallsE => /def_incl_union [??].
      apply wequiv_if_rel_eq with checker_st_eq tt tt tt => //.
      + by apply hc1.
      by apply hc2.
    + move=> > hc ii; rewrite !CallsE => ?.
      by apply wequiv_for_rel_eq with checker_st_eq tt tt => //; apply hc.
    + move=> > hc hc' ii; rewrite !CallsE => /def_incl_union [??].
      apply wequiv_while_rel_eq with checker_st_eq tt => //.
      + by apply hc.
      by apply hc'.
    + move=> >; rewrite !CallsE => hfin.
      apply wequiv_call_rel_eq with checker_st_eq tt => //.
      move=> ???; apply: wequiv_fun_rec; split => //.
      by move: hfin; rewrite /def_incl; SfD.fsetdec.
    move=> n hn; apply: pfxp.
    by apply: live_calls_in hfd n hn.
  Qed.

  End IT.

End PROOF.

Lemma foldl_compat x y l (x_eq_y: Sf.Equal x y):
  Sf.Equal (foldl (fun f c => Sf.add c f) x l)
           (foldl (fun f c => Sf.add c f) y l).
Proof.
elim: l x y x_eq_y=> // a l IH /= x y x_eq_y.
by apply: IH; SfD.fsetdec.
Qed.

Lemma foldlE a l x:
  Sf.Equal (foldl (fun f c => Sf.add c f) x (a :: l))
           (Sf.add a (foldl (fun f c => Sf.add c f) x l)).
Proof.
elim: l a x=> // a0 l IH a x.
rewrite /= in IH.
rewrite /=.
rewrite -IH.
apply: foldl_compat; SfD.fsetdec.
Qed.

(* -------------------------------------------------------------------- *)

Section IT.

Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Lemma it_dead_calls_errP (s : Sf.t) (p p': prog) :
  dead_calls_err s p = ok p' →
  ∀ f ev, Sf.In f s →
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) f f (rpostF (eS := eq_spec)).
Proof.
rewrite /dead_calls_err.
case: ifP => // /SfD.F.subset_2 pfx [] <- f ev hin fs _ [_ <-].
apply: it_dead_calls_callP => //; split => //.
exact: live_calls_subset.
Qed.

Theorem it_dead_calls_err_seqP (s : seq funname) (p p': prog) :
  dead_calls_err_seq s p = ok p' →
  ∀ f ev, f \in s →
  wiequiv_f p p' ev ev (rpreF (eS := eq_spec)) f f (rpostF (eS := eq_spec)).
Proof.
  rewrite /dead_calls_err_seq.
  move=> h f ev fins; apply: (it_dead_calls_errP h).
  elim: {h} s fins=> // a l IH Hin.
  rewrite foldlE.
  rewrite in_cons in Hin; case/orP: Hin=> [/eqP ->|/IH Hin]; SfD.fsetdec.
Qed.

End IT.

Lemma dead_calls_err_get_fundef s p p' fn fd :
  dead_calls_err s p = ok p' →
  get_fundef (p_funcs p') fn = Some fd →
  get_fundef (p_funcs p) fn = Some fd.
Proof.
rewrite /dead_calls_err; case: ifP => // _ [<- {p'}].
move: (live_calls s (p_funcs p)) => {}s.
rewrite /get_fundef /dead_calls (assoc_filterI (λ q, Sf.mem q s)).
by case: ifP.
Qed.

End Section.

End WITH_PARAMS.
