(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import expr compiler_util psem gen_map dead_calls.
(* ------- *) (* - *) Import PosSet.
Import Utf8 xseq.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Fixpoint i_Calls (i : instr) {struct i} : Sp.t :=
  let: MkI _ i := i in i_Calls_r i

with i_Calls_r (i : instr_r) {struct i} : Sp.t :=
  let c_Calls (cmd : cmd) :=
    foldr Sp.union Sp.empty [seq i_Calls c | c <- cmd]
  in

  match i with
  | Cassgn _  _  _ _  => Sp.empty
  | Copn   _  _  _  _ => Sp.empty
  | Cif    _  c1 c2   => Sp.union (c_Calls c1) (c_Calls c2)
  | Cfor   _  _  c1   => c_Calls c1
  | Cwhile _ c1 _  c2 => Sp.union (c_Calls c1) (c_Calls c2)
  | Ccall  _  _  f  _ => Sp.singleton f
  end.

Definition c_Calls (cmd : cmd) :=
  foldr Sp.union Sp.empty [seq i_Calls c | c <- cmd].

(* -------------------------------------------------------------------- *)
Lemma i_Calls_MkI ii i :
  i_Calls (MkI ii i) = i_Calls_r i.
Proof. by []. Qed.

Lemma i_Calls_asgn lv tg ty e :
  i_Calls_r (Cassgn lv tg ty e) = Sp.empty.
Proof. by []. Qed.

Lemma i_Calls_opn lv t op es :
  i_Calls_r (Copn lv t op es) = Sp.empty.
Proof. by []. Qed.

Lemma i_Calls_if e c1 c2 :
  i_Calls_r (Cif e c1 c2) = Sp.union (c_Calls c1) (c_Calls c2).
Proof. by []. Qed.

Lemma i_Calls_for v rg c1 :
  i_Calls_r (Cfor v rg c1) = c_Calls c1.
Proof. by []. Qed.

Lemma i_Calls_while a c1 e c2 :
  i_Calls_r (Cwhile a c1 e c2) = Sp.union (c_Calls c1) (c_Calls c2).
Proof. by []. Qed.

Lemma i_Calls_call ii lv f es :
  i_Calls_r (Ccall ii lv f es) = Sp.singleton f.
Proof. by []. Qed.

Lemma c_Calls_nil : c_Calls [::] = Sp.empty.
Proof. by []. Qed.

Lemma c_Calls_cons i c : c_Calls (i :: c) = Sp.union (i_Calls i) (c_Calls c).
Proof. by []. Qed.

Hint Rewrite i_Calls_MkI  i_Calls_asgn i_Calls_opn   : calls.
Hint Rewrite i_Calls_if   i_Calls_for  i_Calls_while : calls.
Hint Rewrite i_Calls_call c_Calls_nil  c_Calls_cons  : calls.

Definition CallsE :=
  (i_Calls_MkI , i_Calls_asgn, i_Calls_opn  ,
   i_Calls_if  , i_Calls_for , i_Calls_while,
   i_Calls_call, c_Calls_nil , c_Calls_cons ).

(* -------------------------------------------------------------------- *)
Lemma c_callsE c i : Sp.Equal (c_calls c i) (Sp.union c (c_Calls i)).
Proof.
move: c.
apply (@cmd_rect
         (fun i => forall c, Sp.Equal (i_calls_r c i) (Sp.union c (i_Calls_r i)))
         (fun i => forall c, Sp.Equal (i_calls c i) (Sp.union c (i_Calls i)))
         (fun i => forall c, Sp.Equal (c_calls c i) (Sp.union c (c_Calls i)))) => /=
  [ i0 ii Hi | | i0 c0 Hi Hc | x t e | xs o es | e c1 c2 Hc1 Hc2
    | v dir lo hi c0 Hc | a c0 e c' Hc Hc' | ii xs f es ] c //.
+ rewrite CallsE; SpD.fsetdec.
+ rewrite /= CallsE Hc Hi; SpD.fsetdec.
+ SpD.fsetdec.
+ SpD.fsetdec.
+ rewrite -/(foldl _ _) -/(foldl _ _) -/(c_calls _ _) -/(c_calls _ _) Hc2 Hc1 -/(c_Calls _) -/(c_Calls _); SpD.fsetdec.
+ rewrite -/(foldl _ _) -/(foldl _ _) -/(c_calls _ _) -/(c_calls _ _) Hc' Hc -/(c_Calls _) -/(c_Calls _); SpD.fsetdec.
+ SpD.fsetdec.
Qed.

Section Section.

Context {T:eqType} {pT:progT T} {sCP: semCallParams}.

Instance live_calls_m : Proper (Sp.Equal ==> eq ==> Sp.Equal) live_calls.
Proof.
  move=> x y le p p' <- {p'}.
  elim: p x y le => // [[n d] p] ih x y le /=.
  rewrite <- le.
  case: Sp.mem. 2: auto.
  apply: ih.
  rewrite ! c_callsE. SpD.fsetdec.
Qed.

Instance live_calls_mono : Proper (Sp.Subset ==> eq ==> Sp.Subset) live_calls.
Proof.
  move=> x y le p p' <- {p'}.
  elim: p x y le => // [[n d] p] ih x y le /=.
  case hm: Sp.mem. apply Sp.mem_spec in hm.
  rewrite (SpD.F.mem_1 (le _ hm)). apply: ih. rewrite ! c_callsE. SpD.fsetdec.
  case: Sp.mem. apply: ih. rewrite c_callsE. SpD.fsetdec.
  auto.
Qed.

Lemma live_calls_subset c p :
  Sp.Subset c (live_calls c p).
Proof.
  elim: p c => /=. SpD.fsetdec.
  move=> [n d] p ih c.
  case: Sp.mem => //.
  etransitivity. 2: apply: ih.
  rewrite c_callsE. SpD.fsetdec.
Qed.

Lemma live_calls_in K p fn fd :
  Sp.In fn K →
  get_fundef p fn = Some fd →
  Sp.Subset (c_Calls (f_body fd)) (live_calls K p).
Proof.
  elim: p K fn fd => // [[n d] p] ih K fn fd hn /=.
  case: eqP.
  - move <- => {n} /Some_inj ->.
    rewrite (SpD.F.mem_1 hn) c_callsE.
    etransitivity. 2: apply: live_calls_subset. SpD.fsetdec.
  - move => ne rec. specialize (ih _ _ _ hn rec).
    case hm: Sp.mem => //.
    etransitivity. exact: ih.
    apply: live_calls_mono => //.
    rewrite c_callsE. SpD.fsetdec.
Qed.

(* -------------------------------------------------------------------- *)
Lemma get_dead_calls K p n d:
  Sp.In n K →
  get_fundef p n = Some d →
  get_fundef (dead_calls K p) n = Some d.
Proof.
  move=> k a.
  rewrite /get_fundef.
  rewrite (assoc_filter (p:= λ x, Sp.mem x K)) => //.
  apply SpD.F.mem_1, k.
Qed.

Section PROOF.

  Variables (K : Sp.t) (p: prog) (ev:extra_val_t).
  Notation gd := (p_globs p).

  Let p' := {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := dead_calls K (p_funcs p) |}.

  Context (pfxp: Sp.Subset (live_calls K (p_funcs p)) K).

  Definition def_incl sv : Prop := Sp.Subset sv K.

  Lemma def_incl_union a b :
    def_incl (Sp.union a b) → def_incl a ∧ def_incl b.
  Proof.
    rewrite /def_incl; intuition SpD.fsetdec.
  Qed.

  Let Pi s (i:instr) s' :=
    def_incl (i_Calls i) -> sem_I p ev s i s' -> sem_I p' ev s i s'.

  Let Pi_r s (i:instr_r) s' :=
    def_incl (i_Calls_r i) -> sem_i p ev s i s' -> sem_i p' ev s i s'.

  Let Pc s (c:cmd) s' :=
    def_incl (c_Calls c) -> sem p ev s c s' -> sem p' ev s c s'.

  Let Pfor (i:var_i) vs s c s' :=
    def_incl (c_Calls c) -> sem_for p ev i vs s c s' -> sem_for p' ev i vs s c s'.

  Let Pfun m1 fn vargs m2 vres :=
    def_incl (Sp.singleton fn) -> sem_call p ev m1 fn vargs m2 vres -> sem_call p' ev m1 fn vargs m2 vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof. move=> s _ _; exact: Eskip. Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c Hsi Hi Hsc Hc Hincl.
    rewrite CallsE in Hincl.
    move: Hincl=> /def_incl_union [Hincli Hinclc] H.
    exact: (Eseq (Hi Hincli Hsi) (Hc Hinclc Hsc)).
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof.
    move=> ii i s1 s2 Hs Hi Hincl _.
    apply: EmkI.
    exact: (Hi Hincl Hs).
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move => s1 s2 x tag ty e v v' hv hv' hw _ _.
    by apply: Eassgn;eauto.
  Qed.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move=> s1 s2 t o xs es H _ _; by apply: Eopn; eauto.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H Hsi Hc Hincl _.
    rewrite CallsE in Hincl.
    move: Hincl=> /def_incl_union [Hincl1 Hincl2].
    apply: (Eif_true (P:=p') _ H).
    exact: (Hc Hincl1 Hsi).
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 H Hsi Hc Hincl _.
    rewrite CallsE in Hincl.
    move: Hincl=> /def_incl_union [Hincl1 Hincl2].
    apply: (Eif_false (P:=p') _ H).
    exact: (Hc Hincl2 Hsi).
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' Hs1 Hc1 H Hs2 Hc2 Hsw Hiw Hinclw _.
    rewrite CallsE in Hinclw.
    have /def_incl_union [Hincl Hincl'] := Hinclw.
    exact: (Ewhile_true (Hc1 Hincl Hs1) H (Hc2 Hincl' Hs2) (Hiw Hinclw Hsw)).
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' Hs1 Hc1 H Hinclw _.
    rewrite CallsE in Hinclw.
    have /def_incl_union [Hincl Hincl'] := Hinclw.
    exact: (Ewhile_false _ _ (Hc1 Hincl Hs1) H).
  Qed.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi Hlo Hhi Hsf Hf Hincl _.
    rewrite CallsE in Hincl.
    apply: (Efor (P:= p') Hlo Hhi).
    exact: (Hf Hincl Hsf).
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s i c Hincl _; exact: EForDone.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
   move=> s1 s1' s2 s3 i w ws c H Hsc Hc Hsf Hf Hincl _.
   exact: (EForOne H (Hc Hincl Hsc) (Hf Hincl Hsf)).
  Qed.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs Hargs Hcall Hfun Hres Hincl Hsi.
    apply: (Ecall (P:=p') _ Hargs _ Hres).
    exact: Hfun.
  Qed.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
    move=> m1 m2 fn fd vargs vargs' s0 s1 s2 vres vres'
           Hget Htyin Hi Hvargs Hsem Hc Hvres Htyout Hfi Hin Hcall.
    have Hin' := Hin _ (SpD.F.singleton_2 erefl).
    have Hfd := get_dead_calls Hin' Hget.
    refine (EcallRun (P:=p') Hfd Htyin Hi Hvargs _ Hvres Htyout Hfi).
    apply: Hc=> // n hn; apply: pfxp.
    by apply: live_calls_in Hget n hn.
  Qed.

  Lemma dead_calls_callP fd mem mem' va vr:
    Sp.In fd K ->
    sem_call p ev mem fd va mem' vr ->
    sem_call p' ev mem fd va mem' vr.
  Proof.
    move=> Hincl H.
    apply: (@sem_call_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
           Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc)=> //.
    move => ??; SpD.fsetdec.
  Qed.

End PROOF.

Lemma foldl_compat x y l (x_eq_y: Sp.Equal x y):
  Sp.Equal (foldl (fun f c => Sp.add c f) x l)
           (foldl (fun f c => Sp.add c f) y l).
Proof.
elim: l x y x_eq_y=> // a l IH /= x y x_eq_y.
by apply: IH; SpD.fsetdec.
Qed.

Lemma foldlE a l x:
  Sp.Equal (foldl (fun f c => Sp.add c f) x (a :: l))
           (Sp.add a (foldl (fun f c => Sp.add c f) x l)).
Proof.
elim: l a x=> // a0 l IH a x.
rewrite /= in IH.
rewrite /=.
rewrite -IH.
apply: foldl_compat; SpD.fsetdec.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dead_calls_errP (s : Sp.t) (p p': prog) :
  dead_calls_err s p = cfok p' →
  ∀ f ev m args m' res, Sp.In f s →
    sem_call p ev m f args m' res →
    sem_call p' ev m f args m' res.
Proof.
rewrite /dead_calls_err; case: ifP => // /SpD.F.subset_2 pfx [] <- f ev m args m' res fins Hcall.
apply: dead_calls_callP=> //.
apply: live_calls_subset fins.
Qed.

Theorem dead_calls_err_seqP (s : seq funname) (p p': prog) :
  dead_calls_err_seq s p = cfok p' →
  ∀ f ev m args m' res, f \in s →
    sem_call p ev m f args m' res →
    sem_call p' ev m f args m' res.
Proof.
  rewrite /dead_calls_err_seq.
  move=> h f ev m args m' res fins; apply: (dead_calls_errP h).
  elim: {h} s fins=> // a l IH Hin.
  rewrite foldlE.
  rewrite in_cons in Hin; case/orP: Hin=> [/eqP ->|/IH Hin]; SpD.fsetdec.
Qed.

Lemma dead_calls_err_get_fundef s p p' fn fd :
  dead_calls_err s p = cfok p' →
  get_fundef (p_funcs p') fn = Some fd →
  get_fundef (p_funcs p) fn = Some fd.
Proof.
rewrite /dead_calls_err; case: ifP => // _ [<- {p'}].
move: (live_calls s (p_funcs p)) => {s} s.
rewrite /get_fundef /dead_calls (assoc_filterI (λ q, Sp.mem q s)).
by case: ifP.
Qed.

End Section.
