From Coq Require Import Program.Equality.
From Coq Require Import Lia JMeq.
From HB Require Import structures.

From mathcomp Require Import
  ssreflect
  ssralg
  ssrfun
  ssrbool
  ssrnum
  ssrnat
  choice
  distr
  eqtype
  fintype
  matrix
  order
  reals
  seq
  word
  word_ssrZ
.

From ITree Require Import
  Basics
  ITree
  ITreeDefinition
  ITreeFacts
  Rutt
  RuttFacts
  Exception
.
Import ITree.

Require Import
  compiler
  core_logics
  distr
  utils
  word
.
Require Import
  arch_decl
  arch_extra
  arch_sem
  arch_params
  sem_params_of_arch_extra
.
Require Import
  rutt_extras
  xrutt
  xrutt_facts
.
Require Import
  arch_params_proof
  stack_alloc_proof_1
  stack_alloc_proof_2
  compiler_proof
  it_compiler_proof
.
Require allocation.

Require Import
  adv
  it_sems_core
  psem
  psem_facts
  relational_logic
  hoare_logic
.

Require Import it_exec.

Import Order.TTheory.

#[local] Open Scope ring_scope.
#[local] Open Scope Z.
#[local] Open Scope order_scope.

Coercion Pos.to_nat : positive >-> nat.

Notation "'let*' p ':=' c1 'in' c2" :=
  (@ITree.bind _ _ _ c1 (fun p => c2))
    (at level 61, p as pattern, c1 at next level, right associativity).

Notation "x |> f" := (f x) (only parsing, at level 25).

Definition r2o {E A} (r : result E A) : option A :=
  if r is Ok v then Some v else None.

Definition rdflt {E A} (d : A) (r : result E A) : A :=
  if r is Ok v then v else d.

Lemma valid_getP n (a : WArray.array n) i :
  reflect
    (exists w, WArray.get8 a i = ok w)
    (WArray.in_bound a i && WArray.is_init a i).
Proof.
rewrite /WArray.get8; case: WArray.in_bound; last by constructor => -[].
case: WArray.is_init; last by constructor => -[].
constructor; eexists; reflexivity.
Qed.

Lemma decode_u8 (w : u8) : LE.decode U8 [:: w ] = w.
Proof. by rewrite /LE.decode /make_vec /= Z.lor_0_r wrepr_unsigned. Qed.

(* TODO MOVE *)
Section SAFE.

  Require Import core_logics.
  From Paco Require Import paco.
  From ITree Require Import
    ITree
    ITreeFacts
    Basics.HeterogeneousRelations
    Interp.Recursion
    Eq.Paco2
    Eq.Rutt
    Eq.RuttFacts.
  Require Import xrutt xrutt_facts rutt_extras.

Definition EPreRel_safe E1 E2 is_error (REv : prerel E1 E2) : prerel E1 E2 :=
  fun A B e1 e2 => [\/ is_error _ e1 | REv A B e1 e2 ].

Context
  {E1 E2 : Type -> Type}
  (is_error : forall T, E1 T -> bool)
  (REv : prerel E1 E2) (RAns : postrel E1 E2)
  (PEv1 : prepred E1) (PAns1 : postpred E1)
  (PEv2 : prepred E2) (PAns2 : postpred E2)
  {R1 R2 : Type}
  (RR : R1 -> R2 -> Prop) (P1 : R1 -> Prop) (P2:R2 -> Prop).

Lemma safe_xrutt_rutt (t1 : itree E1 R1) t2 :
  safe is_error t1 ->
  xrutt (errcutoff is_error) nocutoff (EPreRel_safe is_error REv) RAns RR t1 t2 ->
  rutt REv RAns RR t1 t2.
Proof.
  move: t1 t2; pcofix CIH => t1 t2 hsafe hxrutt.
  pstep. punfold hxrutt. red in hxrutt |- *.
  move: hsafe; rewrite {1}(itree_eta t1).
  elim: hxrutt => // {t1 t2}.
  + by move=> r1 r2 hRR _; constructor.
  + move=> t1 t2 hxrutt hsafe; constructor.
    by pclearbot; right; apply CIH => //; apply safe_Tau.
  + move=> T1 T2 e1 e2 k1 k2 _ _ hREv hAns hsafe.
    have [hnerr {}hsafe]:= safe_inv_Vis hsafe.
    case: hREv => hREv; first by rewrite hREv in hnerr.
    constructor=> // r1 r2 /hAns hxrutt.
    by pclearbot; right; eauto.
  + move=> T e1 k1 ot2 + hsafe.
    have [hnerr _]:= safe_inv_Vis hsafe.
    rewrite /errcutoff.
    move => H.
    have: (is_error e1 = false).
    { simpl in hnerr. red in hnerr.
      rewrite /negb in hnerr.
      rewrite H in hnerr. auto with *. }
    eauto with *.
  + move=> t1 ot2 _ hrec.
    by rewrite -safe_Tau {1}(itree_eta t1) => /hrec; apply Rutt.EqTauL.
  by move=> ot1 t2 _ hrec /hrec; apply Rutt.EqTauR.
Qed.

Lemma lutt_xrutt_trans_l' t1 t2 (REv' : prerel E1 E2) (RAns' : postrel E1 E2) RR' :
  (forall A1 A2 e1 e2,
      PEv1 e1 -> REv e1 e2 -> REv' A1 A2 e1 e2) ->
  (forall A1 A2 e1 a1 e2 a2,
      IsNoCut_ (errcutoff is_error) A1 e1 ->
      IsNoCut_ nocutoff A2 e2 ->
      PEv1 e1 ->
      REv e1 e2 ->
      RAns' A1 A2 e1 a1 e2 a2 ->
      PAns1 e1 a1 /\ RAns e1 a1 e2 a2) ->
  (forall r1 r2, P1 r1 -> RR r1 r2 -> RR' r1 r2) ->
  lutt PEv1 PAns1 P1 t1 ->
  xrutt (errcutoff is_error) nocutoff REv RAns RR t1 t2 ->
  xrutt (errcutoff is_error) nocutoff REv' RAns' RR' t1 t2.
Proof.
move=> he ha hr h1 h2.
apply: xrutt_weaken_v2; last exact: lutt_xrutt_trans_l h1 h2.
- done.
- done.
- move=> ???? []; exact: he.
- move=> ???????? []; exact: ha.
move=> ?? []; exact: hr.
Qed.

End SAFE.

Section ISEM_FINALIZE.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {wsw : WithSubWord}
  {scP : semCallParams}
  {dc : DirectCall}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE : RndE0 syscall_state E0}
.

(* TODO this should say that the values have the right types, nothing else. *)
Definition is_finalize fd fs := exists st, finalize_funcall fd st = ok fs.

#[local] Existing Instance trivial_invEvent.

Lemma isem_fun_finalize p ev fn fd fs :
  get_fundef (p_funcs p) fn = Some fd ->
  lutt
    (fun _ => PredT) (fun _ _ => PredT)
    (is_finalize fd)
    (isem_fun p ev fn fs).
Proof.
move=> h.
rewrite isem_call_unfold /isem_fun_body /kget_fundef h /= bind_ret_l.
apply: lutt_bind; first exact: lutt_true.
move=> s _; apply: lutt_bind; first exact: lutt_true.
move=> s' _; exists (iresult s' (finalize_funcall fd s')).
case h': finalize_funcall => [fs' | e].
- apply: rutt_Ret; split=> //; by exists s'.
apply: rutt_Vis => //; split=> //; by exists erefl.
Qed.

End ISEM_FINALIZE.

Section ITREE.

Lemma safe_bind E R1 R2 is_error t (k : R1 -> itree E R2) :
  safe is_error t ->
  (forall r, safe is_error (k r)) ->
  safe is_error (let* r := t in k r).
Proof. move=> ht hk; apply: (lutt_bind ht) => t1 _; exact: hk. Qed.
End ITREE.

Section WORD.

Lemma wunsigned_inj' ws (x y : word ws) :
  (wunsigned x == wunsigned y) = (x == y).
Proof.
case: (x =P y) => [<-|h]; first by rewrite eqxx.
by apply/eqP => /wunsigned_inj.
Qed.

Lemma lt_succ_r (x y : Z) : (x < Z.succ y) = (x <= y).
Proof. by case: lezP => /Z.lt_succ_r /ltzP // /negPf. Qed.

Lemma count_ziota (n m x : Z) :
  count (pred1 x) (ziota n m) = (n <= x < n + m).
Proof.
case: (Z.le_ge_cases m 0).
- by rewrite -in_ziota => /ziota_neg ->.
move: m; apply: natlike_ind => [|m hm hind]. (* TODO why not elim? *)
- by rewrite -in_ziota.
rewrite ziotaS_cat // count_cat hind /= addn0 Z.add_succ_r lt_succ_r
  [in x <= _]le_eqVlt eq_sym.
case: (x =P n + m); lia.
Qed.

Context {ws : wsize}.

Definition enum_word := map (wrepr ws) (ziota 0 (wbase ws)).

Lemma word_enumP : Finite.axiom enum_word.
Proof.
move=> b.
rewrite count_map (eq_in_count (a2 := pred1 (wunsigned b))).
- rewrite count_ziota; by have [/lezP -> /ltzP /= ->] := wunsigned_range b.
move=> /= x; rewrite in_ziota => /andP [/lezP ? /ltzP ?].
by rewrite -wunsigned_inj' wunsigned_repr_small.
Qed.

(* TODO warning?? *)
HB.instance Definition _ := [Countable of (word ws) by <: ].
HB.instance Definition _ := isFinite.Build (word ws) word_enumP.

End WORD.

Definition arr_is_def (n : positive) (a : WArray.array n) : bool :=
  all (WArray.is_init a) (ziota 0 n).

Section WSEQ.

Definition wseq := seq u8.

Definition dummy_wseq : wseq := [::].

Definition wseq_of_arr (len : positive) (a : WArray.array len) : wseq :=
  rdflt [::] (mapM (WArray.get8 a) (ziota 0 len)).

Section READ_WRITE.

  Context {pd : PointerData}.

  Definition read8 m p i := CoreMem.read m Aligned (p + wrepr Uptr i)%R U8.

  Definition write8 m p i (b : u8) :=
    CoreMem.write m Aligned (p + wrepr Uptr i)%R b.

  Definition read_wseq m p len : wseq :=
    rdflt [::] (mapM (read8 m p) (ziota 0 len)).

  Definition write_wseq m p (bs : wseq) : mem :=
    rdflt m (fill_mem m p bs).

End READ_WRITE.

Section PD.

Context {pd : PointerData}.

Lemma write_wseq_stack_stable {m p bytes} :
  stack_stable m (write_wseq m p bytes).
Proof.
rewrite /write_wseq; case h: fill_mem => //; exact: fill_mem_stack_stable h.
Qed.

Lemma write_wseq_validw_eq m p bytes :
  validw m =3 validw (write_wseq m p bytes).
Proof.
rewrite /write_wseq; case h: fill_mem => [m'|//]; exact: fill_mem_validw_eq h.
Qed.

Lemma write_wseq_disjoint m p bytes al p' ws :
  disjoint_zrange p (Z.of_nat (size bytes)) p' (wsize_size ws) ->
  read m al p' ws = read (write_wseq m p bytes) al p' ws.
Proof.
rewrite /write_wseq; by case h: fill_mem => [m'|//] /(fill_mem_disjoint h).
Qed.

(* TODO useful in stackalloc? the lemma with the same name has more premises *)
Lemma fill_fill_mem (n : positive) a m p bytes :
  (forall k : Z, 0 <= k < n -> validw m Aligned (p + wrepr _ k)%R U8) ->
  WArray.fill n bytes = ok a ->
  exists m', fill_mem m p bytes = ok m'.
Proof.
move=> hv; rewrite /WArray.fill /fill_mem.
t_xrbindP=> /eqP hn [? a'] hfold /= ?; subst a'.
elim: bytes m 0 (WArray.empty n) {hn} hv hfold => [|b bytes hind] m z a0 hv /=;
  first by exists m.
t_xrbindP=> _ a' hset <- /hind {}hind.
move: hset => /WArray.set_bound.
rewrite WArray.mk_scale_U8 Z.mul_1_r wsize8 => -[h1 h2 _].
suff [m0 hm0] :
  exists m0, [elaborate write m Aligned (p + wrepr Uptr z)%R b = ok m0 ].
- rewrite hm0; apply: hind => k hk.
  rewrite (write_validw_eq hm0); apply: hv; lia.
apply/writeV.
rewrite /validw /= is_align8 (valid8_validw _ Aligned) andbT /= add_0.
apply: hv; lia.
Qed.

Lemma read_write_wseq bytes (n : positive) a (i : Z) w p m :
  (Zpos n <= wbase Uptr) ->
  (forall k : Z, 0 <= k < n -> validw m Aligned (p + wrepr _ k)%R U8) ->
  WArray.fill n bytes = ok a ->
  read a Aligned i U8 = ok w ->
  read (write_wseq m p bytes) Aligned (p + wrepr Uptr i)%R U8 = ok w.
Proof.
move=> hn hv ha; have [m' hm'] := fill_fill_mem hv ha.
rewrite (WArray.fill_get8 ha) /write_wseq hm' /= (fill_mem_read8 _ hm') /=
  -(WArray.fill_size ha); last lia.
case: andP => // -[??] <-.
rewrite subE -{2 4 6}(GRing.addr0 p) (GRing.addrC p (wrepr _ _)) GRing.addrKA
  GRing.subr0 wunsigned_repr_small; last lia.
case: ifP => //; lia.
Qed.

End PD.

Section EP.

Context {syscall_state : Type} {ep : EstateParams syscall_state}.

Lemma wseq_in_mem m n (a : WArray.array n) p :
  arr_is_def a ->
  value_in_mem m (Varr a) (Vword p) ->
  wseq_of_arr a = read_wseq m p n.
Proof.
move=> hdef [_ [[/= <- h]]].
rewrite /wseq_of_arr /read_wseq.
have {}hdef :
  forall i : Z,
    i \in ziota 0 n ->
    exists2 w,
      WArray.get8 a i = ok w &
      read m Aligned (p + wrepr Uptr i)%R U8 = ok w.
- move=> i hi.
  have [|w hw] := elimT (valid_getP a i).
  + apply/andP; split; last by move: hdef => /allP /(_ _ hi).
    apply/WArray.in_boundP; rewrite in_ziota in hi; lia.
  exists w => //; apply: h.
  by rewrite /read /= is_align8 /= add_0 hw /= decode_u8.
f_equal; elim: ziota hdef => //= x xs hind hdef.
move: (hdef x); rewrite in_cons eqxx /read8 => /(_ erefl) [w -> ->].
rewrite hind // => i hi; apply: hdef; by rewrite in_cons hi orbT.
Qed.

Lemma write_wseq_wf_ptr_arg
  {gsz rip ms mt p bytes wptrs vs vt writable ws v p' i} :
  let: mt' := write_wseq mt p bytes in
  wf_arg_pointer gsz rip ms mt wptrs vs vt writable ws v p' i ->
  wf_arg_pointer gsz rip ms mt' wptrs vs vt writable ws v p' i.
Proof.
rewrite /write_wseq; case h: fill_mem => [m'|] //=.
move=> [?? hvalid ???]; split=> // w hw.
by rewrite -(fill_mem_validw_eq h) (hvalid _ hw).
Qed.

Lemma write_wseq_wf_arg {gsz rip ms mt p bytes wptrs vs vt ws i} :
  wf_arg gsz rip ms mt wptrs ws vs vt i ->
  wf_arg gsz rip ms (write_wseq mt p bytes) wptrs ws vs vt i.
Proof.
rewrite /wf_arg; case: nth => // b [p' [-> h]]; exists p'; split=> //.
exact: write_wseq_wf_ptr_arg.
Qed.

Lemma write_wseq_it_wf_args {gsz rip ms mt p bytes wptrs vs vt ws} :
  wf_args gsz rip ms mt wptrs ws vs vt ->
  wf_args gsz rip ms (write_wseq mt p bytes) wptrs ws vs vt.
Proof. move=> h i; exact: write_wseq_wf_arg (h i). Qed.

Lemma write_wseq_extend_mem ms mt rip gd p a :
  let: n := Z.of_nat (size a) in
  n <= wbase Uptr ->
  disjoint_zrange p n rip (Z.of_nat (size gd)) ->
  (forall w, validw ms Aligned w U8 -> disjoint_zrange p n w 1) ->
  extend_mem ms mt rip gd ->
  extend_mem ms (write_wseq mt p a) rip gd.
Proof.
move=> hsz hrip hdisj; rewrite /write_wseq; case hm': fill_mem => [m'|//] /=.
move=> [?? hold ? hv hgd]; split=> //.
- move=> x hx; rewrite (hold _ hx) (fill_mem_disjoint hm') //; exact: hdisj hx.
- move=> x /hv; by rewrite (fill_mem_validw_eq hm').
move=> x hx; rewrite -(hgd _ hx); apply: (fill_mem_disjoint hm').
exact: disjoint_zrange_byte hrip hx.
Qed.

End EP.

End WSEQ.

Section WVEC.

Definition wvec (n : nat) : Type := 'rV[u8]_n.
Definition mkwvec (n : nat) (s : seq u8) : wvec n := \row_i nth 0%R s i.
Definition dummy_wvec (n : nat) : wvec n := \row_i 0%R.

Coercion wseq_of_wvec (n : nat) (v : wvec n) : wseq :=
  [seq v ord0 i | i <- enum 'I_n ].

Definition wvec_of_arr n (a : WArray.array n) : wvec n :=
  mkwvec n (wseq_of_arr a).

Definition read_wvec {_ : PointerData} m p (len : positive) : wvec len :=
  mkwvec len (read_wseq m p len).

Definition wvec_of_val (n : positive) (v : value) : wvec n :=
  if to_arr n v is Ok a then wvec_of_arr a else dummy_wvec n.

End WVEC.

Section MAIN.

Context
  {R : realType}
  (advmem : Type) (* Adversary's memory. *)
.

Instance sc_sem : syscall.syscall_sem unit :=
  {| syscall.get_random := fun _ _ => (tt, [::]); |}.

Definition E := ErrEvent +' RndEvent unit.
Existing Instance with_Error0.
Existing Instance RndE00.

Definition handleE : RndEvent unit ~> itree (distr.Rnd (R := R)) :=
  fun _ '(Rnd _ len) =>
    let* bs := unif_seq (T := u8) (Z.to_nat len) in
    Ret (tt, bs).

Definition translateE : itree (RndEvent unit) ~> itree distr.Rnd :=
  fun _ t => interp handleE t.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {call_conv : calling_convention}
  {asm_scsem : asm_syscall_sem}
  {lowering_options : Type}
  (aparams : architecture_params lowering_options)
  (haparams : h_architecture_params aparams)
  (cparams : compiler_params lowering_options)
  (print_uprogP : forall s p, cparams.(print_uprog) s p = p)
  (print_sprogP : forall s p, cparams.(print_sprog) s p = p)
.

(* Not all of the implicits are always needed. *)
Let isemS (p : uprog) :=
  isem_fun
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (sip := sip_of_asm_e)
    (scP := sCP_unit)
    (E := E)
    (wsw := nosubword)
    (dc := indirect_c)
    (pT := progUnit)
    p tt.

Let isemT (q : sprog) (rip : pointer) :=
  isem_fun
    (asm_op := extended_op)
    (ep := ep_of_asm_e)
    (spp := spp_of_asm_e)
    (sip := sip_of_asm_e)
    (scP := sCP_stack)
    (E := E)
    (wsw := withsubword)
    (dc := direct_c)
    (pT := progStack)
    q rip.

Context (
  pkbytes (* MLKEM_INDCPA_PUBLICKEYBYTES *)
  skbytes (* KYBER_INDCPA_SECRETKEYBYTES *)
  ctbytes (* KYBER_INDCPA_BYTES *)
  msgbytes (* MLKEM_INDCPA_MSGBYTES *)
  : positive
).

Notation KEM_Challenger :=
  (Challenger
     (R := R)
     (pkey := wseq)
     (skey := wseq)
     (ciphert := wseq)
     (msg := wvec msgbytes)).

Notation KEM_Adversary :=
  (Adversary
     (R := R)
     (pkey := wseq)
     (advmem := advmem)
     (ciphert := wseq)
     (msg := wvec msgbytes)).

Section DEFS.

Context
  (p : uprog)
  (q : sprog)
  (rip : word Uptr)
  (fn_genkey fn_encap fn_decap : funname)
.

(* Abstractly, the signatures are as follows:
   genkey : () -> u8[MLKEM_INDCPA_PUBLICKEYBYTES] * u8[KYBER_INDCPA_SECRETKEYBYTES]
   encap : u8[MLKEM_INDCPA_PUBLICKEYBYTES] -> u8[KYBER_INDCPA_BYTES] * u8[MLKEM_INDCPA_MSGBYTES]
   decap : u8[KYBER_INDCPA_SECRETKEYBYTES] -> u8[KYBER_INDCPA_BYTES] -> u8[KYBER_INDCPA_MSGBYTES]
  *)

Definition pubkey := WArray.array pkbytes.
Definition seckey := WArray.array skbytes.
Definition ciphert := WArray.array ctbytes.
Definition msg := WArray.array msgbytes.

Definition pk_of_w := WArray.fill pkbytes.
Definition sk_of_w := WArray.fill skbytes.
Definition ct_of_w := WArray.fill ctbytes.

Definition dummyp := WArray.empty pkbytes.
Definition dummys := WArray.empty skbytes.
Definition dummyc := WArray.empty ctbytes.
Definition dummym := WArray.empty msgbytes.

Definition dummy2 : wseq * wseq := (dummy_wseq, dummy_wseq).
Definition dummymsg : wvec msgbytes := dummy_wvec _.

Section SEM.
  Context (m : mem).

  Let fs_of_vals vs : fstate := {| fscs := tt; fmem := m; fvals := vs; |}.

  Definition fsS_GenKey := fs_of_vals [:: Varr dummyp; Varr dummys ].
  Definition fsS_Encap (pk : pubkey) :=
    fs_of_vals [:: Varr dummyc; Varr dummym; Varr pk ].
  Definition fsS_Decap (sk : seckey) (ct : ciphert) :=
    fs_of_vals [:: Varr dummym; Varr ct; Varr sk ].

  Definition fsT_GenKey (ppk psk : pointer) :=
    fs_of_vals [:: Vword ppk; Vword psk ].
  Definition fsT_Encap (ppk pct pmsg : pointer) (pk : wseq) :=
    {|
      fscs := tt;
      fmem := write_wseq m ppk pk;
      fvals := [:: Vword pct; Vword pmsg; Vword ppk ];
    |}.
  Definition fsT_Decap (psk pct pmsg : pointer) (sk ct : wseq) :=
    let m' := write_wseq m psk sk in
    {|
      fscs := tt;
      fmem := write_wseq m' pct ct;
      fvals := [:: Vword pmsg; Vword pct; Vword psk ];
    |}.

  Definition get_res (n : positive) (vs : seq value) (i : nat) : wvec n :=
    nth (Vint 0) vs i |> wvec_of_val n.

  (* Implementation signature:
       (u8[pkbytes], u8[skbytes]) -> u8[pkbytes], u8[skbytes] *)
  Definition semS_GenKey :=
    let* fs' := isemS p fn_genkey fsS_GenKey |> interp_Err in
    if fs' is ESok fs' then
      let p := get_res pkbytes (fvals fs') 0 in
      let s := get_res skbytes (fvals fs') 1 in
      Ret (p : wseq, s : wseq)
    else Ret (dummy_wseq, dummy_wseq).

  (* Implementation signature:
       (u8[ctbytes], u8[msgbytes], u8[pkbytes]) -> u8[ctbytes], u8[msgbytes] *)
  Definition semS_Encap pk :=
    if pk_of_w pk is Ok pk then (* TODO pk should be a wvec *)
      let fs := fsS_Encap pk in
      let* fs' := isemS p fn_encap fs |> interp_Err in
      if fs' is ESok fs' then
        let m := get_res msgbytes (fvals fs') 1 in
        let c := get_res ctbytes (fvals fs') 0 in
        Ret (m, c : wseq)
      else Ret (dummymsg, dummy_wseq)
    else Ret (dummymsg, dummy_wseq).

  (* TODO how does the implementation signal a failure? *)
  (* Implementation signature:
       (u8[msgbytes], u8[ctbytes], u8[skbytes]) -> u8[msgbytes] *)
  Definition semS_Decap sk ct :=
    match sk_of_w sk, ct_of_w ct with
    | Ok sk, Ok ct =>
        let fs := fsS_Decap sk ct in
        let* fs' := isemS p fn_decap fs |> interp_Err in
        if fs' is ESok fs' then Ret (Some (get_res msgbytes (fvals fs') 0))
        else Ret None
    | _, _ => Ret None
    end.

  Definition semT_GenKey ppk psk :=
    let fs := fsT_GenKey ppk psk in
    let* fs' := isemT q rip fn_genkey fs |> interp_Err in
    if fs' is ESok fs' then
      let pk := read_wvec (fmem fs') ppk pkbytes in
      let sk := read_wvec (fmem fs') psk skbytes in
      Ret (pk : wseq, sk : wseq)
    else Ret (dummy_wseq, dummy_wseq).

  (* TODO pk should be a wvec *)
  Definition semT_Encap ppk pct pmsg pk :=
    if pk_of_w pk is Error _ then Ret (dummymsg, dummy_wseq)
    else
      let fs := fsT_Encap ppk pct pmsg pk in
      let* fs' := isemT q rip fn_encap fs |> interp_Err in
      if fs' is ESok fs' then
        let ct := read_wvec (fmem fs') pct ctbytes in
        let msg := read_wvec (fmem fs') pmsg msgbytes in
        Ret (msg, ct : wseq)
      else Ret (dummymsg, dummy_wseq).

  (* TODO we should check that the function didn't fail. *)
  Definition semT_Decap psk pct pmsg sk ct :=
    if sk_of_w sk is Error _ then Ret None
    else if ct_of_w ct is Error _ then Ret None
    else
      let fs := fsT_Decap psk pct pmsg sk ct in
      let* fs' := isemT q rip fn_decap fs |> interp_Err in
      if fs' is ESok fs' then Ret (Some (read_wvec (fmem fs') pmsg msgbytes))
      else Ret None.

  Definition Challenger_of_S : KEM_Challenger :=
    {|
      GenKey := translateE semS_GenKey;
      Encap := fun pk => translateE (semS_Encap pk);
      Decap := fun sk ct => translateE (semS_Decap sk ct);
    |}.

  Definition Challenger_of_T ppk psk pct pmsg : KEM_Challenger :=
    {|
      GenKey := translateE (semT_GenKey ppk psk);
      Encap := fun pk => translateE (semT_Encap ppk pct pmsg pk);
      Decap := fun sk ct => translateE (semT_Decap psk pct pmsg sk ct);
    |}.

End SEM.

(* Safety means:
 1. Jasmin safety (defined with lutt).
 2. Output arrays are defined (can be added to lutt).
 3. There exists a target memory and some pointers that can fit all the
    arguments, results, and global variables
    (a statement on the program and what the compiler decides about its stack
    usage, typically shouldn't be called "safety" but a different requirement
    on the compiler theorem to apply). *)

Definition safe_uprog fn fs := safe (is_error (with_Error0)) (isemS p fn fs).

Definition val_is_def (v : value) : bool :=
  if v is Varr _ a then arr_is_def a else is_defined v.

(* TODO why does lutt involve an exists instead of saying t ~ t? *)
Definition res_defined fn fs :=
  lutt
    (E := E)
    (fun T e => True)
    (fun T e r => True)
    (fun fs => all val_is_def (fvals fs))
    (isemS p fn fs).

Definition total_stack fd :=
  let: e := fd.(f_extra) in
  e.(sf_stk_max) + wsize_size e.(sf_align) - 1.

Record ok_fun fn ufd sfd ms mt args argt :=
  {
    (* [ufd] is the definition of [fn]. *)
    ok_fun_ufd : get_fundef (p_funcs p) fn = Some ufd;

    (* [sfd] is the definition of the compilation of [fn]. *)
    (* TODO this should come from compiler_meta *)
    ok_fun_sfd : get_fundef (p_funcs q) fn = Some sfd;

    (* There's enough stack space in the target memory. *)
    ok_fun_space :
      let: stk_sz := wunsigned (top_stack mt) - wunsigned (stack_limit mt) in
      (0 <= total_stack sfd <= stk_sz)%Z;

    (* The arguments are well formed. *)
    ok_fun_args : it_wf_args p q rip fn ms mt args argt;

    (* The return address is not on the stack or in a register. *)
    (* TODO can we derive this because it's in entries? *)
    ok_fun_ra : is_RAnone (sf_return_address (f_extra sfd));
  }.

End DEFS.

Section THEOREM.

Context
  (entries : seq funname)
  (up : uprog)
  (sp : sprog) (rip : pointer)
  (fn_genkey fn_encap fn_decap : funname)
  (ufd_genkey ufd_encap ufd_decap : ufundef)
  (sfd_genkey sfd_encap sfd_decap : sfundef)
  (ms mt : mem) (* TODO maybe each function should have their own memory *)
  (ppk psk pct pmsg : pointer) (* TODO each function should have its own
                                  pointers *)
.

Context
  (* These are necessary to be able to write the values in memory. *)
  (* TODO these should come from the disjointedness or wf_arg_pointer *)
  (small_pkbytes : (pkbytes : Z) <= wbase Uptr)
  (small_skbytes : (skbytes : Z) <= wbase Uptr)
  (small_ctbytes : (ctbytes : Z) <= wbase Uptr)

  (hcomp : compiler_front_end aparams cparams entries up = ok sp)

  (export_genkey : fn_genkey \in entries)
  (export_encap : fn_encap \in entries)
  (export_decap : fn_decap \in entries)

  (* TODO argument and result variables should be different *)
  (sig_genkey:
    exists pk sk,
      [/\ f_params ufd_genkey = [:: pk; sk ]
        , f_res ufd_genkey = [:: pk; sk ]
        , f_tyout ufd_genkey = [:: sarr pkbytes; sarr skbytes ]
        , wptr_status pk = Some true
        & wptr_status sk = Some true
  ])

  (sig_encap:
    exists pk ct msg,
      [/\ f_params ufd_encap = [:: ct; msg; pk ]
        , f_res ufd_encap = [:: ct; msg ]
        , f_tyout ufd_encap = [:: sarr ctbytes; sarr msgbytes ]
        , wptr_status pk = Some false
        , wptr_status ct = Some true
        & wptr_status msg = Some true
  ])

  (sig_decap:
    exists sk ct msg,
      [/\ f_params ufd_decap = [:: msg; ct; sk ]
        , f_res ufd_decap = [:: msg ]
        , f_tyout ufd_decap = [:: sarr msgbytes ]
        , wptr_status sk = Some false
        , wptr_status ct = Some false
        & wptr_status msg = Some true
  ])

  (* This is only needed in the algorithms where the pointers are not writable,
     since otherwise we have [wf_arg_pointer].
     TODO [wf_arg_pointer] only ensures this when [size_glob sp > 0], why?
     TODO can we derive this from [wf_arg_pointer] given that they are writable
     arguments to some of the functions? *)
  (ppk_not_rip : disjoint_zrange rip (size_glob sp) ppk pkbytes)
  (pct_not_rip : disjoint_zrange rip (size_glob sp) pct ctbytes)
  (psk_not_rip : disjoint_zrange rip (size_glob sp) psk skbytes)

  (* Only needed in Decap. *)
  (* Really we only need to know that reading from these pointers after writing
     gives us the right values, not that they are disjoint. *)
  (pct_not_psk : disjoint_zrange pct ctbytes psk skbytes)

  (* GenKey is safe on the source memory. *)
  (ok_safe_genkey : safe_uprog up fn_genkey (fsS_GenKey ms))

  (* Encap is safe on the source memory for every public key argument. *)
  (ok_safe_encap : forall pk, safe_uprog up fn_encap (fsS_Encap ms pk))

  (* Decap is safe on the source memory for every ciphertext and secret key
     arguments. *)
  (ok_safe_decap : forall sk ct, safe_uprog up fn_decap (fsS_Decap ms sk ct))

  (* GenKey initializes the entire output arrays. *)
  (ok_defined_genkey : res_defined up fn_genkey (fsS_GenKey ms))

  (* Encap initializes the entire output arrays for any public key
     argument. *)
  (ok_defined_encap : forall pk, res_defined up fn_encap (fsS_Encap ms pk))

  (* Decap initializes the entire output array for every ciphertext and secret
     key arguments. *)
  (ok_defined_decap :
    forall sk ct, res_defined up fn_decap (fsS_Decap ms sk ct))

  (* The target memory coincides with the source one and allocates the global
     data. *)
  (* TODO: Should we write the global data ourselves? *)
  (ok_extend_mem : it_extend_mem sp rip ms mt)

  (* GenKey is defined and [ppk] and [psk] are valid pointers. *)
  (ok_genkey :
    let: args := [:: Varr dummyp; Varr dummys ] in
    let: argt := [:: Vword ppk; Vword psk ] in
    ok_fun up sp rip fn_genkey ufd_genkey sfd_genkey ms mt args argt)

  (* Encap is defined and [pct], [pmsg], and [ppk]  are valid pointers. *)
  (ok_encap :
    forall pk : pubkey,
      let: args := [:: Varr dummyc; Varr dummym; Varr pk ] in
      let: argt := [:: Vword pct; Vword pmsg; Vword ppk ] in
      ok_fun up sp rip fn_encap ufd_encap sfd_encap ms mt args argt)

  (* Decap is defined and [pmsg], [pct], and [psk] are valid pointers. *)
  (ok_decap :
    forall (sk : seckey) (ct : ciphert),
      let: args := [:: Varr dummym; Varr ct; Varr sk ] in
      let: argt := [:: Vword pmsg; Vword pct; Vword psk ] in
      ok_fun up sp rip fn_decap ufd_decap sfd_decap ms mt args argt)
.

(* Used to combine the compiler correctness result with safety and the condition
   on defined results. *)
Definition aux_post fn (s t s' t' : fstate) :=
  let: n := get_nb_wptr up fn in
  let: argt := fvals t in
  let: ress := fvals s' in
  [/\ List.Forall2 (value_in_mem (fmem t')) (take n ress) (take n argt)
    , all val_is_def ress
    & forall fd,
        get_fundef (p_funcs up) fn = Some fd ->
        is_finalize (pT := progUnit) (wsw := nosubword) (scP := sCP_unit)
          (dc := indirect_c) fd s'
  ].

Definition REeq {E : Type -> Type} A1 A2 (e1: E A1) (e2: E A2) :=
  exists h : A2 = A1, e1 = eq_rect A2 E e2 A1 h.

Definition RAeq
  {E : Type -> Type} A1 A2 (e1: E A1) (a1: A1) (e2: E A2) (a2: A2) :=
  JMeq a1 a2.

#[local]
Instance _eS : EquivSpec := FrontEndEquiv up sp rip.

Lemma correct_comp {fn fd s t} :
  fn \in entries ->
  get_fundef (p_funcs up) fn = Some fd ->
  safe_uprog up fn s ->
  res_defined up fn s ->
  rpreF fn fn s t ->
  eutt (aux_post fn s t) (isemS up fn s) (isemT sp rip fn t).
Proof.
move=> hfn hfd hsafe hdef hpre.
apply/simple_rutt_eutt/(safe_xrutt_rutt hsafe).
apply: (lutt_xrutt_trans_l'
  (REv := EPreRel_safe (is_error with_Error0) REeq)
  (RAns := RAeq)
  (RR := fun s' t' => all val_is_def (fvals s') /\ rpostF fn fn s t s' t'));
  cycle -2.
- exact: (isem_fun_finalize (scP := sCP_unit)) hfd.
- apply: (lutt_xrutt_trans_l'
    (REv := EPreRel (rE0 := HandlerContract))
    (RAns := EPostRel (rE0 := HandlerContract))); cycle -2.
  + exact: hdef.
  + exact: (it_compiler_front_endP
              haparams print_uprogP print_sprogP hcomp hfn hpre).
  + move=> T1 T2 [|[[] n1]]; first by left.
    move=> [//|[[] _]] _ [_ <-]; right; by exists erefl.
  + move=> T1 T2 [//|e1] r1 [//|e2] r2 _ _ [] _.
    destruct e1 as [[] n1]; destruct e2 as [[] n2].
    by move=> /(JMeq_eq (x := r1)) <-.
  done.
- done.
- done.
move=> s' t' hfin [{}hdef [res_in_mem _ _ _ _]].
split=> //; by rewrite hfd => _ [<-].
Qed.

Lemma pre_GenKey :
  rpreF fn_genkey fn_genkey (fsS_GenKey ms) (fsT_GenKey mt ppk psk).
Proof.
have [ok_ufd_genkey ok_sfd_genkey ok_alloc wf_args ok_ra] := ok_genkey.
split=> //.
- move=> fd; rewrite ok_sfd_genkey => -[?]; subst fd.
  rewrite /stack_alloc_proof_2.sf_total_stack ok_ra; by split.
rewrite /get_wptrs ok_ufd_genkey /=.
have [var_pk [var_sk [-> _ _ /= -> ->]]] := sig_genkey.
constructor; last constructor; last by constructor.
- exists ppk; split=> //= i w; by rewrite WArray.get_empty -fun_if.
exists psk; split=> //= i w; by rewrite WArray.get_empty -fun_if.
Qed.

(* TODO This proof is the same for the three algorithms. I could not come up
   with the usual generic statement using List.Forall and nth. *)
Lemma eutt_GenKey :
  eutt eq
    (semS_GenKey up fn_genkey ms)
    (semT_GenKey sp rip fn_genkey mt ppk psk).
Proof.
have [hfd _ _ _ _] := ok_genkey.
rewrite /semS_GenKey /semT_GenKey.
apply: (eutt_clo_bind (exec_rel (aux_post fn_genkey _ _))).
- apply/interp_exec_eutt/(correct_comp _ hfd) => //; exact: pre_GenKey.
move=> [s'|?] [t'|?] => //; last reflexivity.
move=> [] /[swap] hdef /[swap] /(_ _ hfd) [] st.
rewrite /finalize_funcall /get_nb_wptr /get_wptrs /= hfd /=.
have [var_pk [var_sk [-> -> -> /= -> ->]]] /= := sig_genkey.
t_xrbindP=> _ vpk0 hpk0 _ vsk0 hsk0 <- <-.
t_xrbindP=>
  _ vpk1 /truncate_val_typeE [apk ??]
  _ vsk1 /truncate_val_typeE [ask ??]
  _ <- <- <- ?;
  subst vpk0 vpk1 vsk0 vsk1 s'.
move: hdef => /andP /[!andbT] /= -[defpk defsk].
move=> /List_Forall2_inv [] pk_mem /List_Forall2_inv [] sk_mem _.
rewrite /get_res /= /wvec_of_val /= !WArray.castK /wvec_of_arr
  (wseq_in_mem defpk pk_mem) (wseq_in_mem defsk sk_mem).
reflexivity.
Qed.

Lemma pre_Encap pk apk :
  pk_of_w pk = ok apk ->
  rpreF fn_encap fn_encap (fsS_Encap ms apk) (fsT_Encap mt ppk pct pmsg pk).
Proof.
move=> hpk.
have [ok_ufd_encap ok_sfd_encap ok_alloc wf_args ok_ra] := ok_encap apk.
move: (wf_args 2%N); rewrite /= /wf_arg /get_wptrs ok_ufd_encap /=.
have [var_pk [var_ct [var_msg [-> _ _ /= -> -> ->]]]] := sig_encap.
move=> [_ [[<-] [_ hov hv hdisj _ _]]].
split=> //.
- move=> fd; rewrite ok_sfd_encap => -[?]; subst fd.
  rewrite /stack_alloc_proof_2.sf_total_stack ok_ra; split=> //=.
  rewrite /allocatable_stack -(ss_top_stack (a := mt));
    last exact: write_wseq_stack_stable.
  rewrite -(ss_limit (m := mt)) //; exact: write_wseq_stack_stable.
- exact: write_wseq_it_wf_args wf_args.
- constructor; last constructor; last constructor; last by constructor.
  + exists pct; split=> //= i w; by rewrite WArray.get_empty -fun_if.
  + exists pmsg; split=> //= i w; by rewrite WArray.get_empty -fun_if.
  exists ppk; split=> //= i w hw.
  apply: (read_write_wseq small_pkbytes _ hpk hw).
  move=> k hk; apply: hv; apply: (between_byte hov); first exact: zbetween_refl.
  by rewrite !(rwP ltzP, rwP lezP) (rwP andP) hk.
apply: write_wseq_extend_mem (ok_extend_mem);
  rewrite -(WArray.fill_size hpk) positive_nat_Z.
- exact: small_pkbytes.
- rewrite -/(size_glob sp); exact/disjoint_zrange_sym/ppk_not_rip.
exact: hdisj.
Qed.

Lemma eutt_Encap {pk} :
  eutt eq
    (semS_Encap up fn_encap ms pk)
    (semT_Encap sp rip fn_encap mt ppk pct pmsg pk).
Proof.
rewrite /semS_Encap /semT_Encap; case hpk: pk_of_w => [apk|]; last reflexivity.
have [hfd _ _ _ _] := ok_encap apk.
apply: (eutt_clo_bind (exec_rel (aux_post fn_encap _ _))).
- apply/interp_exec_eutt/(correct_comp _ hfd) => //; exact: pre_Encap hpk.
move=> [s'|?] [t'|?] => //; last reflexivity.
move=> [] /[swap] hdef /[swap] /(_ _ hfd) [] st.
rewrite /finalize_funcall /get_nb_wptr /get_wptrs /= hfd /=.
have [var_pk [var_ct [var_msg [-> -> -> /= -> -> ->]]]] /= := sig_encap.
t_xrbindP=> _ vct0 hct0 _ vmsg0 hmsg0 <- <-.
t_xrbindP=>
  _ vct1 /truncate_val_typeE [act ??]
  _ vmsg1 /truncate_val_typeE [amsg ??]
  _ <- <- <- ?;
  subst vct0 vct1 vmsg0 vmsg1 s'.
move: hdef => /andP /[!andbT] /= -[defct defmsg].
move=> /List_Forall2_inv [] ct_mem /List_Forall2_inv [] msg_mem _.
rewrite /get_res /= /wvec_of_val /= !WArray.castK /wvec_of_arr
  (wseq_in_mem defct ct_mem) (wseq_in_mem defmsg msg_mem).
reflexivity.
Qed.

Lemma pre_Decap sk ct ask act :
  sk_of_w sk = ok ask ->
  ct_of_w ct = ok act ->
  rpreF fn_decap fn_decap
    (fsS_Decap ms ask act) (fsT_Decap mt psk pct pmsg sk ct).
Proof.
move=> hsk hct.
have [ok_ufd_decap ok_sfd_decap ok_alloc wf_args ok_ra] :=
  ok_decap ask act.
move: (wf_args 1%N) (wf_args 2%N);
  rewrite /= /wf_arg /get_wptrs ok_ufd_decap /=.
have [var_sk [var_ct [var_msg [-> _ _ /= -> -> ->]]]] := sig_decap.
move=> [_ [[<-] [_ ct_ov ct_v ct_disj _ _]]]
  [_ [[<-] [_ sk_ov sk_v sk_disj _ _]]].
split=> //.
- move=> fd; rewrite ok_sfd_decap => -[?]; subst fd.
  rewrite /stack_alloc_proof_2.sf_total_stack ok_ra; split=> //=.
  rewrite /allocatable_stack -(ss_top_stack (a := mt)); last first.
  - transitivity (write_wseq mt psk sk); exact: write_wseq_stack_stable.
  rewrite -(ss_limit (m := mt)) //.
  transitivity (write_wseq mt psk sk); exact: write_wseq_stack_stable.
- exact/write_wseq_it_wf_args/(write_wseq_it_wf_args wf_args).
- constructor; last constructor; last constructor; last by constructor.
  + exists pmsg; split=> //= i w; by rewrite WArray.get_empty -fun_if.
  + exists pct; split=> //= i w hw.
    apply: (read_write_wseq small_ctbytes _ hct hw).
    move=> k hk; rewrite -(write_wseq_validw_eq); apply: ct_v.
    apply: (between_byte ct_ov); first exact: zbetween_refl.
    by rewrite !(rwP ltzP, rwP lezP) (rwP andP) hk.
  exists psk; split=> //= i w hw.
  rewrite -(write_wseq_disjoint (write_wseq mt _ _)); first last.
  + rewrite -(WArray.fill_size hct) positive_nat_Z.
    apply: (disjoint_zrange_byte pct_not_psk).
    (* TODO [read = ok -> in_bound ] should be a lemma *)
    rewrite -(WArray.get8_read _ AAdirect) in hw.
    have [+ + _] := WArray.get_bound hw.
    rewrite /= /wsize_size; lia.
  apply: (read_write_wseq small_skbytes _ hsk hw) => k hk.
  apply: sk_v; apply: (between_byte sk_ov); first exact: zbetween_refl.
  by rewrite !(rwP ltzP, rwP lezP) (rwP andP) hk.
apply: write_wseq_extend_mem; rewrite -?(WArray.fill_size hct) ?positive_nat_Z.
- exact: small_ctbytes.
- rewrite -/(size_glob sp); exact/disjoint_zrange_sym/pct_not_rip.
- exact: ct_disj.
apply: write_wseq_extend_mem (ok_extend_mem);
  rewrite -(WArray.fill_size hsk) positive_nat_Z.
- exact: small_skbytes.
- rewrite -/(size_glob sp); exact/disjoint_zrange_sym/psk_not_rip.
exact: sk_disj.
Qed.

Lemma eutt_Decap {sk c} :
  eutt eq
    (semS_Decap up fn_decap ms sk c)
    (semT_Decap sp rip fn_decap mt psk pct pmsg sk c).
Proof.
rewrite /semS_Decap /semT_Decap.
case hsk: sk_of_w => [ask|]; last reflexivity.
case hct: ct_of_w => [act|]; last reflexivity.
have [hfd _ _ _ _] := ok_decap ask act.
apply: (eutt_clo_bind (exec_rel (aux_post fn_decap _ _))).
- apply/interp_exec_eutt/(correct_comp _ hfd) => //; exact: pre_Decap hsk hct.
move=> [s'|?] [t'|?] => //; last reflexivity.
move=> [] /[swap] hdef /[swap] /(_ _ hfd) [] st.
rewrite /finalize_funcall /get_nb_wptr /get_wptrs /= hfd /=.
have [var_sk [var_ct [var_msg [-> -> -> /= -> -> ->]]]] /= := sig_decap.
t_xrbindP=> _ vmsg0 hmsg0 <-.
t_xrbindP=> _ vmsg1 /truncate_val_typeE [amsg ??] _ <- <- ?;
  subst vmsg0 vmsg1 s'.
move: hdef => /= /[!andbT] defmsg.
move=> /List_Forall2_inv [] msg_mem _.
rewrite /get_res /= /wvec_of_val /= !WArray.castK /wvec_of_arr
  (wseq_in_mem defmsg msg_mem).
reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Generic *)

(* TODO How to make this into a rewrite? *)
Lemma eutt_translateE T (RR : T -> T -> Prop) :
  Proper (eutt RR ==> eutt RR) (translateE (T := T)).
Proof. exact: eutt_interp'. Qed.

Let C_s :=
  Challenger_of_S
    up
    fn_genkey fn_encap fn_decap
    ms.

Let C_t :=
  Challenger_of_T
    sp rip
    fn_genkey fn_encap fn_decap
    mt ppk psk pct pmsg.

Lemma handle_DecP T sk ex (e : (Dec +' distr.Rnd) T) :
  eutt eq (handle_Dec C_s sk ex e) (handle_Dec C_t sk ex e).
Proof.
move: T e => _ [[c] | []] /=; last reflexivity.
case: (_ == _); first reflexivity.
exact/eutt_translateE/eutt_Decap.
Qed.

Lemma interactP T (A : itree _ T) sk ex :
  eutt eq (interact C_s A sk ex) (interact C_t A sk ex).
Proof.
apply: eutt_interp; last reflexivity. move=> Y e; exact: handle_DecP.
Qed.

Theorem eutt_game {A : KEM_Adversary} : eutt eq (game C_s A) (game C_t A).
Proof.
rewrite /game /= (eutt_translateE eutt_GenKey).
apply: eutt_eq_bind => -[pk sk].
rewrite interactP; apply: eutt_eq_bind => l.
rewrite (eutt_translateE eutt_Encap); apply: eutt_eq_bind => -[m0 c].
apply: eutt_eq_bind => m1; apply: eutt_eq_bind => b.
rewrite interactP; reflexivity.
Qed.

Corollary deqX_game {A : KEM_Adversary} : dgame C_s A =1 dgame C_t A.
Proof. exact/dinterp_eutt/eutt_game. Qed.

Corollary reduction {A : KEM_Adversary} : advantage C_t A <= advantage C_s A.
Proof. by rewrite /advantage (eq_mu_pr _ deqX_game). Qed.

End THEOREM.

End MAIN.

(* TODO instantiate with x86? *)
