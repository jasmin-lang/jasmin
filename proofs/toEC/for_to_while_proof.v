From ITree Require Import ITree ITreeFacts.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From Coq Require Import ZArith Lia.
Require Import compiler_util psem psem_facts sem_op_typed_facts.
Require Import dead_code for_to_while.
Require dead_code_proof.

(* * Correctness of [for_to_while], from the transformed program to the source.

   The states are related by [st_eq_on] on the variables that are live in the
   source, as [dead_code] computes them: after a [for] loop whose index is not
   live, the indices of the two programs may differ. The fresh variables that
   hold the bounds are not variables of the function, hence never live. *)

Local Open Scope Z_scope.

Section LIVE.

Context {asm_op syscall_state : Type} {sip : SemInstrParams asm_op syscall_state}.

Lemma loop_live (f : Sv.t -> cexec (Sv.t * cmd)) ii n rx wx U sv0 sv1 c1 :
  (forall s s' c, f s = ok (s', c) -> Sv.Subset s' (Sv.union s U)) ->
  dead_code.loop f ii n rx wx sv0 = ok (sv1, c1) ->
  Sv.Subset sv1 (Sv.union sv0 (Sv.union rx U)).
Proof.
move=> hf; elim: n sv0 => // n ih sv0 /=.
t_xrbindP => -[s' c'] /hf hs'.
case: ifP => _ ; first by move=> [<- _]; SvD.fsetdec.
by move=> /ih; SvD.fsetdec.
Qed.

Lemma wloop_live (f : Sv.t -> cexec (Sv.t * (Sv.t * (cmd * cmd)))) ii n U s sic :
  (forall s s' sic, f s = ok (s', sic) ->
     Sv.Subset s' (Sv.union s U) /\ Sv.Subset sic.1 (Sv.union s U)) ->
  dead_code.wloop f ii n s = ok sic -> Sv.Subset sic.1 (Sv.union s U).
Proof.
move=> hf; elim: n s => // n ih s /=.
t_xrbindP => -[s' sic'] /hf [hs' hsic].
case: ifP => _ ; first by move=> [<-].
by move=> /ih; SvD.fsetdec.
Qed.

(* [wloop] stops on a set of the variables live at the head of the loop,
   that contains the variables live after it. *)
Lemma wloop_liveP (f : Sv.t -> cexec (Sv.t * (Sv.t * (cmd * cmd)))) ii n U s sic :
  (forall s s' sic, f s = ok (s', sic) -> Sv.Subset s' (Sv.union s U)) ->
  dead_code.wloop f ii n s = ok sic ->
  exists si s', [/\ Sv.Subset s si, Sv.Subset si (Sv.union s U), f si = ok (s', sic)
                  & Sv.Subset s' si].
Proof.
move=> hf; elim: n s => // n ih s /=.
t_xrbindP => -[s' sic'] hs.
case: ifP => hsub.
+ move: hsub => /Sv.subset_spec hsub [<-]; exists s, s'; split => //; SvD.fsetdec.
move=> /ih [si [s'' [h1 h2 h3 h4]]]; exists si, s''; split => //; first by SvD.fsetdec.
by have := hf _ _ _ hs; SvD.fsetdec.
Qed.

Context {LC : LoopCounter}.
Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).
Notation ftw_i := (for_to_while_i fresh_var_ident).
Notation ftw_c V := (for_to_while_c (ftw_i V)).

Lemma ftw_c_cons V i c O :
  ftw_c V (i :: c) O =
    Let r := ftw_c V c O in
    Let ri := ftw_i V i r.1 in
    ok (ri.1, ri.2 ++ r.2).
Proof. by []. Qed.

(* The live sets are those of the source: the variables live before an
   instruction are live after it or read by it. *)
Let Li (i : instr) := forall V O I c',
  ftw_i V i O = ok (I, c') -> Sv.Subset I (Sv.union O (read_I i)).
Let Li_r (i : instr_r) := forall ii, Li (MkI ii i).
Let Lc (c : cmd) := forall V O I c',
  ftw_c V c O = ok (I, c') -> Sv.Subset I (Sv.union O (read_c c)).

Lemma ftw_c_live c : Lc c.
Proof.
move: c; apply (cmd_rect (Pr := Li_r) (Pi := Li) (Pc := Lc)) => //; rewrite /Li_r /Li /Lc.
+ by move=> _ O _ _ [<- _]; SvD.fsetdec.
+ move=> i c hi hc V O I c_; rewrite ftw_c_cons.
  t_xrbindP => -[R c1] /hc{}hc [I1 i1] /hi{}hi /= <- _.
  by rewrite read_c_cons /=; move: hi => /=; SvD.fsetdec.
+ move=> x tg ty e ii V O I c_ /= [<- _].
  by rewrite read_Ii read_i_assgn read_rvE read_eE; SvD.fsetdec.
+ move=> xs t o es ii V O I c_ /= [<- _].
  by rewrite read_Ii read_i_opn read_esE read_rvsE; SvD.fsetdec.
+ move=> xs o es ii V O I c_ /= [<- _].
  by rewrite read_Ii read_i_syscall read_esE read_rvsE; SvD.fsetdec.
+ move=> a ii V O I c_ /= [<- _].
  by rewrite read_Ii read_i_assert read_eassertE; SvD.fsetdec.
+ move=> e c1 c2 hc1 hc2 ii V O I c_ /=.
  t_xrbindP => -[I1 c1_] /hc1{}hc1 [I2 c2_] /hc2{}hc2 [<- _].
  by rewrite read_Ii read_i_if read_eE; SvD.fsetdec.
+ move=> x d lo hi c hc ii V O I c_ /=.
  have hl : forall V0 s c1,
    loop (ftw_c V0 c) ii loop_counter Sv.empty (Sv.add x Sv.empty) O = ok (s, c1) ->
    Sv.Subset (read_e_rec (read_e_rec s hi) lo)
      (Sv.union O (read_I (MkI ii (Cfor x (d, lo, hi) c)))).
  + move=> V0 s c1 /(loop_live (U := read_c c)) -/(_ (fun s s1 c => hc V0 s s1 c)).
    by rewrite read_Ii read_i_for !read_eE; SvD.fsetdec.
  case: d hl => hl /=; t_xrbindP => _ [[V0 cb] b] _ /=; t_xrbindP.
  + by move=> -[s c1] /hl h [<- _].
  by move=> -[s c1] /hl h [<- _].
+ move=> a c1 e inf c2 hc1 hc2 ii V O I c_ /=.
  t_xrbindP => -[s [c1_ c2_]] /wloop_live h [<- _].
  rewrite read_Ii read_i_while; apply: h => s0 s1 sic.
  t_xrbindP => -[I1 c1_'] /hc1 h1 /=; t_xrbindP => -[I2 c2_'] /hc2 h2.
  by move=> [<- <-] /=; rewrite read_eE in h1; split; SvD.fsetdec.
move=> xs f es ii V O I c_ /= [<- _].
by rewrite read_Ii read_i_call read_esE read_rvsE; SvD.fsetdec.
Qed.

Lemma write_while_of_for ii x d lo hi c :
  Sv.Equal (write_c (while_of_for ii x d lo hi c)) (Sv.add x (write_c c)).
Proof.
case: d; rewrite /while_of_for /= !write_c_cons !write_Ii write_i_assgn write_i_while.
all: rewrite write_c_app write_c_cons !write_c_nil write_Ii write_i_assgn /=.
all: SvD.fsetdec.
Qed.

Lemma write_guarded_while_of_for ii x d lo hi c :
  Sv.Equal (write_c (guarded_while_of_for ii x d lo hi c)) (Sv.add x (write_c c)).
Proof.
rewrite /guarded_while_of_for write_c_cons write_Ii write_i_if write_c_nil write_c_app.
rewrite write_while_of_for write_c_cons write_c_nil write_Ii write_i_assgn /=.
SvD.fsetdec.
Qed.

Lemma loop_boundW ii V W x sfx e V0 cb b :
  loop_bound fresh_var_ident ii V W x sfx e = ok (V0, cb, b) ->
  Sv.Subset V V0 /\ forall z, Sv.In z (write_c cb) -> ~ Sv.In z V.
Proof.
rewrite /loop_bound; case: stable_bound.
+ by move=> [<- <- _]; split => // z; rewrite write_c_nil; SvD.fsetdec.
t_xrbindP => /Sv_memP hb <- <- _; split; first by SvD.fsetdec.
by move=> z; rewrite write_c_assgn1 /= => /SvD.F.add_iff [<- | /SvD.F.empty_iff].
Qed.

(* The variables of [V] that the transformed code writes are written by the
   source. *)
Let Wi (i : instr) := forall V O I c',
  ftw_i V i O = ok (I, c') ->
  forall z, Sv.In z V -> Sv.In z (write_c c') -> Sv.In z (write_I i).
Let Wi_r (i : instr_r) := forall ii, Wi (MkI ii i).
Let Wc (c : cmd) := forall V O I c',
  ftw_c V c O = ok (I, c') ->
  forall z, Sv.In z V -> Sv.In z (write_c c') -> Sv.In z (write_c c).

Lemma ftw_c_write c : Wc c.
Proof.
move: c; apply (cmd_rect (Pr := Wi_r) (Pi := Wi) (Pc := Wc)) => //; rewrite /Wi_r /Wi /Wc.
+ by move=> V O I c_ [_ <-].
+ move=> i c hi hc V O I c_; rewrite ftw_c_cons.
  t_xrbindP => -[R c1] /hc{}hc [I1 i1] /hi{}hi /= _ <- z hz.
  by rewrite write_c_app write_c_cons => /Sv.union_spec [/(hi _ hz) | /(hc _ hz)]; SvD.fsetdec.
1-4: by move=> > /= [_ <-] z _; rewrite write_c_cons write_c_nil; SvD.fsetdec.
+ move=> e c1 c2 hc1 hc2 ii V O I c_ /=.
  t_xrbindP => -[I1 c1_] /hc1{}hc1 [I2 c2_] /hc2{}hc2 [_ <-] z hz.
  rewrite write_c_cons write_c_nil !write_Ii !write_i_if.
  by move=> /Sv.union_spec [/Sv.union_spec [/(hc1 _ hz) | /(hc2 _ hz)] | ]; SvD.fsetdec.
+ move=> x d lo hi c hc ii V O I c_ /=.
  have hl : forall V0 cb s c1 lo0 hi0 z, Sv.Subset V V0 ->
    (forall z, Sv.In z (write_c cb) -> ~ Sv.In z V) ->
    loop (ftw_c V0 c) ii loop_counter Sv.empty (Sv.add x Sv.empty) O = ok (s, c1) ->
    Sv.In z V ->
    Sv.In z (write_c (cb ++ (if Sv.mem x O then guarded_while_of_for ii x d lo0 hi0 c1
                             else while_of_for ii x d lo0 hi0 c1))) ->
    Sv.In z (write_I (MkI ii (Cfor x (d, lo, hi) c))).
  + move=> V0 cb s c1 lo0 hi0 z hV hcb /dead_code_proof.loopP [_ [s2 [/hc{}hc _]]] hz.
    rewrite write_c_app write_Ii write_i_for.
    have {}hc : Sv.In z (write_c c1) -> Sv.In z (write_c c) by apply hc; SvD.fsetdec.
    case: Sv.mem; rewrite ?write_guarded_while_of_for ?write_while_of_for.
    + by move=> h; have h2 := hcb z; SvD.fsetdec.
    by move=> h; have h2 := hcb z; SvD.fsetdec.
  case: d hl => hl /=; t_xrbindP => _ [[V0 cb] b] /loop_boundW [hV hcb] /=; t_xrbindP.
  + by move=> -[s c1] hloop [_ <-] z hz; apply: hl hV hcb hloop hz.
  by move=> -[s c1] hloop [_ <-] z hz; apply: hl hV hcb hloop hz.
+ move=> a c1 e inf c2 hc1 hc2 ii V O I c_ /=.
  t_xrbindP => -[s [c1_ c2_]] /dead_code_proof.wloopP [si [s' [_ [+ _]]]].
  t_xrbindP => -[I1 c1'] /hc1{}hc1 /=; t_xrbindP => -[I2 c2'] /hc2{}hc2.
  move=> [_ _ <- <-] _ <- z hz.
  rewrite write_c_cons write_c_nil !write_Ii !write_i_while.
  by move=> /Sv.union_spec [/Sv.union_spec [/(hc1 _ hz) | /(hc2 _ hz)] | ]; SvD.fsetdec.
by move=> > /= [_ <-] z _; rewrite write_c_cons write_c_nil; SvD.fsetdec.
Qed.

End LIVE.

#[local] Existing Instance progUnit.
#[local] Existing Instance nosubword.
#[local] Existing Instance indirect_c.

Section PROOF.

Context
  {asm_op syscall_state : Type} {wa : WithAssert} {ep : EstateParams syscall_state}
  {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
  {LC : LoopCounter} {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

Context (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident).
Context (p p' : prog) (ev : extra_val_t).
Hypothesis Hp : for_to_while_prog fresh_var_ident p = ok p'.

Notation wequiv_ftw := (wequiv_rec p' p ev ev eq_spec).

(* A [while] loop of the transformed program against a [for] loop of the
   source: [R js] relates the states at the head of the loop, [js] being the
   indices that the [for] loop has still to run. *)
Lemma wequiv_while_for (R : seq Z -> rel_c) (Rj : Z -> seq Z -> rel_c) (P Q : rel_c)
    ii a cond inf body ii' x d lo hi c :
  (forall t s b, P t s -> sem_cond (p_globs p') cond t = ok b ->
     exists2 bnds, sem_bound (p_globs p) lo hi s = ok bnds & R (wrange d bnds.1 bnds.2) t s) ->
  (forall js t s b, R js t s -> sem_cond (p_globs p') cond t = ok b ->
     if js is [::] then b = false /\ Q t s else b = true) ->
  (forall j js t s, R (j :: js) t s ->
     exists2 s', write_var true x (Vint j) s = ok s' & Rj j js t s') ->
  (forall j js, wequiv_ftw (Rj j js) body c (R js)) ->
  wequiv_ftw P [:: MkI ii (Cwhile a [::] cond inf body)] [:: MkI ii' (Cfor x (d, lo, hi) c)] Q.
Proof.
move=> hP hR hw hbody t s hts.
case hc: (sem_cond (spp := spp) (p_globs p') cond t) => [b | err]; last first.
+ rewrite isem_cmd_while /= /isem_cond hc /= bind_throw bind_throw.
  apply xrutt.xrutt_CutL.
  by rewrite /core_logics.errcutoff /is_error /= mid12.
have [bnds hb hR0] := hP _ _ _ hts hc.
rewrite /isem_cmd_ /= /isem_bound hb /= bind_ret_l !bind_ret_r.
move: (wrange _ _ _) t s hR0 {hts hc hb} => js; elim: js => [ | j js ih] t s hjs.
all: rewrite /isem_while_loop unfold_iter /isem_while_round /= bind_ret_l /isem_cond.
all: case hc: (sem_cond (spp := spp) (p_globs p') cond t) => [bc | err] /=; last first.
1,3: rewrite bind_throw bind_throw; apply xrutt.xrutt_CutL.
1,2: by rewrite /core_logics.errcutoff /is_error /= mid12.
+ have [-> hQ] := hR _ _ _ _ hjs hc.
  by rewrite bind_ret_l bind_ret_l /=; apply xrutt.xrutt_Ret.
have /= ? := hR _ _ _ _ hjs hc; subst bc.
have [s1 hws hRj] := hw _ _ _ _ hjs.
rewrite /isem_for_round /iwrite_var hws /= !bind_ret_l bind_bind.
apply xrutt_facts.xrutt_bind with (RR := R js); first exact: hbody hRj.
by move=> t2 s2 hR2; rewrite bind_ret_l; apply xrutt.xrutt_add_Tau_l; exact: ih.
Qed.

Lemma eltiI gd s e1 e2 bc :
  sem_cond gd (elti e1 e2) s = ok bc ->
  exists z1 z2, [/\ sem_pexpr true gd s e1 >>= to_int = ok z1,
    sem_pexpr true gd s e2 >>= to_int = ok z2 & bc = (z1 <? z2)%Z].
Proof.
rewrite /sem_cond /=; t_xrbindP => v v1 h1 v2 h2 /sem_sop2I [w1 [w2 [w3 [hw1 hw2 + ->]]]].
move=> /= -[<-] /= [<-].
by exists w1, w2; rewrite h1 h2.
Qed.

Lemma sem_assgn_intP (pp : prog) t t' (x : var_i) e :
  sem_assgn pp (Lvar x) AT_none aint e t = ok t' ->
  exists z, [/\ sem_pexpr true (p_globs pp) t e >>= to_int = ok z,
    eval_atype (vtype x) = cint & t' = with_vm t (evm t).[x <- Vint z]].
Proof.
rewrite /sem_assgn; t_xrbindP => v hv v' htr /=.
move: htr; rewrite /truncate_val /=; t_xrbindP => z hz <- /write_varP [-> hdb htr].
exists z; split => //; first by rewrite hv.
by move: htr; rewrite /truncatable; case: eval_atype => //= _ /eqP.
Qed.

Lemma get_var_set_int (vm : Vm.t) (y : var) z :
  eval_atype (vtype y) = cint -> get_var true vm.[y <- Vint z] y = ok (Vint z).
Proof. by move=> hty; rewrite /get_var Vm.setP_eq hty. Qed.

Lemma ftw_globs : p_globs p' = p_globs p.
Proof using Hp. by move: Hp; rewrite /for_to_while_prog; t_xrbindP => ? _ <-. Qed.

Lemma loop_boundP ii V W x sfx e V0 cb b :
  loop_bound fresh_var_ident ii V W x sfx e = ok (V0, cb, b) ->
  Sv.Subset W V -> Sv.Subset (read_e e) V ->
  [/\ Sv.Subset V V0, ~~ use_mem b, Sv.Subset (read_e b) V0,
      (forall z, Sv.In z (read_e b) -> ~ Sv.In z W)
    & forall I, Sv.Subset I V -> Sv.Subset (read_e e) I ->
        wequiv_ftw (st_eq_on I) cb [::]
          (fun t s => st_eq_on I t s /\
             sem_pexpr true (p_globs p') t b >>= to_int =
             sem_pexpr true (p_globs p) s e >>= to_int)].
Proof using Hp.
rewrite /loop_bound; case hs: stable_bound.
+ move: hs => /andP [/disjointP hdis hnm] [<- <- <-] hW he; split => //.
  move=> I hI heI; apply wequiv_nil => t s [hscs hmem hvm]; split => //.
  by rewrite ftw_globs (eq_on_sem_pexpr _ _ hmem (eq_onI heI hvm)).
t_xrbindP => /Sv_memP hb <- <- <- hW he.
split => //; first by SvD.fsetdec.
+ by rewrite /read_e /= /read_gvar /=; SvD.fsetdec.
+ by move=> z; move: hb; rewrite /read_e /= /read_gvar /=; SvD.fsetdec.
move=> I hI heI; apply wequiv_assign_left => t t' s [hscs hmem hvm] /sem_assgn_intP [z [hz hty ->]].
split.
+ split => //= y hy; rewrite Vm.setP_neq; first exact: hvm.
  by apply/eqP => heq; apply: hb; rewrite /= heq; exact: hI hy.
rewrite -ftw_globs -(eq_on_sem_pexpr _ _ hmem (eq_onI heI hvm)) hz /=.
by rewrite /get_gvar /= get_var_set_int.
Qed.

(* The indices that a loop starting at [k] has still to run, [vb] being the
   bound read at each iteration. *)
Definition next_idx d (k : Z) := if d is UpTo then (k + 1)%Z else (k - 1)%Z.
Definition prev_idx d (k : Z) := if d is UpTo then (k - 1)%Z else (k + 1)%Z.
Definition rng d (k vb : Z) := if d is UpTo then wrange UpTo k vb else wrange DownTo vb k.
Definition in_rng d (k vb : Z) := if d is UpTo then (k <? vb)%Z else (vb <? k)%Z.

Lemma rngE d k vb :
  rng d k vb = if in_rng d k vb then k :: rng d (next_idx d k) vb else [::].
Proof.
case: d; rewrite /rng /in_rng /next_idx.
+ by rewrite {1}wrange_recU.
by rewrite {1}wrange_recD.
Qed.

Lemma eaddiP gd s e1 e2 z1 z2 :
  sem_pexpr true gd s e1 >>= to_int = ok z1 ->
  sem_pexpr true gd s e2 >>= to_int = ok z2 ->
  sem_pexpr true gd s (eaddi e1 e2) >>= to_int = ok (z1 + z2)%Z.
Proof.
t_xrbindP => v1 h1 /to_intI ? v2 h2 /to_intI ?; subst v1 v2.
by rewrite /= h1 h2.
Qed.

Lemma esubiP gd s e1 e2 z1 z2 :
  sem_pexpr true gd s e1 >>= to_int = ok z1 ->
  sem_pexpr true gd s e2 >>= to_int = ok z2 ->
  sem_pexpr true gd s (esubi e1 e2) >>= to_int = ok (z1 - z2)%Z.
Proof.
t_xrbindP => v1 h1 /to_intI ? v2 h2 /to_intI ?; subst v1 v2.
by rewrite /= h1 h2.
Qed.

Definition cond_of d (x : var_i) b :=
  if d is UpTo then elti (Plvar x) b else elti b (Plvar x).
Definition step_of d (x : var_i) :=
  if d is UpTo then eaddi (Plvar x) (Pconst 1) else esubi (Plvar x) (Pconst 1).

Lemma while_of_forE ii x d eo b c1 :
  while_of_for ii x d (if d is UpTo then eo else b) (if d is UpTo then b else eo) c1 =
    [:: assign_int ii x eo;
        MkI ii (Cwhile NoAlign [::] (cond_of d x b) ii (c1 ++ [:: assign_int ii x (step_of d x)]))].
Proof.
by case: d.
Qed.

Lemma sem_lvar_int gd t (x : var_i) k :
  get_var true (evm t) x = ok (Vint k) -> sem_pexpr true gd t (Plvar x) >>= to_int = ok k.
Proof.
by move=> h; rewrite /= /get_gvar /= h.
Qed.

Lemma cond_ofP gd t d (x : var_i) b k vb bc :
  get_var true (evm t) x = ok (Vint k) ->
  sem_pexpr true gd t b >>= to_int = ok vb ->
  sem_cond gd (cond_of d x b) t = ok bc -> bc = in_rng d k vb.
Proof.
move=> /(sem_lvar_int gd) hx hb.
by case: d; rewrite /cond_of /in_rng => /eltiI [z1 [z2 [h1 h2 ->]]];
  move: h1 h2; rewrite ?hx ?hb => -[->] [->].
Qed.

Lemma step_ofP gd t d (x : var_i) k :
  get_var true (evm t) x = ok (Vint k) ->
  sem_pexpr true gd t (step_of d x) >>= to_int = ok (next_idx d k).
Proof.
move=> /(sem_lvar_int gd) hx.
by case: d; [apply: eaddiP hx _ | apply: esubiP hx _].
Qed.

Lemma get_var_int vm (y : var) k :
  vm.[y] = Vint k -> get_var true vm y = ok (Vint k).
Proof.
by move=> h; rewrite /get_var h.
Qed.

Lemma vm_get_int vm (y : var) k : vm.[y] = Vint k -> eval_atype (vtype y) = cint.
Proof.
by move=> h; have := Vm.getP vm y; rewrite h => /compat_valE.
Qed.

Lemma in_rng_last d k vb :
  in_rng d (prev_idx d k) vb -> ~~ in_rng d k vb -> k = vb.
Proof.
by case: d; rewrite /in_rng /prev_idx => /ZltP h /ZltP h'; lia.
Qed.

(* The generated loop against the source [for] loop. [eo] is the bound read
   once, before the loop, [b] the bound read at each iteration, which has the
   value of the source bound [eb]. After the loop the index of the generated
   loop is out of the range; when [g] holds, the range is not empty and the
   index of the source holds its last element. *)
Lemma wequiv_while_of_for (g : bool) ii ii' (x : var_i) d lo hi b c c1 s1 s2 :
  let eo := if d is UpTo then lo else hi in
  let eb := if d is UpTo then hi else lo in
  ~~ use_mem b ->
  ~ Sv.In x (read_e b) ->
  (forall z, Sv.In z (read_e b) -> ~ Sv.In z (write_c c1)) ->
  ~ Sv.In x (write_c c1) -> ~ Sv.In x (write_c c) ->
  Sv.Subset s2 (Sv.add x s1) ->
  wequiv_ftw (st_eq_on s2) c1 c (st_eq_on s1) ->
  wequiv_ftw
    (fun t s => [/\ st_eq_on (Sv.union (read_e eo) (Sv.remove x s1)) t s,
        sem_pexpr true (p_globs p') t b >>= to_int = sem_pexpr true (p_globs p) s eb >>= to_int
      & g -> exists kst vb, [/\ sem_pexpr true (p_globs p) s eo >>= to_int = ok kst,
                sem_pexpr true (p_globs p') t b >>= to_int = ok vb & in_rng d kst vb]])
    (while_of_for ii x d (if d is UpTo then eo else b) (if d is UpTo then b else eo) c1)
    [:: MkI ii' (Cfor x (d, lo, hi) c)]
    (fun t s => exists k vb, [/\ st_eq_on (Sv.remove x s1) t s,
        sem_pexpr true (p_globs p') t b >>= to_int = ok vb,
        (evm t).[x] = Vint k, ~~ in_rng d k vb
      & g -> k = vb /\ (evm s).[x] = Vint (prev_idx d vb)]).
Proof using Hp.
move=> eo eb hsb hxb hbw hxc1 hxc hs2 hbody.
rewrite while_of_forE -[[:: MkI ii' _]]cat0s.
rewrite -[[:: assign_int _ _ _; _]]cat1s.
apply wequiv_cat with (fun t s => exists kst, [/\ st_eq_on (Sv.remove x s1) t s,
    (evm t).[x] = Vint kst,
    sem_pexpr true (p_globs p) s eo >>= to_int = ok kst,
    sem_pexpr true (p_globs p') t b >>= to_int = sem_pexpr true (p_globs p) s eb >>= to_int
  & g -> exists vb, sem_pexpr true (p_globs p') t b >>= to_int = ok vb /\ in_rng d kst vb]).
+ apply wequiv_assign_left => t t' s [heq hb hg] /sem_assgn_intP [z [hz hty ->]].
  case: heq => hscs hmem hvm.
  have hzs : sem_pexpr true (p_globs p) s eo >>= to_int = ok z.
  + by rewrite -ftw_globs -(eq_on_sem_pexpr _ _ hmem (eq_onI _ hvm)) // ; SvD.fsetdec.
  have hbt : sem_pexpr true (p_globs p') (with_vm t (evm t).[x <- Vint z]) b =
             sem_pexpr true (p_globs p') t b.
  + apply use_memP_eq_on => //; move=> y hy /=.
    by rewrite Vm.setP_neq //; apply/eqP => ?; subst y.
  exists z; rewrite hbt; split => //.
  + split => //= y hy; rewrite Vm.setP_neq; first by apply hvm; SvD.fsetdec.
    by apply/eqP => ?; subst y; SvD.fsetdec.
  + by rewrite Vm.setP_eq hty.
  move=> /hg [kst [vb [hk hvb hin]]]; exists vb; split => //.
  by move: hk; rewrite hzs => -[->].
apply (wequiv_while_for
  (R := fun js t s => exists k vb kst, [/\ st_eq_on (Sv.remove x s1) t s,
      sem_pexpr true (p_globs p') t b >>= to_int = ok vb, (evm t).[x] = Vint k,
      js = rng d k vb
    & g -> in_rng d kst vb /\
           (k = kst \/ (evm s).[x] = Vint (prev_idx d k) /\ in_rng d (prev_idx d k) vb)])
  (Rj := fun j js t s => exists vb kst, [/\ st_eq_on (Sv.add x (Sv.remove x s1)) t s,
      sem_pexpr true (p_globs p') t b >>= to_int = ok vb, (evm t).[x] = Vint j,
      (evm s).[x] = Vint j, js = rng d (next_idx d j) vb, in_rng d j vb
    & g -> in_rng d kst vb])).
+ move=> t s bc [kst [heq hx hk hbeq hg]] hc.
  have [vb hvb] : exists vb, sem_pexpr true (p_globs p') t b >>= to_int = ok vb.
  + by move: hc; case: (d) => /eltiI [z1 [z2 [h1 h2 _]]]; [exists z2 | exists z1].
  rewrite hvb in hbeq.
  exists (if d is UpTo then (kst, vb) else (vb, kst)).
  + by move: hk hbeq; rewrite /eo /eb /sem_bound; case: (d) => /= -> <-.
  exists kst, vb, kst; split => //; first by case: (d).
  by move=> /hg [vb' []]; rewrite hvb => -[<-] hin; split => //; left.
+ move=> js t s bc [k [vb [kst [heq hvb hx -> hg]]]] /(cond_ofP (get_var_int hx) hvb) ->.
  rewrite rngE; case: ifP => hin //; split => //; exists k, vb; split => //; first by rewrite hin.
  move=> /hg [hkst [? | [hpx hprev]]]; first by subst k; rewrite hkst in hin.
  by have ? := in_rng_last hprev (negbT hin); subst k.
+ move=> j js t s [k [vb [kst [[hscs hmem hvm] hvb hx hjs hg]]]].
  move: hjs; rewrite rngE; case: ifP => // hin [? ?]; subst j js.
  have hty := vm_get_int hx.
  exists (with_vm s (evm s).[x <- Vint k]).
  + by apply: write_var_eq_type => //; rewrite hty.
  exists vb, kst; split => //; last by move=> /hg [].
  + split => //= y hy; case: (v_var x =P y) => [<- | hne].
    + by rewrite Vm.setP_eq hty /= hx.
    by rewrite Vm.setP_neq; [apply hvm; SvD.fsetdec | apply/eqP].
  by rewrite /= Vm.setP_eq hty.
move=> j js; rewrite -[c]cats0.
apply wequiv_cat with (fun t s => exists vb kst, [/\ st_eq_on (Sv.remove x s1) t s,
    sem_pexpr true (p_globs p') t b >>= to_int = ok vb, (evm t).[x] = Vint j,
    (evm s).[x] = Vint j, js = rng d (next_idx d j) vb, in_rng d j vb
  & g -> in_rng d kst vb]).
+ match goal with |- wequiv _ _ _ _ ?P _ _ _ => have hf := wequiv_frame (F := P) hbody end.
  apply: (wequiv_weaken _ _ hf).
  + move=> t s h; split => //; case: h => vb [kst [h _ _ _ _ _ _]].
    by apply: st_rel_weaken h => ??; apply eq_onI; SvD.fsetdec.
  move=> t s [heq [t0 [s0 [[vb [kst [_ hvb hxt hxs hjs hin hg]]] ht hs]]]].
  exists vb, kst; split => //.
  + by apply: st_rel_weaken heq => ??; apply eq_onI; SvD.fsetdec.
  + rewrite -hvb; congr (_ >>= _); apply use_memP_eq_on => //.
    by move=> y hy; rewrite ht //; apply: hbw hy.
  + by rewrite -ht.
  by rewrite -hs.
apply wequiv_assign_left => t t' s [vb [kst [heq hvb hxt hxs hjs hin hg]]].
move=> /sem_assgn_intP [z [hz hty ->]].
move: hz; rewrite (step_ofP _ _ (get_var_int hxt)) => -[?]; subst z.
have hprev : prev_idx d (next_idx d j) = j by case: (d); rewrite /prev_idx /next_idx; lia.
exists (next_idx d j), vb, kst; split => //.
+ case: heq => hscs hmem hvm; split => //= y hy; rewrite Vm.setP_neq; first exact: hvm.
  by apply/eqP => ?; subst y; SvD.fsetdec.
+ rewrite -hvb; congr (_ >>= _); apply use_memP_eq_on => //; move=> y hy /=.
  by rewrite Vm.setP_neq //; apply/eqP => ?; subst y.
+ by rewrite /= Vm.setP_eq hty.
by move=> /hg hkst; split => //; right; rewrite hprev.
Qed.

(* The [for] loop, once its bound read at each iteration is chosen. *)
Lemma ftw_for_aux V O ii (x : var_i) d lo hi c sfx V0 cb b s1 c1 :
  let eo := if d is UpTo then lo else hi in
  let eb := if d is UpTo then hi else lo in
  Sv.Subset
    (Sv.union (Sv.union (vars_c c) (Sv.singleton x)) (Sv.union (read_e lo) (read_e hi))) V ->
  Sv.Subset O V -> ~ Sv.In x (write_c c) ->
  (forall V' O' I' c'', Sv.Subset (vars_c c) V' -> Sv.Subset O' V' ->
     for_to_while_c (for_to_while_i fresh_var_ident V') c O' = ok (I', c'') ->
     wequiv_ftw (st_eq_on I') c'' c (st_eq_on O')) ->
  loop_bound fresh_var_ident ii V (Sv.add x (write_c c)) x sfx eb = ok (V0, cb, b) ->
  dead_code.loop (for_to_while_c (for_to_while_i fresh_var_ident V0) c) ii
      loop_counter Sv.empty (Sv.add x Sv.empty) O = ok (s1, c1) ->
  let lo0 := if d is UpTo then eo else b in
  let hi0 := if d is UpTo then b else eo in
  wequiv_ftw (st_eq_on (read_e_rec (read_e_rec s1 hi) lo))
    (cb ++ (if Sv.mem x O then guarded_while_of_for ii x d lo0 hi0 c1
            else while_of_for ii x d lo0 hi0 c1))
    [:: MkI ii (Cfor x (d, lo, hi) c)] (st_eq_on O).
Proof using Hp.
move=> eo eb hV hO hxc hc hlb hloop lo0 hi0.
have hW : Sv.Subset (Sv.add x (write_c c)) V by rewrite /vars_c in hV; SvD.fsetdec.
have heb : Sv.Subset (read_e eb) V by rewrite /eb; case: (d); SvD.fsetdec.
have [hVV0 hsb hbV0 hbW hcb] := loop_boundP hlb hW heb.
have [hOs1 [s2 [hbody hs2]]] := dead_code_proof.loopP hloop.
have hs1V : Sv.Subset s1 V.
+ have := loop_live (U := read_c c) (fun s s' c0 h => ftw_c_live h) hloop.
  by rewrite /vars_c in hV; SvD.fsetdec.
have hIH := hc V0 s1 s2 c1 ltac:(SvD.fsetdec) ltac:(SvD.fsetdec) hbody.
have hw1 := ftw_c_write hbody.
have hxV : Sv.In x V by SvD.fsetdec.
have hxc1 : ~ Sv.In x (write_c c1) by move=> /(hw1 _ (hVV0 _ hxV)).
have hxb : ~ Sv.In x (read_e b) by move=> /hbW; apply; SvD.fsetdec.
have hbw : forall z, Sv.In z (read_e b) -> ~ Sv.In z (write_c c1).
+ by move=> z hz /(hw1 _ (hbV0 _ hz)) hzc; apply: (hbW _ hz); SvD.fsetdec.
have hs2' : Sv.Subset s2 (Sv.add x s1) by SvD.fsetdec.
set I := read_e_rec (read_e_rec s1 hi) lo.
have hI : Sv.Subset I V by rewrite /I !read_eE; SvD.fsetdec.
have hebI : Sv.Subset (read_e eb) I by rewrite /I /eb !read_eE; case: (d); SvD.fsetdec.
rewrite -[[:: MkI ii (Cfor _ _ _)]]cat0s.
apply wequiv_cat with (fun t s => st_eq_on I t s /\
  sem_pexpr true (p_globs p') t b >>= to_int = sem_pexpr true (p_globs p) s eb >>= to_int).
+ exact: hcb.
have heoI : Sv.Subset (read_e eo) I by rewrite /I /eo !read_eE; case: (d); SvD.fsetdec.
have hs1I : Sv.Subset s1 I by rewrite /I !read_eE; SvD.fsetdec.
case: Sv_memP => hxO; last first.
+ have hWF := wequiv_while_of_for (g := false) ii ii hsb hxb hbw hxc1 hxc hs2' hIH.
  move: hWF; rewrite /lo0 /hi0 /eo /eb => hWF.
  eapply wequiv_weaken; last exact: hWF.
  + move=> t s [heq hb] /=; split => //.
    by apply: st_rel_weaken heq => ??; apply eq_onI; SvD.fsetdec.
  move=> t s [k [vb [heq _ _ _ _]]].
  by apply: st_rel_weaken heq => ??; apply eq_onI; SvD.fsetdec.
have hval : forall t s bc, st_eq_on I t s ->
  sem_pexpr true (p_globs p') t b >>= to_int = sem_pexpr true (p_globs p) s eb >>= to_int ->
  sem_cond (p_globs p') (elti lo0 hi0) t = ok bc ->
  exists z1 z2, [/\ sem_bound (p_globs p) lo hi s = ok (z1, z2), bc = (z1 <? z2)%Z,
    sem_pexpr true (p_globs p') t b >>= to_int = ok (if d is UpTo then z2 else z1)
  & sem_pexpr true (p_globs p) s eo >>= to_int = ok (if d is UpTo then z1 else z2)].
+ move=> t s bc [hscs hmem hvm] hb /eltiI [z1 [z2 [h1 h2 ->]]].
  have heo : sem_pexpr true (p_globs p') t eo = sem_pexpr true (p_globs p) s eo.
  + by rewrite ftw_globs (eq_on_sem_pexpr _ _ hmem (eq_onI heoI hvm)).
  exists z1, z2; move: h1 h2 hb heo; rewrite /sem_bound /lo0 /hi0 /eo /eb.
  by case: (d) => /= h1 h2 hb heo; split => //; rewrite -?hb -?heo ?h1 ?h2.
rewrite /guarded_while_of_for; apply wequiv_if_left => -[]; last first.
+ apply wequiv_for_empty => t s [[heq hb] hcd].
  have [z1 [z2 [hbnd hbc _ _]]] := hval _ _ _ heq hb hcd.
  exists (z1, z2) => //=; split.
  + by case: (d); [rewrite {1}wrange_recU | rewrite {1}wrange_recD]; rewrite -hbc.
  by apply: st_rel_weaken heq => ??; apply eq_onI; SvD.fsetdec.
have hWT := wequiv_while_of_for (g := true) ii ii hsb hxb hbw hxc1 hxc hs2' hIH.
move: hWT; rewrite /lo0 /hi0 /eo /eb => hWT.
rewrite -[[:: MkI ii (Cfor _ _ _)]]cats0.
eapply wequiv_cat; first (eapply wequiv_weaken; last exact: hWT).
+ move=> t s [[heq hb] hcd]; have [z1 [z2 [hbnd hbc hvb heo]]] := hval _ _ _ heq hb hcd.
  split => //; first by apply: st_rel_weaken heq => ??; apply eq_onI; SvD.fsetdec.
  move=> _; exists (if d is UpTo then z1 else z2), (if d is UpTo then z2 else z1); split => //.
  by move: hbc; rewrite /in_rng; case: (d).
+ by move=> t s h; exact h.
apply wequiv_assign_left => t t' s [k [vb [[hscs hmem hvm] hvb hxt hin /(_ erefl) [? hxs]]]].
subst k; move=> /sem_assgn_intP [z [hz hty ->]].
have ? : z = prev_idx d vb.
+ move: hz; rewrite /hi0 /lo0 /prev_idx; case: (d) => /=.
  + have h1 : sem_pexpr true (p_globs p') t (Pconst 1) >>= to_int = ok 1%Z by [].
    have := esubiP hvb h1.
    by rewrite /esubi /= => -> [].
  have h1 : sem_pexpr true (p_globs p') t (Pconst 1) >>= to_int = ok 1%Z by [].
  have := eaddiP hvb h1.
  by rewrite /eaddi /= => -> [].
subst z; split => //= y hy; case: (v_var x =P y) => [<- | hne].
+ by rewrite Vm.setP_eq hty /= hxs.
rewrite Vm.setP_neq; last by apply/eqP.
by apply: hvm; SvD.fsetdec.
Qed.

Lemma ftw_forP V O I c' ii x d lo hi c :
  Sv.Subset (vars_I (MkI ii (Cfor x (d, lo, hi) c))) V -> Sv.Subset O V ->
  (forall V' O' I' c'', Sv.Subset (vars_c c) V' -> Sv.Subset O' V' ->
     for_to_while_c (for_to_while_i fresh_var_ident V') c O' = ok (I', c'') ->
     wequiv_ftw (st_eq_on I') c'' c (st_eq_on O')) ->
  for_to_while_i fresh_var_ident V (MkI ii (Cfor x (d, lo, hi) c)) O = ok (I, c') ->
  wequiv_ftw (st_eq_on I) c' [:: MkI ii (Cfor x (d, lo, hi) c)] (st_eq_on O).
Proof using Hp.
rewrite vars_I_for => hV hO hc /=.
t_xrbindP => /Sv_memP hxc.
case: d => /=; t_xrbindP => -[[V0 cb] b] hlb /=; t_xrbindP => -[s1 c1] hloop [<- <-].
+ exact: (ftw_for_aux (d := UpTo) hV hO hxc hc hlb hloop).
exact: (ftw_for_aux (d := DownTo) hV hO hxc hc hlb hloop).
Qed.

Lemma ftw_funcs : map_cfprog (for_to_while_fd fresh_var_ident) (p_funcs p) = ok (p_funcs p').
Proof using Hp.
by move: Hp; rewrite /for_to_while_prog; t_xrbindP => ? h <-.
Qed.

Lemma ftw_get_fundef fn fd' :
  get_fundef (p_funcs p') fn = Some fd' ->
  exists2 fd, get_fundef (p_funcs p) fn = Some fd &
    exists I, [/\ for_to_while_c (for_to_while_i fresh_var_ident (vars_fd fd)) (f_body fd)
                    (read_es [seq Plvar i | i <- f_res fd]) = ok (I, f_body fd')
                & fd' = with_body fd (f_body fd')].
Proof using Hp.
move=> /(get_map_cfprog_name_gen' ftw_funcs) [fd hfd ->]; exists fd => //.
by move: hfd; rewrite /for_to_while_fd; t_xrbindP => -[I c] h <-; exists I.
Qed.

Lemma ftw_sem_pre fn fs : sem_pre p' fn fs = ok tt -> sem_pre p fn fs = ok tt.
Proof using Hp.
rewrite /sem_pre ftw_globs; have := get_map_cfprog_name_gen_aux fn ftw_funcs.
case: get_fundef => [fd [fd' + ->] | -> //].
by rewrite /for_to_while_fd; t_xrbindP => ?? <-.
Qed.

Lemma ftw_sem_post fn vs fr : sem_post p' fn vs fr = ok tt -> sem_post p fn vs fr = ok tt.
Proof using Hp.
rewrite /sem_post ftw_globs; have := get_map_cfprog_name_gen_aux fn ftw_funcs.
case: get_fundef => [fd [fd' + ->] | -> //].
by rewrite /for_to_while_fd; t_xrbindP => ?? <-.
Qed.

#[local] Lemma checker_st_eq_onP' : Checker_eq p' p checker_st_eq_on.
Proof using Hp.
by apply checker_st_eq_onP; rewrite ftw_globs.
Qed.

#[local] Lemma checker_a_st_eq_onP' : Checker_a_eq p' p checker_a_st_eq_on.
Proof using Hp.
by apply checker_a_st_eq_onP; rewrite ftw_globs.
Qed.

#[local] Hint Resolve checker_st_eq_onP' checker_a_st_eq_onP' : core.

Let Pi (i : instr) := forall V O I c',
  Sv.Subset (vars_I i) V -> Sv.Subset O V ->
  for_to_while_i fresh_var_ident V i O = ok (I, c') ->
  wequiv_ftw (st_eq_on I) c' [:: i] (st_eq_on O).
Let Pi_r (i : instr_r) := forall ii, Pi (MkI ii i).
Let Pc (c : cmd) := forall V O I c',
  Sv.Subset (vars_c c) V -> Sv.Subset O V ->
  for_to_while_c (for_to_while_i fresh_var_ident V) c O = ok (I, c') ->
  wequiv_ftw (st_eq_on I) c' c (st_eq_on O).

Lemma ftw_cP c : Pc c.
Proof using Hp.
move: c; apply (cmd_rect (Pr := Pi_r) (Pi := Pi) (Pc := Pc)) => //; rewrite /Pi_r /Pi /Pc.
+ by move=> V O I c' _ _ [<- <-]; apply wequiv_nil.
+ move=> i c hi hc V O I c_ hV hO; rewrite ftw_c_cons vars_c_cons in hV *.
  t_xrbindP => -[R c1] hc1 [I1 i1] hi1 /= <- <-.
  have hR := ftw_c_live hc1.
  rewrite -cat1s; apply wequiv_cat with (st_eq_on R).
  + by apply: hi hi1; rewrite /vars_c in hV; SvD.fsetdec.
  by apply: hc hc1; SvD.fsetdec.
+ move=> x tg ty e ii V O I c' _ _ /= [<- <-]; rewrite write_i_assgn.
  apply wequiv_assgn_rel_eq with checker_st_eq_on
    (read_rv_rec (read_e_rec (Sv.diff O (vrv x)) e) x) => //=.
  + by split => //; rewrite /read_es /= read_rvE !read_eE; SvD.fsetdec.
  by split => //; rewrite /read_rvs /vrvs /= !read_rvE ?read_eE; SvD.fsetdec.
+ move=> xs tg o es ii V O I c' _ _ /= [<- <-].
  apply wequiv_opn_rel_eq with checker_st_eq_on
    (read_es_rec (read_rvs_rec (Sv.diff O (vrvs xs)) xs) es) => //=.
  + by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
  by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
+ move=> xs o es ii V O I c' _ _ /= [<- <-].
  set X := read_es_rec _ es.
  apply wequiv_syscall_rel_eq_core with checker_st_eq_on X => //=.
  + by split => //; rewrite /X read_esE read_rvsE; SvD.fsetdec.
  + by split => //; rewrite /X read_esE read_rvsE; SvD.fsetdec.
  exact: wrequiv_eq.
+ move=> a ii V O I c' _ _ /= [<- <-].
  apply wequiv_assert_rel_eq with checker_a_st_eq_on => //=.
  by split => //; rewrite read_eassertE; SvD.fsetdec.
+ move=> e c1 c2 hc1 hc2 ii V O I c_ hV hO /=; rewrite vars_I_if in hV.
  t_xrbindP => -[I1 c1'] h1 [I2 c2'] h2 [<- <-].
  have hV1 : Sv.Subset (vars_c c1) V by SvD.fsetdec.
  have hV2 : Sv.Subset (vars_c c2) V by SvD.fsetdec.
  have {}hc1 := hc1 _ _ _ _ hV1 hO h1.
  have {}hc2 := hc2 _ _ _ _ hV2 hO h2.
  apply wequiv_if_rel_eq with checker_st_eq_on (read_e_rec (Sv.union I1 I2) e) O O => //=.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  + apply wequiv_weaken with (st_eq_on I1) (st_eq_on O) => //.
    by apply st_rel_weaken => ??; apply eq_onI; rewrite read_eE; SvD.fsetdec.
  apply wequiv_weaken with (st_eq_on I2) (st_eq_on O) => //.
  by apply st_rel_weaken => ??; apply eq_onI; rewrite read_eE; SvD.fsetdec.
+ by move=> x d lo hi c hc ii V O I c' hV hO; apply: ftw_forP.
+ move=> a c1 e inf c2 hc1 hc2 ii V O I c_ hV hO /=; rewrite vars_I_while in hV.
  set dobody := (X in dead_code.wloop X).
  t_xrbindP => -[sv1 [c1' c2']] hloop [<- <-].
  have hf : forall s s0 sic, dobody s = ok (s0, sic) ->
    Sv.Subset s0 (Sv.union s (Sv.union (read_e e) (Sv.union (read_c c1) (read_c c2)))).
  + move=> s s0 sic; rewrite /dobody; t_xrbindP => -[I1 c1_] /ftw_c_live h1 /=.
    t_xrbindP => -[I2 c2_] /ftw_c_live h2.
    by move=> [<- _]; rewrite read_eE in h1; SvD.fsetdec.
  have [si [s' [hOsi hsi hbody hs']]] := wloop_liveP hf hloop.
  move: (hbody); rewrite /dobody; t_xrbindP => -[I1 c1_] h1 /=.
  t_xrbindP => -[I2 c2_] h2 [? ? ? ?]; subst I2 I1 c1_ c2_.
  have hV1 : Sv.Subset (vars_c c1) V by SvD.fsetdec.
  have hV2 : Sv.Subset (vars_c c2) V by SvD.fsetdec.
  rewrite /vars_c in hV.
  have hsiV : Sv.Subset (read_e_rec si e) V by rewrite read_eE; SvD.fsetdec.
  have hsv1 := ftw_c_live h1.
  have hsv1V : Sv.Subset sv1 V by rewrite read_eE in hsv1; SvD.fsetdec.
  have {}hc1 := hc1 V _ _ _ hV1 hsiV h1.
  have {}hc2 := hc2 V _ _ _ hV2 hsv1V h2.
  apply wequiv_weaken with (st_eq_on sv1) (st_eq_on (read_e_rec si e)) => //.
  + by apply st_rel_weaken => ??; apply eq_onI; rewrite read_eE; SvD.fsetdec.
  apply wequiv_while_rel_eq with checker_st_eq_on (read_e_rec si e) => //.
  + by split => //; rewrite /read_es /= !read_eE; SvD.fsetdec.
  apply wequiv_weaken with (st_eq_on s') (st_eq_on sv1) => //.
  by apply st_rel_weaken => ??; apply eq_onI; rewrite read_eE; SvD.fsetdec.
move=> xs f es ii V O I c' _ _ /= [<- <-].
apply wequiv_call_rel_eq_wa with checker_st_eq_on
  (read_es_rec (read_rvs_rec (Sv.diff O (vrvs xs)) xs) es) => //.
+ by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
+ by split => //; rewrite read_esE read_rvsE; SvD.fsetdec.
+ by move=> s1 s2 vs [h1 h2 _]; rewrite /mk_fstate h1 h2; apply ftw_sem_pre.
+ by move=> ?? ->; exact: wequiv_fun_rec.
by move=> vs fr; apply ftw_sem_post.
Qed.

Lemma ftw_callP fn :
  wiequiv_f p' p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof using Hp.
apply wequiv_fun_ind_wa => {}fn _ fs _ [<- <-] fd' hget'.
have [fd hget [I [hbody hfd']]] := ftw_get_fundef hget'.
exists fd => // hpre; split; first exact: ftw_sem_pre.
move=> s hinit; exists s.
+ by move: hinit; rewrite hfd'.
exists (st_eq_on I), (st_eq_on (read_es [seq Plvar i | i <- f_res fd])); split => //.
+ apply: ftw_cP hbody; rewrite ?vars_l_read_es /vars_fd; SvD.fsetdec.
+ rewrite hfd' /finalize_funcall /= => t t' fr [hscs hmem hvm].
  t_xrbindP => vs hgv vs' htr <-.
  move: hgv; rewrite -(sem_pexprs_get_var _ [::]) => hres.
  rewrite (eq_on_sem_pexprs _ _ hmem (eq_onI _ hvm)) in hres; last by [].
  rewrite sem_pexprs_get_var in hres.
  by rewrite hres /= htr /= hscs hmem; eexists; eauto.
by move=> fr1 fr2 <-; apply ftw_sem_post.
Qed.

End PROOF.

(* When the transformed program runs without failure, the source runs with
   the same arguments and results. *)
Lemma for_to_while_l :
  forall {asm_op syscall_state : Type} {wa : WithAssert} {ep : EstateParams syscall_state}
    {spp : SemPexprParams} {sip : SemInstrParams asm_op syscall_state}
    {LC : LoopCounter} {E E0 : Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}
    (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
    (p p' : uprog) (ev : extra_val_t),
  for_to_while_prog (pT := progUnit) fresh_var_ident p = ok p' ->
  forall fn,
  wiequiv_f (wa1 := wa) (wa2 := wa)
    p' p ev ev (rpreF (eS := eq_spec)) fn fn (rpostF (eS := eq_spec)).
Proof.
move=> asm_op syscall_state wa ep spp sip LC E E0 wE rE fresh_var_ident p p' ev hp fn.
exact: (ftw_callP (rE := rE) ev hp).
Qed.
