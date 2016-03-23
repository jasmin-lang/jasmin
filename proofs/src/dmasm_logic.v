(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import word dmasm_utils dmasm_type dmasm_var dmasm_sem 
               dmasm_sem_props dmasm_Ssem symbolic_expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------------- *)
(* ** Hoare Logic                                                             *)
(* -------------------------------------------------------------------------- *)

Definition hpred := sestate -> Prop.

Definition hoare (Pre:hpred) (c:cmd) (Post:hpred) := 
  forall (s s':sestate),  ssem s c s' -> Pre s -> Post s'.

Definition fpred (t:stype) := mem -> sst2ty t -> Prop.

Definition hoaref ta tr (Pre:fpred ta) (f:fundef ta tr) (Post:fpred tr) := 
  forall (m m':mem) va vr, ssem_fun f m va m' vr -> Pre m va -> Post m' vr.

(* -------------------------------------------------------------------------- *)
(* ** Core Rules                                                              *)
(* -------------------------------------------------------------------------- *)

(* Consequence *)

Lemma hoare_conseq (P1 Q1:hpred) c (P2 Q2:hpred) : 
  (forall s, P2 s -> P1 s) ->
  (forall s, Q1 s -> Q2 s) -> 
  hoare P1 c Q1 -> hoare P2 c Q2.
Proof.
  move=> HP HQ Hh s s' Hsem Hs.
  by apply: HQ;apply:(Hh _ _ Hsem);apply: HP.
Qed.

(* Skip *)

Lemma hoare_skip_core P : hoare P [::] P.
Proof. 
  by move=> ?? s Hp;case: _ {-1}_ _ / s (erefl ([::]:cmd)) Hp.
Qed.

Lemma hoare_skip (Q P:hpred) : (forall s, Q s -> P s) -> hoare Q [::] P.
Proof. 
  move=> qp;apply: (@hoare_conseq P P)=> //;apply hoare_skip_core.
Qed.

(* Base command *)
Lemma hoare_bcmd (P:hpred) bc: 
  hoare (fun s1 =>  forall s2,  ssem_bcmd s1 bc = ok s2 -> P s2) [::Cbcmd bc] P.
Proof.
  move=> ??;set c := Cbcmd _ => /ssem_iV s.
  case: _ {-1}_ _ / s (erefl c) => // ??? e [] ?;subst=> H.
  by apply: (H _ e).
Qed.

(* Sequence *)

Lemma hoare_seq R P Q c1 c2 : 
  hoare P c1 R ->  hoare R c2 Q ->  hoare P (c1 ++ c2) Q.
Proof.
  move=> H1 H2 ?? /ssem_cV [?[s1 s2]] Hp.
  by apply: (H2 _ _ s2 (H1 _ _ s1 Hp)).
Qed.

Lemma hoare_cons R P Q i c : 
  hoare P [::i] R ->  hoare R c Q ->  hoare P (i :: c) Q.
Proof. by apply:hoare_seq. Qed.

(* Conditionnal *)
Lemma hoare_if P Q (e: pexpr sbool) c1 c2 : 
  hoare (fun s => ssem_pexpr s.(sevm) e /\ P s) c1 Q ->
  hoare (fun s => ~~ssem_pexpr s.(sevm) e /\ P s) c2 Q ->
  hoare P [::Cif e c1 c2] Q.
Proof.
  move=> H1 H2 ??;set c := Cif _ _ _ => /ssem_iV s.
  case: _ {-1}_ _ / s (erefl c) => // ?????? s [] ??? Hp;subst.
  + by apply: (H1 _ _ s).
  by apply: (H2 _ _ s).
Qed.

(* Call *)
Lemma hoare_call ta tr Pf Qf x (f:fundef ta tr) e (Q:hpred):
  hoaref Pf f Qf ->
  hoare 
    (fun s => 
       Pf s.(semem) (ssem_pexpr s.(sevm) e) /\
       forall m' (v:sst2ty tr), 
         Qf m' v ->
         Q {|semem := m'; sevm :=  swrite_rval s.(sevm) x v |})
    [::Ccall x f e] 
    Q.
Proof.
  move=> Hf ??;set c := Ccall _ _ _ => /ssem_iV s.
  case: _ {-1}_ _ / s (erefl c) => // -[m mv]??????? /= s [] ??.
  subst=> -[] ? [] [] ? [] ? [] Hpf Hq;subst.
  by apply: Hq;apply: Hf s Hpf.
Qed.

Lemma hoare_call_seq ta tr Pf Qf x (f:fundef ta tr) e (P Q:hpred) c: 
  hoaref Pf f Qf ->
  hoare P c 
    (fun s => 
       Pf s.(semem) (ssem_pexpr s.(sevm) e) /\
       forall m' (v:sst2ty tr), 
         Qf m' v ->
         Q {|semem := m'; sevm := swrite_rval s.(sevm) x v |}) ->
  hoare P (rcons c (Ccall x f e)) Q.
Proof.
  by rewrite -cats1=> Hf Hc;apply: (hoare_seq Hc);apply hoare_call.
Qed.

(* Loop *)

Fixpoint vrv_rec {t} (s:Sv.t) (rv : rval t)  :=
  match rv with
  | Rvar  x               => Sv.add x s
  | Rpair st1 st2 rv1 rv2 => vrv_rec (vrv_rec s rv1) rv2 
  end.

Definition vrv {t} (rv : rval t) := vrv_rec Sv.empty rv.

Definition write_bcmd_rec (s:Sv.t) bc  := 
  match bc with
  | Assgn _ rv _  => vrv_rec s rv
  | _             => s
  end.

Definition write_bcmd := write_bcmd_rec Sv.empty.

Fixpoint write_i_rec s i := 
  match i with
  | Cbcmd bc        => write_bcmd_rec s bc
  | Cif   _ c1 c2   => foldl write_i_rec (foldl write_i_rec s c2) c1
  | Cfor  x _ c     => foldl write_i_rec (vrv_rec s x) c
  | Ccall _ _ x _ _ => vrv_rec s x
  end.

Definition write_i i := write_i_rec Sv.empty i.

Definition write_c c := foldl write_i_rec Sv.empty c.

Instance vrv_rec_m {t} : Proper (Sv.Equal ==> (@eq (rval t)) ==> Sv.Equal) vrv_rec.
Proof.
  move=> s1 s2 Hs ? r ->.
  elim:r s1 s2 Hs => //= [??? -> // | ?? r1 Hr1 r2 Hr2 ???];auto.
Qed.

Lemma vrv_var (x:var) : Sv.Equal (vrv x) (Sv.singleton x). 
Proof. rewrite /vrv /=;SvD.fsetdec. Qed.

Lemma vrv_recE t (r:rval t) s : Sv.Equal (vrv_rec s r) (Sv.union s (vrv r)).
Proof.
  elim: r s => //= [x | ?? r1 Hr1 r2 Hr2] s.
  + by rewrite vrv_var;SvD.fsetdec.
  rewrite /vrv /= !(Hr1,Hr2);SvD.fsetdec.
Qed.

Lemma vrv_pair t1 t2 (r1:rval t1) (r2:rval t2):
  Sv.Equal (vrv (Rpair r1 r2)) (Sv.union (vrv r1) (vrv r2)).
Proof. rewrite {1}/vrv /= !vrv_recE;SvD.fsetdec. Qed.

Definition incr dir (i0:word) := 
  match dir with
  | UpTo   => (i0 + 1)
  | DownTo => (i0 - 1)
  end.

Definition as_loop dir (w1 w2:word) := 
  match dir with UpTo => w1 <= w2 | DownTo => w2 <= w1 end.

Definition svmap_eq_except (s : Sv.t) (vm1 vm2 : svmap) :=
  forall x, ~Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 = vm2 [\ s ]" := (svmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Definition donotdep  (s : Sv.t) t (e:pexpr t) := 
  forall s1 s2, s1 = s2 [\ s] -> ssem_pexpr s1 e = ssem_pexpr s2 e.

Lemma swrite_nin  t (rv:rval t) (v:sst2ty t) z s:
  ~Sv.In z (vrv rv) ->
  ((swrite_rval s rv v).[z])%vmap = s.[z]%vmap.
Proof.
  elim: rv v s => /= [x | ??? Hr1 ? Hr2] v s;rewrite ?vrv_var ?vrv_pair => Hin.
  + by rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
  rewrite Hr1 ?Hr2 //;SvD.fsetdec.
Qed.

Lemma ssem_swrite_rval s (r:rval sword) w: 
  ssem_rval (swrite_rval s r w) r = w.
Proof. by case H : sword / r w => //= ?;rewrite Fv.setP_eq. Qed.

Lemma swrite_ssem_rval s (r:rval sword): swrite_rval s r (ssem_rval s r) = s.
Proof.
  apply Fv.map_ext=> x1;case H : sword / (r) => [ x2 | ] //=. 
  case: (x2 =P x1) => [ -> | /eqP ? ];first by rewrite Fv.setP_eq. 
  by rewrite Fv.setP_neq.   
Qed.

Lemma surj_SEstate s : {| semem := semem s; sevm := sevm s |} = s.
Proof. by case: s. Qed.

Lemma word_add1 (y x: word) : x < y -> nat_of_ord (x + 1)%R = (x + 1)%N.
Proof. 
  move=> Hlt;rewrite /= !modn_small //.
  by apply (@leq_ltn_trans y)=> //;rewrite -ltnS addnC.
Qed.

Lemma word_sub1 (y x: word) : y < x -> (x - 1)%R = (x - 1)%N :> nat.
Proof. 
case: x y => [[|x] ltx] [y lty] //=; rewrite ltnS => le_yx.
rewrite [1%%_]modn_small ?[in X in X%%_]modn_small //.
by rewrite !subn1 /= addSnnS modnDr modn_small // ltnW.
Qed.


  move=> Hlt;rewrite /=.
Admitted.

Lemma hoare_for_base (i:rval sword) dir (e1 e2:pexpr sword) I c:
  donotdep (vrv i) e1 ->
  donotdep (vrv i) e2 ->
  (forall (w1 w2 i0:word), 
    hoare (fun s => [/\ I s , ssem_pexpr s.(sevm) e1 = w1, ssem_pexpr s.(sevm) e2 = w2,
                    ssem_rval s.(sevm) i = i0 & w1 <= i0 <= w2])
          c
          (fun s => 
             ssem_rval s.(sevm) i = i0 /\ 
             let i1 := if i0 == (if dir is UpTo then w2 else w1) then i0 else incr dir i0 in
             let s' := {|semem := s.(semem); sevm := swrite_rval s.(sevm) i i1|} in
             [/\ I s', ssem_pexpr s'.(sevm) e1 = w1 & ssem_pexpr s'.(sevm) e2 = w2]))->
  hoare (fun s => 
           let w1 := ssem_pexpr s.(sevm) e1 in
           let w2 := ssem_pexpr s.(sevm) e2 in
           let i0 := if dir is UpTo then w1 else w2 in
           let s' := {|semem := s.(semem); sevm := swrite_rval s.(sevm) i i0|} in
           if w1 <= w2 then I s' else I s)
         [:: Cfor i (dir,e1,e2) c ]
         (fun s => 
            I s /\ 
            let w1 := ssem_pexpr s.(sevm) e1 in
            let w2 := ssem_pexpr s.(sevm) e2 in
            w1 <= w2 -> ssem_rval s.(sevm) i = if dir is UpTo then w2 else w1).
Proof.
  move=> He1 He2 Hc ??;set c' := Cfor _ _ _ => /ssem_iV Hsem.
  case: _ {-1}_ _ / Hsem (erefl c') => //.
  + move=> s i' dir' e1' e2' c0 w1 w2 Hw [] ?????;subst.
    by rewrite leqNgt Hw /=.
  move=> s s' i' dir' e1' e2' c0 w1 w2 Hw Hfor [] ?????;subst i' dir' e1' e2' c0.
  rewrite -/w1 -/w2 Hw => HI.
  have :  I s' /\ ssem_pexpr (sevm s') e1 = w1 /\ ssem_pexpr (sevm s') e2 = w2 /\
           ssem_rval (sevm s') i = if dir is UpTo then w2 else w1;last first.
  + by move=> [] ? [] -> [] ->.
  pose Pre i' dir' c' (w1' w2':word) s := 
      [/\ i' = i, dir' = dir , c' = c & (if dir is UpTo then w2' = w2 else w1' = w1) ] /\
      let w := if dir is UpTo then w1' else w2' in
      [/\ w1 <= w <= w2, ssem_pexpr (sevm s) e1 = w1 ,
      ssem_pexpr (sevm s) e2 = w2 &
      I {| semem := semem s; sevm := swrite_rval (sevm s) i w |} ].
  pose w1' := w1; pose w2' := w2.
  have : Pre i dir c w1' w2' s.
  + by rewrite /Pre;case : (dir) HI;rewrite leqnn Hw /=;auto.
  have Hie1 : forall s v, ssem_pexpr (swrite_rval s i v) e1 = ssem_pexpr s e1.
  + by move=> ??;apply He1=> ?; apply swrite_nin. 
  have Hie2 : forall s v, ssem_pexpr (swrite_rval s i v) e2 = ssem_pexpr s e2.
  + by move=> ??;apply He2=> ?; apply swrite_nin.
  elim: {HI c'} (Hfor : ssem_for i dir w1' w2' s c s')=> {w1' w2' Hfor}.
  + move=> i' dir' w c' s1 s2 Hs [] {Pre} [] ??? Heqw [] Hbound Hw1 Hw2 HI;subst i' dir' c'.
    have /= [] := Hc w1 w2 w _ _ Hs.
    + by rewrite Hie1 Hie2 ssem_swrite_rval;case: (dir) HI Hbound.
    by rewrite Hie1 Hie2; case: (dir) Heqw Hbound => {HI Hw1 Hw2 Hs} ? Hbound Hi -[];subst;
     rewrite eq_refl -[in X in X -> _]Hi swrite_ssem_rval surj_SEstate => HI Hw1 Hw2;auto.
  move=>  i' dir' w1'' w2'' c' s1 s2 s3 Hlt w Hs w1' w2' _ Hrec [] [] ??? Hw12;subst => /=.
  rewrite -/w => -[] Hbound Hw1 Hw2 HI;apply Hrec.
  have /= [] := Hc w1 w2 w _ _ Hs.
  + by rewrite Hie1 Hie2 ssem_swrite_rval;case: (dir) HI Hbound.
  rewrite Hie1 Hie2 /Pre=> {Hrec Hs HI Hw1 Hw2}.
  have /negPf -> : w != if dir is UpTo then w2 else w1.
  + by rewrite /w neq_ltn; case: (dir) Hw12=> <-;rewrite Hlt ?orbT.
  move=> Hi [] HI Hw1 Hw2;rewrite /w1' /w2' => {w1' w2'};split;split=> //.
  + by case: (dir) Hw12.
  + move: Hbound;rewrite /w=>{Hi HI w};case:(dir) Hw12 => <- /andP [] H1 H2.
    + by rewrite (word_add1 Hlt) /= addnC /= /addn/= -ltnS Hlt andbT ltnS;apply leqW.
    rewrite (word_sub1 Hlt). admit.
  by move: HI;rewrite /w /incr;case: (dir).
Admitted.

(* -------------------------------------------------------------------------- *)
(* ** Weakest Precondition                                                    *)
(* -------------------------------------------------------------------------- *)

Definition f2h (pm:pmap) (sm:smap) f : hpred := 
  fun se => ssem_sform {|pm := pm; sm := sm; vm := se.(sevm) |} f.

Definition osubst (s1 s2: vsubst) := 
  Mv.map (fun t => @subst_spexpr t s1) s2.

Lemma forall_iff A (P1 P2:A-> Prop): 
  (forall x, P1 x <-> P2 x) -> (forall (x:A), P1 x) <-> (forall x, P2 x).
Proof.
  by move=> H;split=> Hx x;move: (Hx x);rewrite H.
Qed.

Lemma osubst_Pe t (e:spexpr t) s1 s2 rho : 
  subst_spexpr (osubst s1 s2) e =[rho] 
  subst_spexpr s1 (subst_spexpr s2 e).
Proof.
  elim: e=> //= [?|???? He1| ????? He1 ? He2 
                | ?????? He1 ? He2 ? He3 | ?? He1 ? He2 ? He3];
  rewrite ?He1 ?He2 ?He3 //.
  by rewrite /osubst Mv.mapP.
Qed.

Lemma osubstP f s1 s2 rho : 
  subst_sform (osubst s1 s2) f =_[rho] 
  subst_sform s1 (subst_sform s2 f).
Proof.
  elim: f rho => /=
    [?|??|? He1|? He1 ? He2|? He1 ? He2|? He1 ? He2|?? He2 ? He3|?? He1] rho;
  rewrite ?He1 ?He2 ?He3 //.
  + by rewrite osubst_Pe.   + by rewrite osubst_Pe.
  + by rewrite osubst_Pe; case: (ssem_spexpr _);rewrite ?He2 ?He3.
  apply forall_iff =>?;apply He1.
Qed.

Definition mv0 := Mv.empty (fun x => Evar x).

Definition wp_assign {t1} (rv:rval t1) (e:spexpr t1) (s:vsubst) := 
  osubst (ewrite_rval mv0 rv e) s.
  
Lemma ssem_subst_spexpr st2 st1 t (e:spexpr t) s: 
  (forall (x:var), Sv.In x (fv e)    -> subst_spexpr s x =[st1, st2] x) ->
  (forall (x:svar), Ssv.In x (sfv e) -> x =[st1, st2] x) ->
  subst_spexpr s e =[st1,st2] e.
Proof.
  set fve := fv e; set sfve := sfv e. 
  have : Sv.Subset (fv e) fve by done.
  have : Ssv.Subset (sfv e) sfve by done.
  move: fve sfve=> fve sfve Hs Hv Hfv Hsfv. (* Enrico : comment on fait le let *)
  elim: e Hv Hs => //=
   [x | x | ?? o e1 He1 | ??? o e1 He1 e2 He2 
   | ???? o e1 He1 e2 He2 e3 He3 | ? e1 He1 e2 He2 e3 He3] Hv Hs. 
  + by rewrite Hfv //;move:Hv;rewrite fv_var;SvD.fsetdec. 
  + apply (Hsfv x);move:Hs;rewrite sfv_svar;SsvD.fsetdec. 
  + by rewrite He1.
  + by rewrite He1 ?He2 //;move: Hv Hs;rewrite fv_op2 sfv_op2;
     (SvD.fsetdec || SsvD.fsetdec). 
  + by rewrite He1 ?He2 ?He3 //;move: Hv Hs;rewrite fv_op3 sfv_op3;
     (SvD.fsetdec || SsvD.fsetdec).
  by rewrite He1 ?He2 ?He3 //; move: Hv Hs;rewrite fv_if sfv_if;
   (SvD.fsetdec || SsvD.fsetdec).
Qed.

Lemma ssem_subst_sform st2 st1 f s : 
  Mv.dft s = (fun x => Evar x) ->
  st1.(pm) = st2.(pm) -> st1.(sm) = st2.(sm) ->
  (forall (x:var), Sv.In x (ffv f) -> subst_spexpr s x =[st1, st2] x) ->
  (forall (x:var), Mv.indom x s -> Ssv.Empty (Ssv.inter (sfv s.[x]%mv) (sffv f))) ->
  subst_sform s f =_[st1, st2] f.
Proof.
  move=> Hdft; elim: f st2 st1=> //=
    [?|??|? Hf1|? Hf1 ? Hf2|? Hf1 ? Hf2|? Hf1 ? Hf2|?? Hf2 ? Hf3|x f1 Hf1] st2 st1 
    Hpm Hsm Hfv Hindom.
  + by rewrite (@ssem_subst_spexpr st2) //= Hsm.
  + by rewrite Hpm (@ssem_subst_spexpr st2) //= Hsm.
  + by rewrite (Hf1 st2).
  + rewrite (Hf1 st2) //. 
    + rewrite (Hf2 st2) //.
      + by move=> ??;apply Hfv;rewrite ffv_and;SvD.fsetdec. 
      by move=> ?/Hindom;rewrite sffv_and;SsvD.fsetdec. 
    + by move=> ??;apply Hfv;rewrite ffv_and;SvD.fsetdec. 
    by move=> ?/Hindom;rewrite sffv_and;SsvD.fsetdec. 
  + rewrite (Hf1 st2) //. 
    + rewrite (Hf2 st2) //.
      + by move=> ??;apply Hfv;rewrite ffv_or;SvD.fsetdec. 
      by move=> ?/Hindom;rewrite sffv_or;SsvD.fsetdec. 
    + by move=> ??;apply Hfv;rewrite ffv_or;SvD.fsetdec. 
    by move=> ?/Hindom;rewrite sffv_or;SsvD.fsetdec. 
  + rewrite (Hf1 st2) //. 
    + rewrite (Hf2 st2) //.
      + by move=> ??;apply Hfv;rewrite ffv_imp;SvD.fsetdec. 
      by move=> ?/Hindom;rewrite sffv_imp;SsvD.fsetdec. 
    + by move=> ??;apply Hfv;rewrite ffv_imp;SvD.fsetdec. 
    by move=> ?/Hindom;rewrite sffv_imp;SsvD.fsetdec. 
  + rewrite (@ssem_subst_spexpr st2) //= ?Hsm //.   
    + case: (ssem_spexpr _);[apply Hf2 | apply Hf3]=> //.
      + by move=> ??;apply Hfv;rewrite ffv_if;SvD.fsetdec. 
      + by move=> ?/Hindom;rewrite sffv_if;SsvD.fsetdec. 
      + by move=> ??;apply Hfv;rewrite ffv_if;SvD.fsetdec. 
      by move=> ?/Hindom;rewrite sffv_if;SsvD.fsetdec. 
    by move=> ??;apply Hfv;rewrite ffv_if;SvD.fsetdec. 
  apply forall_iff =>z;apply Hf1 => //=.
  + by rewrite Hsm.
  + move=> w Hin;have /= <- := Hfv w;last by rewrite ffv_forall.
    case: Mv.indom (Hindom w) (@Mv.indom_getP _ s w)=> 
      [/(_ (erefl _)) H _ | _ /(_ (erefl _)) -> /=];last by rewrite Hdft.
    apply ssem_spexpr_fv;constructor=> y Hy //=.
    apply /Msv.setP_neq/eqP.
    move:H;rewrite sffv_forall=> H;SsvD.fsetdec.
  move=> w /Hindom;rewrite sffv_forall;SsvD.fsetdec.
Qed.

Lemma ewrite_rvalP rho vm s t (rv:rval t) e: 
   (forall (x:var), ssem_spexpr rho s.[x]%mv = vm.[x]%vmap) ->
   forall (x:var),  
     ssem_spexpr rho (ewrite_rval s rv e).[x]%mv =
     (swrite_rval vm rv (ssem_spexpr rho e)).[x]%vmap.
Proof.
  elim: rv e s rho vm => [z | ?? r1 Hr1 r2 Hr2] e s rho vm Hrho x /=.
  + case: (z =P x)=> [<- | /eqP neq].
    + by rewrite Mv.setP_eq Fv.setP_eq.
    by rewrite Mv.setP_neq // Fv.setP_neq//;apply Hrho.
  have /= <- := mk_fstP e rho; apply Hr1=> ?.
  by have /= <- := mk_sndP e rho; apply Hr2.
Qed.

Lemma dft_ewrite_rval s t (rv:rval t) e:
   Mv.dft s = [eta Evar] ->
   Mv.dft (ewrite_rval s rv e) = [eta Evar].
Proof.
  elim: rv e s=> //= ?? r1 Hr1 r2 Hr2 e s Hs;auto.
Qed.

Lemma sfv_mkfst t1 t2 (e:spexpr (t1**t2)): Ssv.Subset (sfv (mk_fst e)) (sfv e).
Proof.
  rewrite /mk_fst.
  case: destr_pair (@destr_pairP _ _ e) => [[p1 p2] /(_ p1 p2) ->| _ ] //=.
  by rewrite sfv_op2;SsvD.fsetdec.
Qed.

Lemma sfv_mksnd t1 t2 (e:spexpr (t1**t2)): Ssv.Subset (sfv (mk_snd e)) (sfv e).
Proof.
  rewrite /mk_snd.
  case: destr_pair (@destr_pairP _ _ e) => [[p1 p2] /(_ p1 p2) ->| _ ] //=.
  by rewrite sfv_op2;SsvD.fsetdec.
Qed.

Lemma empty_ewrite_rval X t (rv:rval t) e s:
 Ssv.Empty (Ssv.inter (sfv e) X) ->
 (forall (x:var), Mv.indom x s ->  Ssv.Empty (Ssv.inter (sfv s.[x]%mv) X)) ->
 forall (x:var),  Mv.indom x (ewrite_rval s rv e) ->
     Ssv.Empty (Ssv.inter (sfv (ewrite_rval s rv e).[x]%mv) X).
Proof.
  elim: rv e s => //= [x | ?? r1 Hr1 r2 Hr2] e s Hemp Hs y.
  + by rewrite Mv.indom_setP; case: (boolP (_ == _)) => /= [/eqP <- _ | ?];
       rewrite ?Mv.setP_eq ?Mv.setP_neq;auto. 
  apply Hr1;first by have := @sfv_mkfst _ _ e;SsvD.fsetdec.
  move=> x;apply Hr2=>//;by have := @sfv_mksnd _ _ e;SsvD.fsetdec.
Qed.

Lemma wp_assignP rho t (rv:rval t) (e:spexpr t) f (s:vsubst):
  Ssv.Empty (Ssv.inter (sfv e) (sffv (subst_sform s f))) ->
  let v := ssem_spexpr rho e in
  let rho' := {| pm := rho.(pm); sm := rho.(sm); 
                 vm:= swrite_rval rho.(vm) rv v; |} in
  ssem_sform rho  (subst_sform (wp_assign rv e s) f) <->
  ssem_sform rho' (subst_sform s f).
Proof.
  move=> Hinter;rewrite /wp_assign osubstP;apply ssem_subst_sform => //.
  + by apply dft_ewrite_rval.
  + by move=> x _;apply ewrite_rvalP=> ?;rewrite /mv0 Mv.get0.
  apply empty_ewrite_rval => //.
Qed.

Lemma sfv_p2sp t (e:pexpr t) : Ssv.Empty (sfv (p2sp e)).
Proof.
  elim: e => //= *;rewrite ?sfv_var ?sfv_const ?sfv_op2 ?sfv_op3; SsvD.fsetdec.
Qed.
             
Lemma hoare_asgn pm sm {t1} (rv:rval t1) (e:pexpr t1) f (s:vsubst):
  hoare (f2h pm sm (subst_sform (wp_assign rv (p2sp e) s) f))
        [:: assgn rv e] 
        (f2h pm sm (subst_sform s f)).
Proof.
  rewrite /assgn; move=> s1_ s2_;set c := Cbcmd _=> /ssem_iV Hi.
  case: _ {-1}_ _ / Hi (erefl c) => // s1 s2 ? H [] ?; subst=> {c s1_ s2_}.
  case: H=> <- {s2};rewrite /f2h /=.
  apply iffLR; set rho := {| pm := pm; sm := sm; vm := sevm s1 |}.
  rewrite -(sem_p2sp e rho);apply: wp_assignP.
  by have := @sfv_p2sp _ e;SsvD.fsetdec.
Qed.

Definition wp_bcmd bc s := 
  match bc with
  | Assgn st rv e => ([::], (wp_assign rv (p2sp e) s))
  | Load  _ _     => ([::Cbcmd bc], s)
  | Store _ _     => ([::Cbcmd bc], s)
  end.

Definition merge_if (e:spexpr sbool) s1 s2 := 
  Mv.map2 (fun _ e1 e2 => Eif e e1 e2) s1 s2.

Definition wp_rec := 
  Eval lazy beta delta [cmd_rect instr_rect' list_rect] in
  @cmd_rect (fun _ => vsubst -> cmd * vsubst)
            (fun _ => vsubst -> cmd * vsubst)
            (fun _ _ _ => vsubst -> unit)
    (fun Q => ([::], Q))
    (fun i _ wpi wpc Q => 
       let (c_, R) := wpc Q in
       if nilp c_ then wpi R
       else (i::c_,R))
    wp_bcmd
    (fun e c1 c2 wpc1 wpc2 Q =>
       let (c1_, P1) := wpc1 Q in
       let (c2_, P2) := wpc2 Q in
       if nilp c1_ && nilp c2_ then
         ([::], merge_if (p2sp e) P1 P2)
       else ([::Cif e c1 c2], Q))
    (fun i rn c _ Q => ([::Cfor i rn c], Q))
    (fun _ _ x f a _ Q => ([::Ccall x f a], Q))
    (fun _ _ _ _ _ _ _ => tt).

(* TODO: move this *)
Definition cmd_Ind (P : cmd -> Prop) := 
  @cmd_ind P (fun _ _ _ => True).

Lemma r_wp_cons i c (p:vsubst) :
  wp_rec (i :: c) p = 
   if nilp (wp_rec c p).1 then wp_rec [::i] (wp_rec c p).2
   else (i::(wp_rec c p).1 , (wp_rec c p).2).
Proof.
  by move=> /=;case (wp_rec c p) => c_ R /=;case:nilP.
Qed.

Lemma r_wp_if e c1 c2 (p:vsubst) : 
  wp_rec [::Cif e c1 c2] p = 
   if nilp (wp_rec c1 p).1 && nilp (wp_rec c2 p).1 then 
     let p1 := (wp_rec c1 p).2 in
     let p2 := (wp_rec c2 p).2 in
     ([::], merge_if (p2sp e) p1 p2)
   else ([::Cif e c1 c2], p).
Proof.
  move=> /=;fold (wp_rec c1 p) (wp_rec c2 p). 
  by case: (wp_rec c1 p) => ??; case: (wp_rec c2 p) => ??.
Qed.

Lemma merge_ifP_e e s1 s2 t (e':spexpr t) rho: 
  (subst_spexpr (merge_if (p2sp e) s1 s2) e') =[rho]
  if ssem_pexpr rho.(vm) e then subst_spexpr s1 e' else subst_spexpr s2 e'.
Proof.
  by elim:e' => //=
    [?|?|?|?|???? He1|????? He1 ? He2|?????? He1 ? He2 ? He3|?? He1 ? He2 ? He3];
    rewrite ?He1 ?He2 ?He3 // /merge_if ?Mv.map2P /= ?sem_p2sp;
    case: (ssem_pexpr (vm rho) e).
Qed.   

Lemma merge_ifP e s1 s2 f rho: 
  (subst_sform (merge_if (p2sp e) s1 s2) f) =_[rho]
  if ssem_pexpr rho.(vm) e then subst_sform s1 f else subst_sform s2 f.
Proof.
  elim: f rho=> /=
    [?|??|? Hf1|? Hf1 ? Hf2|? Hf1 ? Hf2|? Hf1 ? Hf2|?? Hf1 ? Hf2|x ? Hf1] rho;
    rewrite ?merge_ifP_e ?Hf1 ?Hf2 /=; case Heq: (ssem_pexpr (vm rho) e)=> //=.
  + by case: (ssem_spexpr _);rewrite ?Hf1 ?Hf2 ?Heq. 
  + by case: (ssem_spexpr _);rewrite ?Hf1 ?Hf2 ?Heq. 
  + by apply forall_iff=> ?;rewrite Hf1 Heq. 
  by apply forall_iff=> ?;rewrite Hf1 Heq. 
Qed.

Lemma wp_rec_tl pm sm c (f:sform) (s:vsubst) : exists tl, 
   c = (wp_rec c s).1 ++ tl /\
   hoare (f2h pm sm (subst_sform (wp_rec c s).2 f)) tl (f2h pm sm (subst_sform s f)).
Proof.
  elim /cmd_Ind : c s => [ | i c Hi Hc| bc| e c1 c2 Hc1 Hc2| i rn c Hc|?? x g a _ | //] s.
  + by exists ([::]);split=>//=;apply hoare_skip.
  + rewrite r_wp_cons;elim (Hc s)=> {Hc} tlc [Heqc Hwpc].
    case: nilP Heqc => Heq Heqc.
    + elim (Hi (wp_rec c s).2)=> tl [Htl Hwp] ;exists (tl ++ c).
      rewrite catA -Htl;split=>//.
      by rewrite {2} Heqc Heq cat0s;apply:hoare_seq Hwp Hwpc.
    by exists tlc=> /=;rewrite -Heqc.
  + case: bc => [? r e | ?? | ??] /=; try 
      by exists [::];split=>//;apply:hoare_skip.
    exists  [:: Cbcmd (Assgn r e)];split=>//.
    by apply hoare_asgn.
  + rewrite r_wp_if;case: andP=> /=;last
      by exists [::];split=>//;apply:hoare_skip.
    move=> [/nilP Heq1 /nilP Heq2].
    elim (Hc1 s) => {Hc1} tl1;elim (Hc2 s) => {Hc2} tl2.
    rewrite Heq1 Heq2 !cat0s=> -[<- Hc2] [<- Hc1].
    exists [:: Cif e c1 c2];split=>//.
    apply: hoare_if.
    + apply: (hoare_conseq _ _ Hc1)=> // se [] He.
      by apply iffRL;rewrite /f2h merge_ifP /= He.
    apply: (hoare_conseq _ _ Hc2)=> // se [] /negPf He.
    by apply iffRL;rewrite /f2h merge_ifP /= He.
  + by exists [::];split=>//;apply:hoare_skip.
  by exists [::];split=>//;apply:hoare_skip.
Qed.
  

Fixpoint osubst_spexpr st (s : vsubst) (pe : spexpr st) :=
  match pe in spexpr st_ return spexpr st_ with
  | Evar          v              => s.[v]%mv
  | Esvar         x              => x
  | Econst        c              => Econst c
  | Ebool         b              => Ebool  b
  | Eapp1 _ _     op pe1         =>
    mk_op1 op (osubst_spexpr s pe1)
  | Eapp2 _ _ _   op pe1 pe2     => 
    mk_op2 op (osubst_spexpr s pe1) (osubst_spexpr s pe2)
  | Eapp3 _ _ _ _ op pe1 pe2 pe3 => 
    mk_op3 op (osubst_spexpr s pe1) (osubst_spexpr s pe2) (osubst_spexpr s pe3)
  | Eif _ b pe1 pe2       => 
    mk_if (osubst_spexpr s b) (osubst_spexpr s pe1) (osubst_spexpr s pe2)
  end.

Definition mk_fnot f := 
  match f with
  | Fbool e => Fbool (mk_not e)
(*  | Fnot  f => f *)
  | _       => Fnot f
  end.

(* Inductive fbool := 
  | FBbool : bool -> fbool
  | FBexpr : spexpr sbool -> fbool
  | FBnone : fbool. *)

Definition is_fbool f := 
  match f with
  | Fbool e => 
    match e with
    | Ebool b => Some b
    | _       => None
    end
  | _       => None
  end.

Definition mk_fand f1 f2 := 
  match is_fbool f1, is_fbool f2 with
  | Some b, _ => if b then f2 else Fbool false
  | _, Some b => if b then f1 else Fbool false
  | _, _ => Fand f1 f2
  end.

Definition mk_for f1 f2 := 
  match is_fbool f1, is_fbool f2 with
  | Some b, _ => if b then Fbool true else f2
  | _, Some b => if b then Fbool true else f1
  | _, _ => For f1 f2
  end.

Definition mk_fimp f1 f2 := 
  match is_fbool f1, is_fbool f2 with
  | Some b, _ => if b then f2 else Fbool true 
  | _, Some b => if b then Fbool true else mk_fnot f1
  | _, _ => Fimp f1 f2
  end.

(* TODO: add optimisation f1 = f2 -> f1 *)
Definition mk_fif e f1 f2 :=
  match e with
  | Ebool b => if b then f1 else f2
  | _       => Fif e f1 f2
  end.

Fixpoint osubst_sform (s:vsubst) (f:sform) := 
  match f with
  | Fbool   e     => Fbool (osubst_spexpr s e)
  | Fpred   p  e  => @Fpred p (osubst_spexpr s e)
  | Fnot    f     => mk_fnot  (osubst_sform s f)
  | Fand    f1 f2 => mk_fand  (osubst_sform s f1) (osubst_sform s f2) 
  | For     f1 f2 => mk_for   (osubst_sform s f1) (osubst_sform s f2) 
  | Fimp    f1 f2 => mk_fimp  (osubst_sform s f1) (osubst_sform s f2) 
  | Fif   b f1 f2 => mk_fif   (osubst_spexpr s b) (osubst_sform s f1) (osubst_sform s f2) 
  | Fforall x  f  => Fforall x (osubst_sform s f)
  end.

Definition optimize_spexpr t (e:spexpr t) := osubst_spexpr vsubst_id e.

Lemma osubstP_e t (e:spexpr t) s rho : osubst_spexpr s e =[rho] subst_spexpr s e.
Proof.
  elim: e => //=
    [???? He1|????? He1 ? He2|?????? He1 ? He2 ? He3|?? He1 ? He2 ? He3];
    rewrite ?mk_op1P ?mk_op2P ?mk_op3P ?mk_ifP /= ?He1 ?He2 ?He3 //.
Qed.

Lemma optimizeP_e t (e:spexpr t) rho : optimize_spexpr e =[rho] e.
Proof.
  rewrite /optimize_spexpr osubstP_e. 
  by apply ssem_subst_spexpr.
Qed.

Lemma mk_fnotP f rho : mk_fnot f =_[rho] (Fnot f).
Proof.
  case: f => //= e;symmetry;rewrite ?mk_notP //=;apply rwP;apply negP.
Qed.

Lemma is_fboolP f b : is_fbool f = Some b -> f = Fbool b.
Proof. by case: f => // e; jm_destr e => // -[] ->. Qed.

Lemma mk_fandP f1 f2 rho : mk_fand f1 f2 =_[rho] Fand f1 f2.
Proof.
  rewrite /mk_fand;case: (is_fbool f1) (@is_fboolP f1) => [b /(_ b (erefl _)) ->| _] /=.
  + by case b=> /=;intuition. 
  case: (is_fbool f2) (@is_fboolP f2) => [b /(_ b (erefl _)) ->| _] //=.
  by case b=> /=;intuition. 
Qed.

Lemma mk_forP f1 f2 rho : mk_for f1 f2 =_[rho] For f1 f2.
Proof.
  rewrite /mk_for;case: (is_fbool f1) (@is_fboolP f1) => [b /(_ b (erefl _)) ->| _] /=.
  + by case b=> /=;intuition. 
  case: (is_fbool f2) (@is_fboolP f2) => [b /(_ b (erefl _)) ->| _] //=.
  by case b=> /=;intuition. 
Qed.

Lemma mk_fimpP f1 f2 rho : mk_fimp f1 f2 =_[rho] Fimp f1 f2.
Proof.
  rewrite /mk_fimp;case: (is_fbool f1) (@is_fboolP f1) => [b /(_ b (erefl _)) ->| _] /=.
  + by case b=> /=;intuition. 
  case: (is_fbool f2) (@is_fboolP f2) => [b /(_ b (erefl _)) ->| _] //=.
  by case b;rewrite /= ?mk_fnotP /=;intuition. 
Qed.

Lemma mk_fifP e f1 f2 rho : mk_fif e f1 f2 =_[rho] Fif e f1 f2.
Proof.
  rewrite /mk_fif;jm_destr e => //.
  match goal with |- (if ?b then _ else _) =_[_] _ => by case: b end. (* Enrico *)
Qed.

Lemma osubst_sformP f s rho: osubst_sform s f =_[rho] subst_sform s f.
Proof.
  elim:f rho => 
    [?|??|? He1|? He1 ? He2|? He1 ? He2|? He1 ? He2|?? He1 ? He2|?? He1] rho //=;
  rewrite ?mk_fnotP ?mk_fandP ?mk_forP ?mk_fimpP ? mk_fifP /= ?osubstP_e ?He1 ?He2 //.
  + by case: ifP. 
  by apply forall_iff.
Qed.

Definition init_vsubst f := 
  let fv := ffv f in
  Sv.fold (fun x s => s.[x <- Evar x]%mv) fv (vsubst_id).

Lemma init_vsubst_dft f : 
  Mv.dft (init_vsubst f) = [eta Evar].
Proof.
  by rewrite /init_vsubst SvP.MP.fold_spec_right;elim: List.rev.
Qed.

Lemma init_vsubst_get f x : 
  (init_vsubst f).[x]%mv = Evar x.
Proof.
  rewrite /init_vsubst; apply SvP.MP.fold_rec => // z s s1 s2 _ ? ?.
  by case (z =P x) => [-> | /eqP ?] ?;rewrite ?Mv.setP_eq ?Mv.setP_neq.
Qed.
   
Definition wp c f := 
  let s  := init_vsubst f in
  let (c', s') := wp_rec c s in
  let s' := Mv.map (fun _ e => optimize_spexpr e) s' in
  (c', osubst_sform s' f).

Lemma subst_spexpr_eq s1 s2 t (e:spexpr t) rho:
  (forall x : var, (s1.[x])%mv =[rho] (s2.[x])%mv) ->
   subst_spexpr s1 e =[rho] subst_spexpr s2 e.
Proof.
  by move=> Hs;elim: e => //=
   [???? He1|????? He1 ? He2|?????? He1 ? He2 ? He3|?? He1 ? He2 ? He3];
  rewrite ?He1 ?He2 ?He3.
Qed.

Lemma subst_sform_eq s1 s2 f rho:
  (forall rho (x:var), s1.[x]%mv =[rho] s2.[x]%mv) -> 
  subst_sform s1 f =_[rho] subst_sform s2 f.
Proof.
  move=> Hs.
  elim: f rho=> /=
   [?|??|? Hf1|? Hf1 ? Hf2|? Hf1 ? Hf2|? Hf1 ? Hf2|?? Hf1 ? Hf2|?? Hf1] rho;
  rewrite ?(@subst_spexpr_eq s1 s2) // ?Hf1 ?Hf2 //.
  + by case: ifP=>?;rewrite ?Hf1 ?Hf2.
  apply forall_iff=> x;apply Hf1.
Qed.

Lemma hoare_wp pm sm P c Q : 
   hoare P (wp c Q).1 (f2h pm sm (wp c Q).2) -> 
   hoare P c (f2h pm sm Q).
Proof.
  rewrite /wp.
  move=> H1;elim: (@wp_rec_tl pm sm c Q (init_vsubst Q))=> tl [{2}->] H2.
  apply (@hoare_conseq P (f2h pm sm (subst_sform (init_vsubst Q) Q))) => //.
  + move=> rho;apply iffRL;symmetry.
    rewrite /f2h;apply ssem_subst_sform => //.
    + by apply init_vsubst_dft.
    + move=> ??;apply ssem_subst_spexpr=> //= x ?.
      by rewrite init_vsubst_get.
    by move=> ?;rewrite init_vsubst_get sfv_var;SsvD.fsetdec.
  apply: hoare_seq H2; move: H1;case: wp_rec => [c' s'] /=.
  apply: hoare_conseq=> // s;rewrite /f2h.
  apply iffRL;rewrite osubst_sformP.
  by apply subst_sform_eq=> rho x;rewrite Mv.mapP;rewrite optimizeP_e.
Qed.

Lemma ssem_sform_fv f st1 st2 : 
  st1.(pm) = st2.(pm) -> st1 ={ ffv f, sffv f} st2 -> f =_[ st1, st2] f.
Proof.
  elim: f st1 st2=> //= 
    [ ? | ?? | f1 Hf1 | f1 Hf1 f2 Hf2 | f1 Hf1 f2 Hf2 | f1 Hf1 f2 Hf2 
    | ? f1 Hf1 f2 Hf2 | x f1 Hf1] st1 st2 Hpm.
  + by rewrite ffv_bool sffv_bool=> H;rewrite -(ssem_spexpr_fv H).
  + by rewrite Hpm ffv_pred sffv_pred=> H;rewrite -(ssem_spexpr_fv H). 
  + by rewrite ffv_not sffv_not=> H;rewrite (Hf1 _ _ Hpm H).
  + by rewrite ffv_and sffv_and=> H;rewrite (Hf1 _ _ Hpm) ?(Hf2 _ _ Hpm) //;
    apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
  + by rewrite ffv_or sffv_or=> H;rewrite (Hf1 _ _ Hpm) ?(Hf2 _ _ Hpm) //;
    apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
  + by rewrite ffv_imp sffv_imp=> H;rewrite (Hf1 _ _ Hpm) ?(Hf2 _ _ Hpm) //;
    apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
  + rewrite ffv_if sffv_if=> H;rewrite (@ssem_spexpr_fv _ _ st1 st2);
     last by apply: eq_on_m H=> //;(SvD.fsetdec || SsvD.fsetdec).
    (* case: ssem_spexpr.  (Enrico : Bug ?) *)
    case: (ssem_spexpr _);[apply Hf1 | apply Hf2]=>//;apply: eq_on_m H;
    (SvD.fsetdec || SsvD.fsetdec).
  rewrite ffv_forall sffv_forall=> H; apply forall_iff=> v;apply Hf1=> //=.
  constructor=> /= z Hz;first by apply H.
  case: (x =P z) => [<- | /eqP neq];rewrite ?Msv.setP_eq // ?Msv.setP_neq //.
  apply H;move: neq=> /eqP;SsvD.fsetdec.
Qed.

Definition init_st m t (rv:rval t) (v:sst2ty t) := 
  {| semem := m; sevm := swrite_rval svmap0 rv v |}.

Definition f2fpred pm sm P t (rv:rval t) := 
  fun m (v:sst2ty t)  => f2h pm sm P (init_st m rv v).

Fixpoint read_rval t (rv:rval t) : Sv.t := 
  match rv with
  | Rvar x            => Sv.singleton x
  | Rpair _ _ rv1 rv2 => Sv.union (read_rval rv1) (read_rval rv2)
  end.
 
Record shoaref pm sm t tr Pf (f:fundef t tr) Qf := {
  sh_spec : hoaref (f2fpred pm sm Pf f.(fd_arg)) f (f2fpred pm sm Qf f.(fd_res));
  sh_Pf : Sv.subset (ffv Pf) (read_rval f.(fd_arg));
  sh_Qf : Sv.subset (ffv Qf) (read_rval f.(fd_res));
}.
  
Definition wp_call t tr (x:rval tr) (f:fundef t tr) (e:pexpr t)
   (Pf Qf Q:sform) := 
  let id := fresh_svar (Ssv.union (sffv Qf) (sffv Q)) in
  let v  := SVar tr id in
  let p1 := subst_sform (ewrite_rval mv0 f.(fd_arg) (p2sp e)) Pf in
  let q  := subst_sform (ewrite_rval mv0 x v) Q in
  let qf := subst_sform (ewrite_rval mv0 f.(fd_res) v) Qf in
  Fand p1 (Fforall v (Fimp qf q)).

Lemma swrite_nin  t (rv:rval t) (v:sst2ty t) z s:
  ~Sv.In z (read_rval rv) ->
  ((swrite_rval s rv v).[z])%vmap = s.[z]%vmap.
Proof.
  elim: rv v s => /= [x | ??? Hr1 ? Hr2] v s Hin.
  + by rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
  rewrite Hr1 ?Hr2 //;SvD.fsetdec.
Qed.

Lemma swrite_dep t (rv:rval t) (v:sst2ty t) z s1 s2:
  Sv.In z (read_rval rv) ->
  ((swrite_rval s1 rv v).[z])%vmap = ((swrite_rval s2 rv v).[z])%vmap.
Proof.
  elim: rv v s1 s2 => /= [x | ?? r1 Hr1 r2 Hr2] v s1 s2 Hin.
  by have <- : x = z;[SvD.fsetdec | rewrite !Fv.setP_eq].
  case: (SvP.MP.In_dec z (read_rval r1)) => Hz;first by apply Hr1.
  rewrite swrite_nin //;symmetry;rewrite swrite_nin //.
  apply Hr2;SvD.fsetdec.
Qed.

Lemma subst_spexpr_svar (z:svar) (x:rval z.(svtype)) (v:sst2ty z.(svtype))
   pm sm vm t (e:spexpr t): 
  ~ Ssv.In z (sfv e) ->
   ssem_spexpr
     {| pm := pm; sm := (sm.[z <- v])%msv; vm := vm |}
     (subst_spexpr (ewrite_rval mv0 x z) e) =
   ssem_spexpr {| pm := pm; sm := sm; vm := (swrite_rval vm x  v) |} e.
Proof.
  move=> Hin; apply ssem_subst_spexpr=> y Hy /=.
  + by rewrite (@ewrite_rvalP _ vm) //= Msv.setP_eq.   
  by rewrite Msv.setP_neq //;apply /eqP=> H;apply Hin;rewrite H.
Qed.

Lemma subst_sform_svar (z:svar) (x:rval z.(svtype)) (v:sst2ty z.(svtype)) pm sm vm f: 
   ~Ssv.In z (sffv f) -> 
   ssem_sform {|pm := pm; sm := sm.[z <- v]%msv; vm := vm|} 
           (subst_sform (ewrite_rval mv0 x z) f) <->
   ssem_sform {|pm := pm; sm := sm; vm := swrite_rval vm x v |} f.
Proof.
  elim: f pm sm vm=>
   [?|??|? Hf1|? Hf1 ? Hf2|? Hf1 ? Hf2|? Hf1 ? Hf2|?? Hf1 ? Hf2|u ? Hf1] /= pm sm vm.
  + by rewrite sffv_bool=> Hin;rewrite subst_spexpr_svar.
  + by rewrite sffv_pred=> Hin;rewrite subst_spexpr_svar.
  + by rewrite sffv_not=> Hin;rewrite Hf1 /=.
  + by rewrite sffv_and=> Hin;rewrite Hf1 ?Hf2 //;SsvD.fsetdec.
  + by rewrite sffv_or=> Hin;rewrite Hf1 ?Hf2 //;SsvD.fsetdec.
  + by rewrite sffv_imp=> Hin;rewrite Hf1 ?Hf2 //;SsvD.fsetdec.
  + rewrite sffv_if=> Hin;rewrite subst_spexpr_svar;last by SsvD.fsetdec.
    by case:ifP;rewrite ?Hf1 ?Hf2 //;SsvD.fsetdec.
  rewrite sffv_forall=> Hin;apply forall_iff=> y.
  rewrite -Hf1;last by SsvD.fsetdec.
  apply ssem_sform_fv => //;constructor=> w Hw //=.
  case: (z =P w) => [Hzw | /eqP neq].
  + subst;rewrite Msv.setP_eq Msv.setP_neq ?Msv.setP_eq //.
    by apply /eqP;SsvD.fsetdec.
  case: (u =P w) => [Huw | /eqP neq'].
  + by subst;rewrite Msv.setP_eq Msv.setP_neq ?Msv.setP_eq //.
  by rewrite ?Msv.setP_neq //.
Qed.

Lemma fresh_svarP t s: ~ Ssv.In {|svtype := t; svname := fresh_svar s|} s.
Proof.
  rewrite /fresh_svar.
  have Hf: forall p x, Ssv.In x s -> 
    (x.(svname) <= (Ssv.fold
                     (fun (v : svar) (m : positive) =>
                      if (svname v <? m)%positive then m else svname v) s p))%positive.
  + move=> p x;apply SsvP.MP.fold_rec.
    + by move=> ? He H;elim (He _ H).
    move=> {p} z p s1 s2 _ Hnin Ha Hrec /Ha [-> | Hn].
    + by case: Pos.ltb_spec0=> [|_];[ apply: Pos.lt_le_incl | apply Pos.le_refl].
    apply (Pos.le_trans _ p);first by auto.
    by case: Pos.ltb_spec0=> [_|?];[apply Pos.le_refl | rewrite Pos.le_nlt].
  by move=> /(Hf xH) /=;rewrite Pos.le_succ_l;apply Pos.lt_irrefl.
Qed.

Lemma fv_mk_fst t1 t2 (e:spexpr (t1**t2)) : 
  Sv.Subset (fv (mk_fst e)) (fv e).
Proof.
  rewrite /mk_fst;case: destr_pair (@destr_pairP _ _ e) =>
    [[e1 e2] /(_ _ _ (erefl _)) -> | _ ]; rewrite ?fv_op2 ?fv_op1 //;SvD.fsetdec.
Qed.

Lemma fv_mk_snd t1 t2 (e:spexpr (t1**t2)) : 
  Sv.Subset (fv (mk_snd e)) (fv e).
Proof.
  rewrite /mk_snd;case: destr_pair (@destr_pairP _ _ e) =>
    [[e1 e2] /(_ _ _ (erefl _)) -> | _ ]; rewrite ?fv_op2 ?fv_op1 //;SvD.fsetdec.
Qed.

Lemma ewrite_nin  t (rv:rval t) (v:spexpr t) z s:
  ~Sv.In z (read_rval rv) ->
  (ewrite_rval s rv v).[z]%mv = s.[z]%mv.
Proof.
  elim: rv v s => /= [x | ??? Hr1 ? Hr2] v s Hin.
  + by rewrite Mv.setP_neq //;apply /eqP; SvD.fsetdec.
  rewrite Hr1 ?Hr2 //;SvD.fsetdec.
Qed.

Lemma fv_subst_var t (rv:rval t) e x s :
   Sv.In x (read_rval rv) ->
   Sv.Subset (fv ((ewrite_rval s rv e).[x])%mv) (fv e).
Proof.
  elim: rv e s => /= [z | ?? r1 Hr1 r2 Hr2] e s Hin.
  + have <- : z = x by SvD.fsetdec.
    by rewrite Mv.setP_eq. 
  case: (SvP.MP.In_dec x (read_rval r1)) => Hx.
  + by move: (Hr1 (mk_fst e) (ewrite_rval s r2 (mk_snd e)) Hx) (@fv_mk_fst _ _ e);SvD.fsetdec.
  have Hin2 : Sv.In x (read_rval r2) by SvD.fsetdec.
  by rewrite ewrite_nin //; move: (Hr2 (mk_snd e) s Hin2) (@fv_mk_snd _ _ e);SvD.fsetdec.    
Qed.

Lemma SubsetUs (s1 s2 s:Sv.t) : 
  Sv.Subset (Sv.union s1 s2) s -> Sv.Subset s1 s /\ Sv.Subset s2 s.
Proof. split;SvD.fsetdec. Qed.
                
Lemma fv_subst_spexpr t' (e':spexpr t') t (rv:rval t) e :
  Sv.Subset (fv e') (read_rval rv) ->
  Sv.Subset (fv (subst_spexpr (ewrite_rval mv0 rv e) e')) (fv e).
Proof.
  elim: e'=> //= [?|?|?|?|????? He1 ? He2|?????? He1 ? He2 ? He3|?? He1 ? He2 ? He3].
  + by rewrite fv_var => ?;apply: fv_subst_var;SvD.fsetdec.
  + by rewrite fv_svar;SvD.fsetdec.
  + by rewrite fv_const;SvD.fsetdec.
  + by rewrite fv_bool;SvD.fsetdec.
  + by rewrite !fv_op2=> /SubsetUs [] /He1 ? /He2;SvD.fsetdec.
  + by rewrite !fv_op3=> /SubsetUs [] /He1 ? /SubsetUs [] /He2 ? /He3;SvD.fsetdec.
  by rewrite !fv_if=> /SubsetUs [] /He1 ? /SubsetUs [] /He2 ? /He3;SvD.fsetdec.
Qed.

Lemma ffv_subst_sform t (rv:rval t) e f:
  Sv.Subset (ffv f) (read_rval rv) ->
  Sv.Subset (ffv (subst_sform (ewrite_rval mv0 rv e) f)) (fv e).
Proof.
  elim: f=> [?|??|? Hf1|? Hf1 ? Hf2|? Hf1 ? Hf2|? Hf1 ? Hf2|b ? Hf1 ? Hf2|u ? Hf1] /=.
  + by rewrite !ffv_bool => /fv_subst_spexpr.
  + by rewrite !ffv_pred => /fv_subst_spexpr.
  + by rewrite !ffv_not => /Hf1.
  + by rewrite !ffv_and=> /SubsetUs [] /Hf1 ? /Hf2;SvD.fsetdec.
  + by rewrite !ffv_or=> /SubsetUs [] /Hf1 ? /Hf2;SvD.fsetdec.
  + by rewrite !ffv_imp=> /SubsetUs [] /Hf1 ? /Hf2;SvD.fsetdec.
  + by rewrite !ffv_if => /SubsetUs [] /fv_subst_spexpr -/(_ e) ? /SubsetUs [] /Hf1 ? /Hf2;
    SvD.fsetdec.
  by rewrite !ffv_forall.
Qed.

Lemma wp_callP Pf Qf pm sm t tr c x (f:fundef t tr) e P Q :
  shoaref pm sm Pf f Qf ->
  hoare P c (f2h pm sm (wp_call x f e Pf Qf Q)) ->
  hoare P (rcons c (Ccall x f e)) (f2h pm sm Q).
Proof.
  move=> Hf Hc.
  apply (hoare_call_seq (sh_spec Hf)). 
  apply: hoare_conseq Hc=> // s -[] HPf HQ;rewrite /f2fpred /f2h;split.
  + set st2 := (st in ssem_sform st _); move: HPf.
    set st1 := (st in ssem_sform st _ -> _).
    set st3 := {| pm := pm; sm := sm; 
                  vm := swrite_rval (sevm s) (fd_arg f) (ssem_pexpr (sevm s) e) |}.
    rewrite (@ssem_subst_sform st3) //.
    + apply iffRL;apply ssem_sform_fv => //;constructor=>//.
      move=> z Hin /=;apply swrite_dep. 
      by have /SvD.F.subset_2 := sh_Pf Hf;SvD.fsetdec.
    + by apply dft_ewrite_rval.
    + by move=> z Hin /=;rewrite -(@sem_p2sp _ e st1);apply ewrite_rvalP.
    by apply empty_ewrite_rval;have:= @sfv_p2sp _ e;SsvD.fsetdec.
  move=> m' v;move: (HQ v).
  have := @fresh_svarP tr (Ssv.union (sffv Qf) (sffv Q)).
  rewrite /init_st /=;set z := SVar _ _ => Hz.
  rewrite  -!(@subst_sform_svar z).
  move=> H1 H2;apply H1;move: H2.
  + apply iffRL;apply ssem_sform_fv=> //=;constructor=> w Hw //=.
    have /SvD.F.subset_2 /ffv_subst_sform -/(_ z):= sh_Qf Hf.
    rewrite (fv_svar z). (* Enrico Bug? : rewrite fv_svar *)
    by SvD.fsetdec.
  + by SsvD.fsetdec.
  by SsvD.fsetdec.
Qed.

Lemma swrite_rval_ssem x t (rv:rval t) s s': 
  Sv.In x (read_rval rv) ->
  (swrite_rval s' rv (ssem_rval s rv)).[x]%vmap = s.[x]%vmap.
Proof.
  elim: rv s' => [w | ?? r1 Hr1 r2 Hr2] s' /= Hin.
  have <- : w = x by SvD.fsetdec.
  + by rewrite Fv.setP_eq.
  case: (SvP.MP.In_dec x (read_rval r1)) => Hx;first by apply Hr1.
  by rewrite swrite_nin // Hr2 //;SvD.fsetdec.
Qed.

Lemma shoare_fun pm sm t tr (f:fundef t tr)  Pf Qf :
  Sv.subset (ffv Pf) (read_rval f.(fd_arg)) ->
  Sv.subset (ffv Qf) (read_rval f.(fd_res)) ->
  hoare (f2h pm sm Pf) f.(fd_body) (f2h pm sm Qf) ->
  shoaref pm sm Pf f Qf.
Proof.
  move=> HPf HQf Hbody;constructor => //.
  move: HPf HQf => /SvD.F.subset_2 HPf /SvD.F.subset_2 HQf.
  rewrite /f2fpred /f2h /init_st=> m m' va vr H. 
  inversion H;subst=>{H}. inversion H4;subst=>{H4}. 
  inversion H9;subst=>{H9} /=;subst => Hpre.
  pose st2 :=  {| pm := pm; sm := sm; vm := (sevm es') |}.
  rewrite (@ssem_sform_fv Qf _ st2) //.
  + apply: (Hbody _ _ H7);move: Hpre;rewrite /f2h /es /=.
    apply iffRL; apply ssem_sform_fv=> //;constructor=> //= x Hin.
    by apply swrite_dep;SvD.fsetdec.
  constructor=> //= x Hin. 
  apply swrite_rval_ssem;SvD.fsetdec.
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Tactics                                                                 *)
(* -------------------------------------------------------------------------- *)


Ltac skip := try apply:hoare_skip.

Ltac wp_core := 
  match goal with
  | |- hoare ?P ?c (f2h ?pm ?sm ?Q) =>
    let c1 := fresh "c" in
    let q1 := fresh "Q" in
    let c2 := fresh "c" in
    let q2 := fresh "Q'" in
    pose c1 := c; pose q1 := Q;
    apply: (@hoare_wp pm sm P c1 q1);
    match eval vm_compute in (wp c1 q1) with
    | (?c', ?Q') => 
      pose c2 := c'; pose q2 := Q';
      (have -> /=: (wp c1 q1) = (c2,q2) by vm_cast_no_check (erefl (c2,q2)));
      rewrite /c1 /q1 /c2 /q2 => {c1 q1 c2 q2}
    end
  | _ => fail "wp_core: not a hoare judgment"
  end.


(* -------------------------------------------------------------------------- *)
(* ** Tests                                                                   *)
(* -------------------------------------------------------------------------- *)

Definition x := {| vtype := sword; vname := "x" |}.
Definition y := {| vtype := sword; vname := "y" |}.
Definition z := {| vtype := sword; vname := "z" |}.

Definition w0 : N := 0.
Definition w1 : N := 1.

Definition c := 
  [:: assgn x w0;
      assgn y w1;
      Cif (Papp2 Oeq x w1) [::assgn z x] [::assgn z y] ].

Definition pmap0 : pmap := @Msv.empty sst2pred (fun _ _ => True).


Lemma c_ok : 
  hoare (f2h pmap0 msv0 (Fbool true)) c (f2h pmap0 msv0 (Fbool (Eapp2 Oand (Eapp2 Oeq x 0%num) 
                                                             (Eapp2 Oeq y 1%num)))).
Proof.
  wp_core. 
  by skip.
Qed.

Definition c' := 
  [:: assgn x w0;
      assgn y w1;
      Cif (Papp2 Oeq x x) [::assgn z x] [::assgn z y] ].

Lemma c_ok1 : 
  hoare (f2h pmap0 msv0 (Fbool true)) c' 
        (f2h pmap0 msv0 (Fbool (Eapp2 Oand (Eapp2 Oeq x 0%num) 
                                           (Eapp2 Oeq z 0%num)))).
Proof.
  wp_core. by skip.
Qed.
