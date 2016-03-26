(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import word dmasm_utils dmasm_type dmasm_var dmasm_sem 
               dmasm_sem_props dmasm_Ssem dmasm_Ssem_props symbolic_expr symbolic_expr_opt.

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
  hoare (fun s1 => forall s2,  ssem_bcmd s1 bc = ok s2 -> P s2) [::Cbcmd bc] P.
Proof.
  move=> ??;set c := Cbcmd _ => /ssem_iV s.
  case: _ {-1}_ _ / s (erefl c) => // ??? e [] ?;subst=> H.
  by apply: (H _ e).
Qed.

(* Sequence *)

Lemma hoare_seq R P Q c1 c2 : 
  hoare P c1 R -> hoare R c2 Q -> hoare P (c1 ++ c2) Q.
Proof.
  move=> H1 H2 ?? /ssem_cV [?[s1 s2]] Hp.
  by apply: (H2 _ _ s2 (H1 _ _ s1 Hp)).
Qed.

Lemma hoare_cons R P Q i c : 
  hoare P [::i] R ->  hoare R c Q ->  hoare P (i :: c) Q.
Proof. by apply:hoare_seq. Qed.

Lemma hoare_rcons R P Q i c : 
  hoare P c R -> hoare R [::i] Q -> hoare P (rcons c i) Q.
Proof. by rewrite -cats1;apply:hoare_seq. Qed.

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

(* Loop *)

Lemma hoare_for0 (i:rval sword) dir (e1 e2:pexpr sword) c Q:
  hoare (fun s => Q s /\ ssem_pexpr (sevm s) e2 < ssem_pexpr (sevm s) e1) 
        [::Cfor i (dir,e1,e2) c]
        Q.
Proof.
  move=> s1 s2;set c' := Cfor _ _ _ => /ssem_iV Hsem.
  case: _ {-1}_ _ / Hsem (erefl c') => // ?????? /=;first by move=> _ _ [].
  by move=> ? He _ [] ?????;subst=> -[];rewrite ltnNge He.
Qed.

Definition incr dir (i0:word) := 
  match dir with
  | UpTo   => (i0 + 1)
  | DownTo => (i0 - 1)
  end.

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
             [/\ I s', ssem_pexpr s'.(sevm) e1 = w1 & ssem_pexpr s'.(sevm) e2 = w2])) ->
  hoare (fun s => 
           let w1 := ssem_pexpr s.(sevm) e1 in
           let w2 := ssem_pexpr s.(sevm) e2 in
           let i0 := if dir is UpTo then w1 else w2 in
           let s' := {|semem := s.(semem); sevm := swrite_rval s.(sevm) i i0|} in
           w1 <= w2 /\ I s')
         [:: Cfor i (dir,e1,e2) c ]
         (fun s => 
            I s /\ 
            let w1 := ssem_pexpr s.(sevm) e1 in
            let w2 := ssem_pexpr s.(sevm) e2 in
            ssem_rval s.(sevm) i = if dir is UpTo then w2 else w1).
Proof.
  move=> He1 He2 Hc ??;set c' := Cfor _ _ _ => /ssem_iV Hsem.
  case: _ {-1}_ _ / Hsem (erefl c') => //.
  + by move=> /= ?????? Hlt [] ?????;subst;rewrite leqNgt Hlt => -[].
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
  + by rewrite /Pre;case : (dir) HI;rewrite leqnn Hw /= => -[] _ ?.
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
    by rewrite (word_sub1 Hlt);move: H1 H2 Hlt;rewrite -(rwP andP) -!(rwP leP) -minusE;omega.
  by move: HI;rewrite /w /incr;case: (dir).
Qed.

(* -------------------------------------------------------------------------- *)
(* ** Weakest Precondition                                                    *)
(* -------------------------------------------------------------------------- *)

Definition f2h (pm:pmap) (sm:smap) f : hpred := 
  fun se => ssem_sform {|pm := pm; sm := sm; vm := se.(sevm) |} f.


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



Definition init_st m t (rv:rval t) (v:sst2ty t) := 
  {| semem := m; sevm := swrite_rval svmap0 rv v |}.

Definition f2fpred pm sm P t (rv:rval t) := 
  fun m (v:sst2ty t)  => f2h pm sm P (init_st m rv v).
 
Record shoaref pm sm t tr Pf (f:fundef t tr) Qf := {
  sh_spec : hoaref (f2fpred pm sm Pf f.(fd_arg)) f (f2fpred pm sm Qf f.(fd_res));
  sh_Pf : Sv.subset (ffv Pf) (vrv f.(fd_arg));
  sh_Qf : Sv.subset (ffv Qf) (vrv f.(fd_res));
}.
  
Definition wp_call t tr (x:rval tr) (f:fundef t tr) (e:pexpr t)
   (Pf Qf Q:sform) := 
  let id := fresh_svar (Ssv.union (sffv Qf) (sffv Q)) in
  let v  := SVar tr id in
  let p1 := subst_sform (ewrite_rval mv0 f.(fd_arg) (p2sp e)) Pf in
  let q  := subst_sform (ewrite_rval mv0 x v) Q in
  let qf := subst_sform (ewrite_rval mv0 f.(fd_res) v) Qf in
  Fand p1 (Fforall v (Fimp qf q)).

Lemma swrite_dep t (rv:rval t) (v:sst2ty t) z s1 s2:
  Sv.In z (vrv rv) ->
  ((swrite_rval s1 rv v).[z])%vmap = ((swrite_rval s2 rv v).[z])%vmap.
Proof.
  elim: rv v s1 s2 => /= [x | ?? r1 Hr1 r2 Hr2] v s1 s2;rewrite ?vrv_var ?vrv_pair=> Hin.
  by have <- : x = z;[SvD.fsetdec | rewrite !Fv.setP_eq].
  case: (SvP.MP.In_dec z (vrv r1)) => Hz;first by apply Hr1.
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
                     (fun (v : svar) (m : positive) => Pos.max (svname v) m) s p))%positive.
  + move=> p x;apply SsvP.MP.fold_rec.
    + by move=> ? He H;elim (He _ H).
    move=> {p} z p s1 s2 _ Hnin Ha Hrec /Ha [-> | Hn];first by apply Pos.le_max_l. 
    by apply (Pos.le_trans _ p);auto using Pos.le_max_r.
  move=> /(Hf xH) /=;rewrite Pos.le_succ_l;apply Pos.lt_irrefl.
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
  ~Sv.In z (vrv rv) ->
  (ewrite_rval s rv v).[z]%mv = s.[z]%mv.
Proof.
  elim: rv v s => /= [x | ??? Hr1 ? Hr2] v s;rewrite ?vrv_var ?vrv_pair => Hin.
  + by rewrite Mv.setP_neq //;apply /eqP; SvD.fsetdec.
  rewrite Hr1 ?Hr2 //;SvD.fsetdec.
Qed.

Lemma fv_subst_var t (rv:rval t) e x s :
   Sv.In x (vrv rv) ->
   Sv.Subset (fv ((ewrite_rval s rv e).[x])%mv) (fv e).
Proof.
  elim: rv e s => /= [z | ?? r1 Hr1 r2 Hr2] e s;rewrite ?vrv_var ?vrv_pair => Hin.
  + have <- : z = x by SvD.fsetdec.
    by rewrite Mv.setP_eq. 
  case: (SvP.MP.In_dec x (vrv r1)) => Hx.
  + by move: (Hr1 (mk_fst e) (ewrite_rval s r2 (mk_snd e)) Hx) (@fv_mk_fst _ _ e);SvD.fsetdec.
  have Hin2 : Sv.In x (vrv r2) by SvD.fsetdec.
  by rewrite ewrite_nin //; move: (Hr2 (mk_snd e) s Hin2) (@fv_mk_snd _ _ e);SvD.fsetdec.    
Qed.

Lemma SubsetUs (s1 s2 s:Sv.t) : 
  Sv.Subset (Sv.union s1 s2) s -> Sv.Subset s1 s /\ Sv.Subset s2 s.
Proof. split;SvD.fsetdec. Qed.
                
Lemma fv_subst_spexpr t' (e':spexpr t') t (rv:rval t) e :
  Sv.Subset (fv e') (vrv rv) ->
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
  Sv.Subset (ffv f) (vrv rv) ->
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
  Sv.In x (vrv rv) ->
  (swrite_rval s' rv (ssem_rval s rv)).[x]%vmap = s.[x]%vmap.
Proof.
  elim: rv s' => [w | ?? r1 Hr1 r2 Hr2] s' /=;rewrite ?vrv_var ?vrv_pair=> Hin.
  have <- : w = x by SvD.fsetdec.
  + by rewrite Fv.setP_eq.
  case: (SvP.MP.In_dec x (vrv r1)) => Hx;first by apply Hr1.
  by rewrite swrite_nin // Hr2 //;SvD.fsetdec.
Qed.

Lemma shoare_fun pm sm t tr (f:fundef t tr)  Pf Qf :
  Sv.subset (ffv Pf) (vrv f.(fd_arg)) ->
  Sv.subset (ffv Qf) (vrv f.(fd_res)) ->
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

(* Conseq *)

Definition donotdepf (s : Sv.t) (f:hpred) := 
  forall s1 s2, s1.(sevm) = s2.(sevm) [\ s ] -> 
     f s1 <-> f s2.

Lemma hoare_notmod (P P' Q:hpred) c:
  donotdepf (write_c c) P' ->
  hoare (fun s => P s /\ P' s) c Q ->
  hoare (fun s => P s /\ P' s) c (fun s => Q s /\ P' s).
Proof.
  move=> Hd Hc s s' Hsem [HP HP'];split;first by apply (Hc _ _ Hsem).
  by rewrite -(@Hd s s') //;apply writeP.
Qed.

(* Loop *)

Definition f_lt e1 e2 := Fbool (mk_lt e1 e2).

Definition f_le e1 e2 := Fbool (mk_le e1 e2).

Lemma shoare_for0 pm sm i dir e1 e2 c c1 P Q:
   hoare P c1 (f2h pm sm (mk_fand Q (f_lt (p2sp e2) (p2sp e1)))) ->
   hoare P (rcons c1 (Cfor i (dir,e1,e2) c)) (f2h pm sm Q).
Proof.
  move=> Hc1;apply hoare_for0.  
  by apply: hoare_conseq Hc1 => //= s;rewrite /f2h /f_lt mk_fandP /= mk_ltP /= !sem_p2sp.
Qed.

Fixpoint gen_mod_rec (m:list var) sfv (s:vsubst) (f:sform) := 
  match m with
  | [::] => subst_sform s f
  | x::m =>
    let xid := fresh_svar sfv in 
    let sx  := SVar x.(vtype) xid in
    Fforall sx (gen_mod_rec m (Ssv.add sx sfv) s.[x <- sx]%mv f)
  end.

Definition gen_mod m s f := gen_mod_rec (Sv.elements m) (sffv f) s f.

Instance fresh_svar_m : Proper (Ssv.Equal ==> eq) fresh_svar.
Proof.
  move=> f1 f2 Heq;rewrite /fresh_svar;f_equal.
  apply SsvP.MP.fold_equal; auto; first by move=> ??-> ??->.
  by move=> x y z;rewrite !Pos.max_assoc (Pos.max_comm (svname _)).
Qed.


Definition eeq t (e1 e2:spexpr t) := forall rho, e1 =[rho] e2.

Instance eeq_R t: Equivalence (@eeq t).
Proof. 
  constructor => //.
  + by move=> f1 f2 Heq s;rewrite Heq.
  by move=> f1 f2 f3 Heq1 Heq2 s;rewrite Heq1.
Qed.

Definition feq f1 f2 := forall rho, f1=_[rho]f2.

Instance feq_R : Equivalence feq.
Proof. 
  constructor => //.
  + by move=> f1 f2 Heq s;rewrite Heq.
  by move=> f1 f2 f3 Heq1 Heq2 s;rewrite Heq1.
Qed.




   ssem_sform subst_sform vm f 






Instance gen_mod_rec_m: Proper (eq ==> Ssv.Equal ==> eq ==> feq ==> feq) gen_mod_rec.
Proof.
  move=> ? m-> fv1 fv2 H ? s -> f1 f2 Heq.
  elim:m fv1 fv2 H s=> //= [|x m Hrec] fv1 fv2 H s.
ssem_sform rho (subst_sform mv f) = 
subst_sform {pm; sm; vm := fun x => ssem_spexpr rho (subst_spexpr mv.[x]) f.
 
  Search subst_sform.
  have ->: fresh_svar fv1 = fresh_svar fv2 by rewrite H.
  by f_equal;apply Hrec;SsvD.fsetdec.
Qed.

Instance gen_mod_rec_m: Proper (eq ==> Ssv.Equal ==> eq ==> eq ==> eq) gen_mod_rec.
Proof.
  move=> ? m-> fv1 fv2 H ? s -> ? f ->.
  elim:m fv1 fv2 H s=> //= x m Hrec fv1 fv2 H s.
  have ->: fresh_svar fv1 = fresh_svar fv2 by rewrite H.
  by f_equal;apply Hrec;SsvD.fsetdec.
Qed.

Lemma gen_mod_subst m s f rho:
  Ssv.Equal (sffv f) (sffv (subst_sform s f)) ->
  (forall x, Mv.indom x s -> Sv.Empty (Sv.inter (fv s.[x]%mv) m)) ->
  (Mv.dft s = fun x => Evar x) ->
  gen_mod m s f =_[rho] gen_mod m mv0 (subst_sform s f).
Proof.
  move=> Hsfv Hdis Hdft;rewrite /gen_mod;rewrite -Hsfv.
  have : forall x, Mv.indom x s ->
    forall z, ~(SetoidList.InA eq z (Sv.elements m) /\
                Sv.In z (fv (s.[x]%mv))).
  + by move=> x /Hdis ? z;rewrite -SvP.MP.Dec.F.elements_iff; SvD.fsetdec.
  elim: {m} (Sv.elements m) rho s f (sffv f) Hdft {Hsfv Hdis} =>
     /= [|x m Hrec] rho s f fvf Hdft Hdom.
  + symmetry;apply ssem_subst_sform => //=.
  apply forall_iff => v.
  rewrite Hrec ?(Hrec _ (mv0.[x <- _]%mv)) //.

apply Hrec.
;rewrite Hrec.

Search _ osubst.
                               
x \in (Sv.elements
  rewrite /gen_mod /gen_mod_rec.
  set body := (fun x rec s0 sfv => Fforall _ _).
  move: s Hsfv Hdis Hdft; apply SvP.MP.fold_rec=> /=.
  move=> ??? Heq Hdis Hdft;rewrite SvP.MP.fold_1b.
Search Sv.fold SvP.MP.Add.

Search Sv.fold Sv.Empty. 

SvP.MP.fold_1b.

    (fun x rec =>
       forall 

  rewrite /gen_mod_rec.
 elim /SvP.MP.fold_rec: m s.
Sv.fold_rec 

  
  
  


Definition pre_for dir (i:rval sword) (e1 e2:spexpr sword) c I Q := 
  let fvi := vrv i in
  let fv1 := fv e1 in
  let fv2 := fv e2 in
  let modc := write_c c in
  if Sv.is_empty (Sv.inter (Sv.union fv1 fv2) (Sv.union fvi modc)) && 
     Sv.is_empty (Sv.inter fvi modc) then
    let estart := if dir is UpTo then e1 else e2 in
    let eend   := if dir is UpTo then e2 else e1 in
    Some (mk_fand 
            (f_le e1 e2) 
            (mk_fand 
               (subst_sform (ewrite_rval mv0 i estart) I)
               (gen_mod_rec modc (ewrite_rval mv0 i eend) (Fimp I Q))))
  else None.

Definition post_for_body (I:sform) dir (e1 e2 i0:spexpr sword) (i:rval sword) :=
  let vi := 
    mk_if (mk_eq i0 (if dir is UpTo then e2 else e1))
          i0
          (if dir is UpTo then mk_add i0 1%num else mk_sub i0 1%num) in
  let s := ewrite_rval mv0 i vi in
  subst_sform s I.

Definition wp_for dir i e1 e2 c I Q := 
  let e1 := p2sp e1 in
  let e2 := p2sp e2 in
  match pre_for dir i e1 e2 c I Q with
  | Some pre => 
    let id0 := fresh_svar (sffv I) in
    let i0  := SVar sword id0 in
    Some ((id0, post_for_body I dir e1 e2 i0 i), pre)
  | None => None
  end.

Lemma ssem_rval2pe t (i:rval t) s:
   ssem_spexpr s (p2sp (rval2pe i)) = ssem_rval (vm s) i.
Proof. by elim:i => //= ??? -> ? ->. Qed.

Definition pmap0 : pmap := @Msv.empty sst2pred (fun _ _ => True).

Lemma donotdep_fv s t (e:pexpr t): Sv.Empty (Sv.inter s (fv (p2sp e))) -> donotdep s e.
Proof.
  move=> He s1 s2 Hs;set rho := fun s => {|pm := pmap0; sm := msv0; vm := s |}.
  rewrite -!(sem_p2sp _ (rho _));apply ssem_spexpr_fv.
  constructor=>// x Hin;apply Hs;SvD.fsetdec.
Qed.

Lemma hoare_for pm (sm:smap) (i : rval sword) dir (e1 e2 : pexpr sword) c P I Q c1 id0 I' Q':
  wp_for dir i e1 e2 c I Q = Some ((id0,I'),Q') ->
  (forall (v0:word), 
     let i0  := SVar sword id0 in
     let sm0 := sm.[i0 <- v0]%msv in
      hoare (f2h pm sm0 (mk_fand I (Fbool (mk_eq (p2sp (rval2pe i)) i0))))
            c (f2h pm sm0 I')) ->
  hoare P c1 (f2h pm sm Q') -> 
  hoare P (rcons c1 (Cfor i (dir,e1,e2) c)) (f2h pm sm Q).
Proof.
  rewrite /wp_for /pre_for;case: ifP=> //=.
  move=> /andP [] /SvD.F.is_empty_2 He /SvD.F.is_empty_2 Hi [] <- <- <- Hc Hc1.
  rewrite -cats1;apply (hoare_seq Hc1).
  match type of Hc1 with
  | hoare _ _ (f2h _ _ (mk_fand ?X1 (mk_fand ?X2 ?X3))) => 
    set lee := X1; set I0 := X2; set IQ := X3 end.
  set Eqi := Fbool (mk_eq (p2sp (rval2pe i)) (if dir is UpTo then p2sp e2 else p2sp e1)).
  apply (@hoare_conseq (f2h pm sm (Fand (Fand lee I0) IQ))
          (f2h pm sm (Fand (Fand I Eqi) IQ))).
  + by move=> s;rewrite /f2h /= mk_fandP /= mk_fandP /=;tauto.
  + move=> s;rewrite /f2h /=.
(* f2h pm sm (gen_mod modc mv f) s -> 
   f2h pm sm (subst_sform mv f) s *)
    admit.
  apply: hoare_notmod.
  + move=> s1 s2 Hs; apply ssem_sform_fv=> //=.
    constructor=> // x Hx;apply Hs;rewrite write_c_cons.
Lemma gen_mod mv : 
   ffv (gen_mod s) mv f = Sv.diff
   (forall x, Mv.indom mv x -> Sv.Empty (fv mv.[x]

 write_i_for.
    

rewrite /donotdepf.

  apply: (hoare_conseq _ _ (@hoare_for_base i dir e1 e2 (f2h pm sm I) c _ _ _)).
  + move=> s /=;rewrite mk_leP /I0 /= !sem_p2sp /= => -[] [] ? HI0 _;split=>//.
    move:HI0;apply iffRL;symmetry;apply ssem_subst_sform => //=.
    + by apply dft_ewrite_rval.
    + move=> z Hz. 
      set e := (e in ewrite_rval _ _ e);set v := (v in swrite_rval _ _ v).
      set rho := (rho in ssem_spexpr rho _).
      have <-: ssem_spexpr rho e = v.
      + by rewrite /e /v;case dir;rewrite sem_p2sp.
      by apply ewrite_rvalP.
    move=> z Hz;apply empty_ewrite_rval => //.
    by have := @sfv_p2sp _ e1; have := @sfv_p2sp _ e2;case dir; SsvD.fsetdec.  
  + move=> s [] ? /= Hsi;split=>//;rewrite mk_eqP /= ssem_rval2pe /= Hsi.
    by case dir;rewrite sem_p2sp.
  + by apply donotdep_fv;SvD.fsetdec.
  + by apply donotdep_fv;SvD.fsetdec.

case dir.
   
   
    Search _ ssem_rval rval2pe.

Search _ rval2pe.
   
Search _ sfv p2sp.
    Search _ Mv.indom ewrite_rval. 

Search _ ewrite_rval swrite_rval.

Search _ Mv.dft ewrite_rval.

    admit. (* ssem_subst_sform *)


   forall (st2 st1 : sstate) (f : sform) (s : Mv.rt_ spexpr),
   Mv.dft s = [eta Evar] ->
   pm st1 = pm st2 ->
   sm st1 = sm st2 ->
   (forall x : var, Sv.In x (ffv f) -> subst_spexpr s x =[ st1, st2] x) ->
   (forall x : var,
    Mv.indom x s -> Ssv.Empty (Ssv.inter (sfv (s.[x])%mv) (sffv f))) ->
   subst_sform s f =_[ st1, st2] f

Search _ subst_sform.
Search p2sp.
  
        (ewrite_rval mv0 i e)
             match dir with
             | UpTo => p2sp e2
             | DownTo => p2sp e1
             end)

 match dir with
                         | UpTo => p2sp e2
                         | DownTo => p2sp e1
                         end) 

          (let w1 := ssem_pexpr (sevm s) e1 in
           let w2 := ssem_pexpr (sevm s) e2 in
           w1 <= w2 ->
           ssem_rval (sevm s) i =
           match dir0 with
           | UpTo => w2
           | DownTo => w1
           end))
        
  set lee := (f_le (p2sp e1) (p2sp e2)

    

Search _ Sv.is_empty.
  let se1 := p2sp e1 in
   wp_loop dir i e1 e2  

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

Definition sx := (SVar sword 2%positive).

Compute (gen_mod (Sv.add x (Sv.singleton y)) mv0 
           (Fand (f_le x sx) (f_le y z))).



Definition w0 : N := 0.
Definition w1 : N := 1.

Definition c := 
  [:: assgn x w0;
      assgn y w1;
      Cif (Papp2 Oeq x w1) [::assgn z x] [::assgn z y] ].




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
