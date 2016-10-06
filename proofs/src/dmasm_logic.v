(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import seq tuple finfun.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import JMeq ZArith Setoid Morphisms.

Require Import word dmasm_utils dmasm_type dmasm_var dmasm_expr.
Require Import dmasm_sem dmasm_Ssem dmasm_Ssem_props.
Require Import symbolic_expr symbolic_expr_opt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SEM.
Variable valid_addr : word -> bool.
(* -------------------------------------------------------------------------- *)
(* ** Hoare Logic                                                             *)
(* -------------------------------------------------------------------------- *)

Definition hpred := sestate -> Prop.

Definition hoare (Pre:hpred) (c:cmd) (Post:hpred) := 
  forall (s s':sestate), ssem valid_addr s c s' -> Pre s -> Post s'.

Definition fpred (t:stype) := mem -> sst2ty t -> Prop.

Definition hoaref ta tr (Pre:fpred ta) (f:fundef ta tr) (Post:fpred tr) := 
  forall (m m':mem) va vr, ssem_fun valid_addr f m va m' vr -> Pre m va -> Post m' vr.

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

(* Conseq not modify *)

Definition donotdepf (s : Sv.t) (f:hpred) := 
  forall s1 s2, s1.(sevm) = s2.(sevm) [\ s ] -> 
     f s1 <-> f s2.

Lemma hoare_notmod (P P' Q:hpred) c:
  donotdepf (write_c c) P' ->
  hoare (fun s => P s /\ P' s) c Q ->
  hoare (fun s => P s /\ P' s) c (fun s => Q s /\ P' s).
Proof.
  move=> Hd Hc s s' Hsem [HP HP'];split;first by apply (Hc _ _ Hsem).
  by rewrite -(@Hd s s') //;apply (@writeP valid_addr).
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
  hoare (fun s1 => forall s2, ssem_bcmd valid_addr s1 bc = ok s2 -> P s2) [::Cbcmd bc] P.
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

(* -------------------------------------------------------------------- *)
Lemma hoare_for0 (i:rval sword) dir (e1 e2:pexpr sword) c Q:
  hoare (fun s => Q s /\ (ssem_pexpr (sevm s) e2 < ssem_pexpr (sevm s) e1)%Z) 
        [::Cfor i (dir,e1,e2) c]
        Q.
Proof.
move=> s1 s2; set c' := Cfor _ _ _ => /ssem_iV sem.
inversion_clear sem; inversion H => -[] // _ /Z.ltb_lt h.
by move: H0; rewrite /wrange Z.leb_antisym h.
Qed.

(* -------------------------------------------------------------------- *)
Lemma hoare_for_base_x (i : rval sword) (ws : seq.seq word) I c :
  (forall j : word, hoare
     (fun s => [/\ I s, ssem_rval s.(sevm) i = j & j \in ws])
     c
     (fun s => [/\ I s & ssem_rval s.(sevm) i = j]))

  -> (forall s1 s2, s1.(sevm) = s2.(sevm) [\vrv i] -> I s1 -> I s2)
  -> forall s1 s2, ssem_for valid_addr i ws s1 c s2 -> I s1 ->
      [/\ I s2 & ssem_rval s2.(sevm) i = last (ssem_rval s1.(sevm) i) ws].
Proof.
move=> hc Iindep s1 s2 h; elim: h hc Iindep => //=.
move=> {s1 s2 i ws c} i w ws c s1 s2 s3 sc hfor ih hc Idp Is1.
move: sc; set s1' := (X in ssem X) => sc.
case: (hc w _ _ sc); first (split; first last).
+ by rewrite inE eqxx. + by rewrite ssem_swrite_rval.
+ by apply: Idp Is1 => x Sx; rewrite swrite_nin.
case/ih => // => [j s'1 s'2 /hc {hc}hc [? ? j_ws]|].
+ by apply/hc; split=> //; rewrite inE j_ws orbT.
by move=> Is3 eqi <-; split.
Qed.

(* -------------------------------------------------------------------- *)
(* Definition incr dir (i : word) := 
  if dir is UpTo then i+1 else i-1.

Lemma hoare_for_base (i:rval sword) dir (e1 e2:pexpr sword) I cmd:
  donotdep (vrv i) e1 ->
  donotdep (vrv i) e2 ->

  (forall (w1 w2 j : word),
    hoare
      (fun s => [/\ I s, ssem_rval s.(sevm) i = j, w1 <= j <= w2
              , ssem_pexpr s.(sevm) e1 = w1
              & ssem_pexpr s.(sevm) e2 = w2])

      cmd

      (fun s => 
         let w  := if dir is UpTo then w2 else w1 in
         let i1 := if j == w then j else incr dir j in
         let s' := {|semem := s.(semem); sevm := swrite_rval s.(sevm) i i1|} in
         [/\ I s', ssem_rval s.(sevm) i = j
          , ssem_pexpr s'.(sevm) e1 = w1
          & ssem_pexpr s'.(sevm) e2 = w2]))

  ->

  hoare
    (fun s => 
       let w1 := ssem_pexpr s.(sevm) e1 in
       let w2 := ssem_pexpr s.(sevm) e2 in
       let i0 := if dir is UpTo then w1 else w2 in
       let s' := {|semem := s.(semem); sevm := swrite_rval s.(sevm) i i0|} in
       I s' /\ w1 <= w2)

    [:: Cfor i (dir, e1, e2) cmd ]

    (fun s => 
       let w1 := ssem_pexpr s.(sevm) e1 in
       let w2 := ssem_pexpr s.(sevm) e2 in
       I s /\ ssem_rval s.(sevm) i = if dir is UpTo then w2 else w1).
Proof. Admitted.
*)

(*
(* -------------------------------------------------------------------------- *)
(* ** Weakest Precondition                                                    *)
(* -------------------------------------------------------------------------- *)

(* TODO move this *)

(* end move this *)

Definition f2h (pm:pmap) (sm:smap) f : hpred := 
  fun se => ssem_sform {|pm := pm; sm := sm; vm := se.(sevm) |} f.

Definition wp_assign {t1} (rv:rval t1) (e:pexpr t1) (s:pvsubst) := 
  osubst (ewrite rv (p2sp e) Ssv.empty) s.
  
Instance wf_wp_assign (s:pvsubst) {Hs:wf_vsubst s} t (rv:rval t) e: wf_vsubst (wp_assign rv e s).
Proof.
  by rewrite /wp_assign;apply wf_osubst=> //;apply /wf_ewrite;rewrite sfv_p2sp.
Qed.

Lemma hoare_asgn pm sm {t1} (rv:rval t1) (e:pexpr t1) f (s:pvsubst) {Hs:wf_vsubst s}:
  hoare (f2h pm sm (fsubst (wp_assign rv e s) f))
        [:: assgn rv e] 
        (f2h pm sm (fsubst s f)).
Proof.
  rewrite /assgn; move=> s1_ s2_;set c := Cbcmd _=> /ssem_iV Hi.
  case: _ {-1}_ _ / Hi (erefl c) => // s1 s2 ? H [] ?; subst=> {c s1_ s2_}.
  case: H=> <- {s2};rewrite /f2h /=.
  apply iffLR; set rho := {| pm := pm; sm := sm; vm := sevm s1 |}.
  have wf_e := wf_ewrite rv (SsvP.MP.subset_equal (@sfv_p2sp _ e)).
  rewrite !fsubstP /wp_assign;apply feq_on_fv => //.
  have H1 := @eq_on_osubst _ _ wf_e Hs rho (ffv f) (sffv f).
  apply (eq_on_trans H1);constructor=> //.
  rewrite /ewrite /ssubst /rho/= => ??.
  rewrite !Fv.get0. apply eq_on_fv;constructor=> //= ??;rewrite Fv.get0.
  by rewrite (@ewrite_rvalP rho (vm rho)) //= sem_p2sp.
Qed.

Definition wp_bcmd bc s := 
  match bc with
  | Assgn st rv e => ([::], (wp_assign rv e s))
  | Load  _ _     => ([::Cbcmd bc], s)
  | Store _ _     => ([::Cbcmd bc], s)
  end.

Definition wp_rec := 
  Eval lazy beta delta [cmd_rect instr_rect' list_rect] in
  @cmd_rect (fun _ => pvsubst -> cmd * pvsubst)
            (fun _ => pvsubst -> cmd * pvsubst)
            (fun _ _ _ => pvsubst -> unit)
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
    (fun fi i rn c _ Q => ([::Cfor fi i rn c], Q))
    (fun _ _ x f a _ Q => ([::Ccall x f a], Q))
    (fun _ _ _ _ _ _ _ => tt).

Lemma r_wp_cons i c (p:pvsubst) :
  wp_rec (i :: c) p = 
   if nilp (wp_rec c p).1 then wp_rec [::i] (wp_rec c p).2
   else (i::(wp_rec c p).1 , (wp_rec c p).2).
Proof. by move=> /=;case (wp_rec c p) => c_ R /=;case:nilP. Qed.

Lemma r_wp_if e c1 c2 (p:pvsubst) : 
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

Lemma wp_rec_tl pm sm c (f:sform) (s:pvsubst) {Hs:wf_vsubst s}: exists tl, 
   [/\ c = (wp_rec c s).1 ++ tl, wf_vsubst (wp_rec c s).2 &
   hoare (f2h pm sm (fsubst (wp_rec c s).2 f)) tl (f2h pm sm (fsubst s f))].
Proof.
  elim /cmd_Ind : c s Hs => [ | i c Hi Hc| bc| e c1 c2 Hc1 Hc2| i rn c Hc|?? x g a _ | //] s Hs.
  + by exists ([::]);split=>//=;apply hoare_skip.
  + rewrite r_wp_cons;elim (Hc s Hs)=> {Hc} tlc [Heqc Hwf Hwpc].
    case: nilP Heqc => Heq Heqc.
    + elim (Hi (wp_rec c s).2 Hwf)=> tl [Htl Hwf' Hwp] ;exists (tl ++ c).
      rewrite catA -Htl;split=>//.
      by rewrite {2} Heqc Heq cat0s;apply:hoare_seq Hwp Hwpc.
    by exists tlc=> /=;rewrite -Heqc.
  + case: bc => [? r e | ?? | ??] /=; try by exists [::];split=>//;apply:hoare_skip.
    exists  [:: Cbcmd (Assgn r e)];split=>//.
    + by apply wf_wp_assign.
    by apply hoare_asgn.
  + rewrite r_wp_if;case: andP=> /=;last
      by exists [::];split=>//;apply:hoare_skip.
    move=> [/nilP Heq1 /nilP Heq2].
    elim (Hc1 s Hs) => {Hc1} tl1;elim (Hc2 s Hs) => {Hc2} tl2.
    rewrite Heq1 Heq2 !cat0s=> -[<- wf2 Hc2] [<- wf1 Hc1].
    exists [:: Cif e c1 c2];split=>//.
    + by apply wf_merge_if.
    apply: hoare_if.
    + apply: (hoare_conseq _ _ Hc1)=> // se [] He.
      by apply iffRL;rewrite /f2h (@merge_ifP (p2sp e) _ _ f wf1 wf2 _) /= sem_p2sp He. 
    apply: (hoare_conseq _ _ Hc2)=> // se [] /negPf He.
    by apply iffRL;rewrite /f2h  (@merge_ifP (p2sp e) _ _ f wf1 wf2 _) /= sem_p2sp He.
  + by exists [::];split=>//;apply:hoare_skip.
  by exists [::];split=>//;apply:hoare_skip.
Qed.
  
Definition init_vsubst f := 
  let fv := ffv f in
  {| v_fv := Ssv.empty; v_v := Sv.fold (fun x s => s.[x <- Evar x]%mv) fv vs0 |}.

Lemma init_vsubstP f x : 
  (init_vsubst f).(v_v).[x]%mv = Evar x.
Proof.
  rewrite /init_vsubst; apply SvP.MP.fold_rec => // z s s1 s2 _ ? ?.
  by case (z =P x) => [-> | /eqP ?] ?;rewrite ?Mv.setP_eq ?Mv.setP_neq.
Qed.

Instance wf_init_vsubst f : wf_vsubst (init_vsubst f).
Proof.
  constructor.
  + by rewrite /= SvP.MP.fold_spec_right;elim: List.rev.
  by move=> ??;rewrite init_vsubstP sfv_var.   
Qed.

Definition wp c f := 
  let s  := init_vsubst f in
  let (c', s') := wp_rec c s in
  let s' := {| v_fv := s'.(v_fv); v_v := Mv.map (fun _ e => eopt e) s'.(v_v) |} in
  (c', sfsubst s' f).

Lemma hoare_wp pm sm P c Q : 
   hoare P (wp c Q).1 (f2h pm sm (wp c Q).2) -> 
   hoare P c (f2h pm sm Q).
Proof.
  rewrite /wp.
  move=> H1.
  elim: (@wp_rec_tl pm sm c Q _ (wf_init_vsubst Q))=> tl [{3}->] Hwf H2.
  apply (@hoare_conseq P (f2h pm sm (fsubst (init_vsubst Q) Q))) => //.
  + move=> rho;apply iffRL;symmetry.
    rewrite /f2h /= fsubstP;apply feq_on_fv=> //;constructor=> //= ??.
    by rewrite Fv.get0 init_vsubstP.
  apply: hoare_seq H2; move: H1;case: wp_rec Hwf => [c' s'] Hwf.
  apply: hoare_conseq=> // s;rewrite /f2h /snd.
  apply iffRL;set rho := (rho in (_ =_[rho] _)).
  rewrite (sfsubstP Q _ rho) !fsubstP;apply feq_on_fv => //=;constructor=> //= ??.
  by rewrite !Fv.get0 Mv.mapP (eoptP _ rho).
Qed.

(* Call *)

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
  let p1 := fsubst (ewrite f.(fd_arg) (p2sp e) Ssv.empty) Pf in
  let q  := fsubst (ewrite x v (Ssv.singleton v)) Q in
  let qf := fsubst (ewrite f.(fd_res) v (Ssv.singleton v)) Qf in
  f_and p1 (f_forall v (f_imp qf q)).

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

Lemma wp_callP Pf Qf pm sm t tr c x (f:fundef t tr) e P Q :
  shoaref pm sm Pf f Qf ->
  hoare P c (f2h pm sm (wp_call x f e Pf Qf Q)) ->
  hoare P (rcons c (Ccall x f e)) (f2h pm sm Q).
Proof.
  move=> Hf Hc; apply (hoare_rcons Hc).
  eapply (@hoare_conseq _ (f2h pm sm Q));[ | done | eapply (hoare_call (sh_spec Hf))].
  move=> s /= [H1 H2]; pose rho := {| pm := pm; sm := sm; vm := sevm s |};split.
  + apply: iffRL H1;rewrite /f2fpred /init_st /f2h /=. 
    have wf_e := wf_ewrite (fd_arg f) (SsvP.MP.subset_equal (@sfv_p2sp _ e)).
    rewrite fsubstP;apply feq_on_fv=> //;constructor=> //= ??.
    rewrite Fv.get0 (@ewrite_rvalP rho (vm rho)) // sem_p2sp /=.
    apply swrite_dep;have /Sv.subset_spec := sh_Pf Hf;SvD.fsetdec. 
  move=> m' v. have /= {H2} := H2 v.
  set x' := SVar _ _. 
  set rho' := {| pm := pm; sm := (sm.[x' <- v])%msv; vm := sevm s |}.
  match goal with |- (_ -> ?P1) -> _ => move=> H2 HQf; have : P1 end.
  + apply H2;apply: iffRL HQf;rewrite /f2fpred /init_st /f2h /=.
    have wf_e := wf_ewrite (fd_res f) (SsvP.MP.subset_equal (sfv_svar x')).
    rewrite fsubstP;apply feq_on_fv=> //;constructor=> //= z ?.
    + rewrite Fv.get0 (@ewrite_rvalP rho' (vm rho')) //= Msv.setP_eq. 
      by apply swrite_dep;have /Sv.subset_spec := sh_Qf Hf;SvD.fsetdec. 
    rewrite Msv.get0 Msv.setP_neq //. 
    apply /eqP=> Heq. apply (@fresh_svarP tr (Ssv.union (sffv Qf) (sffv Q))). 
    by have /Sv.subset_spec := sh_Qf Hf;SsvD.fsetdec. 
  apply: iffRL; rewrite /f2fpred /init_st /f2h /=.
  have wf_e := wf_ewrite x (SsvP.MP.subset_equal (sfv_svar x')).
  rewrite fsubstP;apply feq_on_fv=> //;constructor=> //= z ?.
  + by rewrite Fv.get0 (@ewrite_rvalP rho' (vm rho')) //= Msv.setP_eq. 
  rewrite Msv.get0 Msv.setP_neq //. 
  by apply /eqP=> Heq;apply (@fresh_svarP tr (Ssv.union (sffv Qf) (sffv Q)));SsvD.fsetdec. 
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
  rewrite (@feq_on_fv Qf _ st2)=> //.
  + apply: (Hbody _ _ H7);move: Hpre;rewrite /f2h /es /=.
    apply iffRL; apply feq_on_fv=> //;constructor=> //= x Hin.
    by apply swrite_dep;SvD.fsetdec.
  constructor=> //= x Hin. 
  by apply swrite_rval_ssem;SvD.fsetdec.
Qed.

(* Loop *)

Lemma shoare_for0 pm sm fi i dir e1 e2 c c1 P Q:
   hoare P c1 (f2h pm sm (sf_and Q (f_lt (p2sp e2) (p2sp e1)))) ->
   hoare P (rcons c1 (Cfor fi i (dir,e1,e2) c)) (f2h pm sm Q).
Proof.
  move=> Hc1;apply (hoare_rcons Hc1).
  eapply hoare_conseq with (Q1 := f2h pm sm Q);[ | |apply hoare_for0 ]=> //.
  by move=> s;rewrite /f2h (sf_andP _ _ _) /= (sltP _ _ _) /= !sem_p2sp .
Qed.

Definition add_fresh (x:var) (s:pvsubst) :=   
  let xid := fresh_svar s.(v_fv) in 
  let sx  := SVar x.(vtype) xid in
  (sx, {| v_fv := Ssv.add sx s.(v_fv); v_v := s.(v_v).[x <- sx]%mv |}).

Fixpoint gen_mod_rec (m:list var) (s:pvsubst) (f:sform) := 
  match m with
  | [::] => fsubst s f
  | x::m =>
    let (sx,s) := add_fresh x s in
    f_forall sx (gen_mod_rec m s f)
  end.

Definition gen_mod m s f := 
  gen_mod_rec (Sv.elements m) {|v_fv := Ssv.union s.(v_fv) (sffv f); v_v := s.(v_v)|} f.

Definition pre_for dir (i:rval sword) (e1 e2:spexpr sword) c I Q := 
  let fvi := vrv i in
  let fv1 := fv e1 in
  let fv2 := fv e2 in
  let modc := write_c c in
  if Sv.is_empty (Sv.inter (Sv.union fv1 fv2) (Sv.union fvi modc)) && 
     Sv.is_empty (Sv.inter fvi modc) then
    let estart := if dir is UpTo then e1 else e2 in
    let eend   := if dir is UpTo then e2 else e1 in
    Some (f_and 
            (f_le e1 e2) 
            (f_and 
               (fsubst (ewrite i estart Ssv.empty) I)
               (gen_mod modc (ewrite i eend Ssv.empty) (f_imp I Q))))
  else None.

Definition post_for_body (I:sform) dir (e1 e2:spexpr sword) id0 (i:rval sword) :=
  let i0  := SVar sword id0 in
  let vi := 
    sif (seq i0 (if dir is UpTo then e2 else e1))
          i0
          (if dir is UpTo then sadd i0 1%num else ssub i0 1%num) in
  let s := ewrite i vi (Ssv.singleton i0) in
  fsubst s I.

Definition wp_for dir i e1 e2 c I Q := 
  let e1 := p2sp e1 in
  let e2 := p2sp e2 in
  match pre_for dir i e1 e2 c I Q with
  | Some pre => 
    let id0 := fresh_svar (sffv I) in
    let i0  := SVar sword id0 in
    Some ((id0, post_for_body I dir e1 e2 id0 i), pre)
  | None => None
  end.

(*Definition Fwrap A B (f:A->B) (a:idfun A) := Wrap (f a). *)

Ltac as_subgoal :=
  let T := fresh "T" in 
  let e := fresh "e" in 
 unshelve (evar (T : Type); evar (e : T); move=> /(_ e));
  [unfold T;clear T | clear T e].

Instance wf_add_fresh x s {H:wf_vsubst s} : wf_vsubst (add_fresh x s).2.
Proof.
  rewrite /add_fresh;constructor => //= z.
  + by apply vdft_v.
  rewrite Mv.indom_setP;case:eqP => [<- _ |/eqP ?] /=;rewrite ?Mv.setP_eq ?Mv.setP_neq //.
  + by rewrite [sfv _]sfv_svar;SsvD.fsetdec.
  by move=> /vindom_v;SsvD.fsetdec.
Qed.

Lemma gen_mod_rec_imp pm sm s Q st modi:
  wf_vsubst s -> Ssv.Subset (sffv Q) (v_fv s) -> 
  (SetoidList.NoDupA eq modi) ->
  (forall x, SetoidList.InA eq x modi -> ~~Mv.indom x (v_v s)) ->
  f2h pm sm (gen_mod_rec modi s Q) st -> f2h pm sm (fsubst s Q) st.
Proof.
  elim: modi sm s => [|x modi Hrec] sm s Hwf Hsub Hdup Hmodi//=.
  have wf_a := @wf_add_fresh x _ Hwf.
  inversion Hdup;subst.
  rewrite /f2h /= => /(_ (sevm st).[x]%vmap) /Hrec. 
  as_subgoal;[ | as_subgoal;[ | as_subgoal] ]=> //.
  + by move=> ? /=;SsvD.fsetdec.
  + move=> z Hz /=;rewrite Mv.indom_setP negb_or Hmodi ?andbT.
    + by apply /eqP=> ?;subst. 
    by apply SetoidList.InA_cons_tl.
  rewrite /f2h /=;apply iffRL.
  rewrite !fsubstP;apply feq_on_fv => //=;constructor=> z Hz /=.
  + rewrite !Fv.get0.
    case: (x =P z)=> [<- | /eqP ?].
    + rewrite Mv.setP_eq /= Msv.setP_eq. 
      rewrite Mv.indom_getP ?vdft_v //.
      by apply Hmodi;apply SetoidList.InA_cons_hd.
    rewrite Mv.setP_neq //;apply eq_on_fv;constructor=> y Hy //=.   
    rewrite Msv.setP_neq //;apply /eqP=> ?;subst.
    apply (@fresh_svarP (vtype x) (v_fv s)).
    case Heq: (Mv.indom z (v_v s)) (@vindom_v _ Hwf z).
    + by move =>/(_ (erefl true));SsvD.fsetdec.
    by move=> _;move:Hy;rewrite Mv.indom_getP ?Heq // vdft_v sfv_var;SsvD.fsetdec.
  rewrite !Msv.get0 Msv.setP_neq //;apply /eqP => ?;subst.
  by apply (@fresh_svarP (vtype x) (v_fv s));SsvD.fsetdec.
Qed.

Instance wf_union s X {Hwf:wf_vsubst s} : 
 wf_vsubst {| v_fv := Ssv.union (v_fv s) X; v_v := v_v s |}.
Proof.
  constructor;first by apply (@vdft_v _ Hwf).
  by move=> x /(@vindom_v s Hwf) /=;SsvD.fsetdec.
Qed.

Lemma gen_mod_imp pm sm modi s Q st:
  wf_vsubst s -> 
  (forall x, Sv.In x modi -> ~~Mv.indom x (v_v s)) ->
  f2h pm sm (gen_mod modi s Q) st -> f2h pm sm (fsubst s Q) st.
Proof.
  move=> Hwf Hin Hgen. 
  have : f2h pm sm (fsubst {| v_fv := Ssv.union (v_fv s) (sffv Q); v_v := v_v s |} Q) st.
  + apply: gen_mod_rec_imp Hgen => /=;first by SsvD.fsetdec.
    + by apply Sv.elements_spec2w.
    by move=> x /SvP.MP.Dec.F.elements_iff;apply Hin.
  by apply iffLR;rewrite /f2h !fsubstP;apply feq_on_fv.
Qed.

Lemma fv_gen_mod_rec s Q modi x:
  wf_vsubst s ->
  Sv.In x (ffv (gen_mod_rec modi s Q)) ->
  (forall z, Mv.indom z (v_v s) -> ~Sv.In x (fv (v_v s).[z]%mv)) -> 
  [/\ ~SetoidList.InA eq x modi,  ~Mv.indom x (v_v s) & Sv.In x (ffv Q)].
Proof.
  elim: modi s=> [| y modi Hrec] /= s Hwf.
  + rewrite fv_fsubst. 
    + move=> H1 H2;have : ~ Mv.indom x (v_v s) /\ Sv.In x (ffv Q).
      + move:H1;rewrite /fv_subst;apply SvP.MP.fold_rec;first by SvD.fsetdec.
        move => w ???;rewrite /fv_subst_body /=. 
        case Heq:Mv.indom (H2 w)=> [] => [/(_ (erefl _)) | _ ].
        + by rewrite Sv.union_spec /SvP.MP.Add=> H1 ?? -> Ha [//| /Ha] [];split;auto.
        rewrite /SvP.MP.Add Sv.add_spec => ?? -> H [-> | /H];last by tauto.
        by rewrite Heq;auto.
      by move=> [??];split=> // H;inversion H.
    by move=> z;rewrite (negbTE (Msv.indom0 _ _)).
  rewrite ffv_quant => /Hrec{Hrec} /= Hrec Hdom;case Hrec=> {Hrec}.
  + move=> z;rewrite Mv.indom_setP;case: (_ =P _) => [<- _ | /eqP ?] /=.
    + by rewrite Mv.setP_eq [fv (SVar _ _)]fv_svar; SvD.fsetdec.
    by rewrite Mv.setP_neq //;apply Hdom.  
  rewrite Mv.indom_setP=> ? /negP;rewrite negb_or=> /andP []/eqP ? /negP ??;split=> //.
  by move=> H;inversion H;subst.
Qed.

Lemma fv_gen_mod s Q modi x: 
  wf_vsubst s ->
  (forall z, Mv.indom z (v_v s) -> ~Sv.In x (fv (v_v s).[z]%mv)) -> 
  Sv.In x (ffv (gen_mod modi s Q)) -> 
  [/\ ~Sv.In x modi,  ~Mv.indom x (v_v s) & Sv.In x (ffv Q)].
Proof.
  move=> Hwf Hdom /fv_gen_mod_rec /= [] // ???;split => //.
  by rewrite SvD.F.elements_iff.
Qed.
  
Lemma shoare_for pm (sm:smap) fi (i : rval sword) dir (e1 e2 : pexpr sword) c P I Q c1 id0 I' Q':
  wp_for dir i e1 e2 c I Q = Some ((id0,I'),Q') ->
  (forall (v0:word), 
     let i0  := SVar sword id0 in
     let sm0 := sm.[i0 <- v0]%msv in
      hoare (f2h pm sm0 (f_and I (f_eq (p2sp (rval2pe i)) i0))) c (f2h pm sm0 I')) ->
  hoare P c1 (f2h pm sm Q') -> 
  hoare P (rcons c1 (Cfor fi i (dir,e1,e2) c)) (f2h pm sm Q).
Proof.
  rewrite /wp_for /pre_for;case: ifP=> //=.
  move=> /andP [] /SvD.F.is_empty_2 He /SvD.F.is_empty_2 Hi [] <- <- <- Hc Hc1.
  rewrite -cats1;apply (hoare_seq Hc1).
  set e := if dir is UpTo then p2sp e2 else p2sp e1.
  set e0 := if dir is UpTo then p2sp e1 else p2sp e2.
  have wf_ew: wf_vsubst (ewrite i e Ssv.empty).
  + by apply wf_ewrite;rewrite /e;case dir;rewrite sfv_p2sp.
  have wf_ew0: wf_vsubst (ewrite i e0 Ssv.empty).
  + by apply wf_ewrite;rewrite /e0;case dir;rewrite sfv_p2sp.
  match type of Hc1 with
  | hoare _ _ (f2h _ _ (f_and ?X1 (f_and ?X2 ?X3))) => 
    set lee := X1; set I0 := X2; set IQ := X3 end.
  set Eqi := f_eq (p2sp (rval2pe i)) e.
  apply (@hoare_conseq (f2h pm sm (f_and (f_and lee I0) IQ))
          (f2h pm sm (f_and (f_and I Eqi) IQ))).
  + by move=> s;rewrite /f2h /=;tauto.
  + move=> s [[HI HEqi]] /gen_mod_imp. as_subgoal.
    + rewrite /ewrite /= => x Hx;apply /negP=> /indom_ewrite_rval.
      by rewrite /vs0 (negbTE (Mv.indom0 _ _)) => -[] //;SvD.fsetdec.
    rewrite /f2h;set rho := {| pm := pm; sm := sm; vm := sevm s |}.
    rewrite fsubstP (@feq_on_fv (f_imp I Q) _ rho) //.
    + by move=> H;apply H.
    constructor => // z Hz /=.
    rewrite Fv.get0 (@ewrite_rvalP rho (sevm s));last by move=> ?;rewrite Mv.get0.
    have -> : ssem_spexpr rho e = ssem_rval (sevm s) i.
    + by move: HEqi;rewrite /Eqi /f_eq /= seqP => /eqP <-;rewrite sem_p2sp ssem_rval2pe.
    by rewrite swrite_ssem_rval.
  apply hoare_notmod;rewrite -/ssem_sform.
  + move=> s1 s2 Hs;apply feq_on_fv=> //=;constructor => z Hz //=.
    apply Hs;rewrite write_c_cons write_i_for write_c_nil.
    case : (SvP.MP.In_dec z (fv e)).
    + rewrite /e;case dir;SvD.fsetdec.
    move=> Hze; move: Hz=> /fv_gen_mod [].
    + move=> y;rewrite /ewrite /= => /indom_ewrite_rval.
      rewrite (negbTE (Mv.indom0 _ _)) => -[] // Hin.
      by have := @fv_ewrite y _ i e vs0 Hin; SvD.fsetdec.
    rewrite indom_ewrite_rval (negbTE (Mv.indom0 _ _)) !Sv.union_spec=> H1 H2 _ [] => //;
      last by SvD.fsetdec.
    by move=> [] ?;[apply H2|apply H1];auto.  
  
  apply: (hoare_conseq _ _ (@hoare_for_base fi i dir e1 e2 (f2h pm sm I) c _ _ _)).
  + move=> s /=. rewrite /f_and sleP /I0 /= !sem_p2sp /= => -[] [] ? HI0 _;split=>//.
    move:HI0;apply iffRL;rewrite fsubstP /f2h /=.
    apply feq_on_fv=> //=;constructor=> // z Hz /=.
    rewrite Fv.get0 (@ewrite_rvalP _ (sevm s)).
    + by case dir;rewrite sem_p2sp. 
    by move=> x;rewrite Mv.get0. 
  + move=> s /= [H1 H2];split => //.
    by rewrite seqP /= sem_p2sp ssem_rval2pe /e;case: (dir) H2;rewrite sem_p2sp=> /eqP.
  + move=> s1 s2 Heq;rewrite -(@sem_p2sp _ e1 {|pm:= pm;sm:=sm;vm:=s1|})
                             -(@sem_p2sp _ e1 {|pm:= pm;sm:=sm;vm:=s2|}).
    by apply eq_on_fv;constructor => //= x Hin;apply Heq;SvD.fsetdec.
  + move=> s1 s2 Heq;rewrite -(@sem_p2sp _ e2 {|pm:= pm;sm:=sm;vm:=s1|})
                             -(@sem_p2sp _ e2 {|pm:= pm;sm:=sm;vm:=s2|}).
    by apply eq_on_fv;constructor => //= x Hin;apply Heq;SvD.fsetdec.

  move=> w1 w2 i0 {Hc1}.
  apply (@hoare_conseq (fun s : sestate =>
      (f2h pm sm I s /\ w1 <= i0 <= w2) /\
      (ssem_rval (sevm s) i = i0 /\ ssem_pexpr (sevm s) e1 = w1 /\ ssem_pexpr (sevm s) e2 = w2))
      (fun s : sestate =>
      (let i1 :=
         if i0 == match dir with
                  | UpTo => ssem_pexpr (sevm s) e2
                  | DownTo => ssem_pexpr (sevm s) e1
                  end
         then i0
         else incr dir i0 in
       let s' := {| semem := semem s; sevm := swrite_rval (sevm s) i i1 |} in
       f2h pm sm I s') /\
       (ssem_rval (sevm s) i = i0 /\ 
        ssem_pexpr (sevm s) e1 = w1 /\ ssem_pexpr (sevm s) e2 = w2))).
  + by move=> s [] ?????;split;split.
  + move=> s [] /= ? [] Hi0 [Hw1 Hw2];split=> //;split => //.
    + by rewrite -Hw1 -Hw2.
    + rewrite -{2}Hw1 -!(sem_p2sp e1 {|pm:=pm; sm:= sm; vm:= _|}).
      apply (@eq_on_fv _ (p2sp e1))=> //;constructor => //= x Hx.
      by apply swrite_nin;SvD.fsetdec.
    rewrite -{2}Hw2 -!(sem_p2sp e2 {|pm:=pm; sm:= sm; vm:= _|}).
    apply (@eq_on_fv _ (p2sp e2))=> //;constructor => //= x Hx.
    by apply swrite_nin;SvD.fsetdec.
  apply hoare_notmod.
  + move=> s1 s2 Hs.
    rewrite -!ssem_rval2pe.
    rewrite -!(sem_p2sp (rval2pe i) {|pm:=pm; sm:= sm; vm:= _|})
       -!(sem_p2sp e2 {|pm:=pm; sm:= sm; vm:= _|})
       -!(sem_p2sp e1 {|pm:=pm; sm:= sm; vm:= _|}). 
    set st1 := {| pm := pm; sm := sm; vm := sevm s1 |}.
    set st2 := {| pm := pm; sm := sm; vm := sevm s2 |}.
    rewrite (@eq_on_fv _ (p2sp (rval2pe i)) st1 st2)
           ?(@eq_on_fv _ (p2sp e1) st1 st2) ?(@eq_on_fv _ (p2sp e2) st1 st2) //. 
    + by constructor=> //= x Hx;apply Hs;SvD.fsetdec.
    + by constructor=> //= x Hx;apply Hs;SvD.fsetdec.
    by constructor=> //= x Hx;apply Hs;move: Hx; rewrite fv_rval2pe;SvD.fsetdec.
  apply: hoare_conseq (Hc i0) => s /=.
  + move=> [] [] HI ? [] ? [] ??;rewrite /f2h /= seqP /= Msv.setP_eq;split.
    + apply: iffRL HI;apply feq_on_fv => //=;constructor => x Hx //=.
      rewrite Msv.setP_neq //;apply /eqP => ?;subst.
      by apply: fresh_svarP Hx.
    by apply /eqP;rewrite sem_p2sp /= ssem_rval2pe.
  rewrite /post_for_body.
  apply iffLR.
  set i' := (SVar sword (fresh_svar (sffv I))).
  set k1 := (seq i' _).
  set k2 := (x in sif _ _ x).
  have Hsub : Ssv.Subset (sfv (sif k1 i' k2)) (Ssv.singleton i').
  + apply (SsvP.MP.subset_trans (@sfv_sif _ k1 i' k2)).
    rewrite sfv_if /k1 /k2;case dir.
    + have := @sfv_seq i' (p2sp e2).
      rewrite !sfv_op2 !sfv_p2sp sfv_const sfv_svar /=. 
      rewrite (@SsvP.MP.empty_union_2 Ssv.empty);auto=> ?.
      by apply SsvP.MP.union_subset_3 => //;apply SsvP.MP.union_subset_3.
    have := @sfv_seq i' (p2sp e1).
    rewrite !sfv_op2 !sfv_p2sp sfv_const sfv_svar /=. 
    rewrite (@SsvP.MP.empty_union_2 Ssv.empty);auto=> ?.
    by apply SsvP.MP.union_subset_3 => //;apply SsvP.MP.union_subset_3.
  have wfe' := @wf_ewrite _ i (sif k1 i' k2) (Ssv.singleton i') Hsub.
  rewrite /f2h fsubstP;apply feq_on_fv=> //=;constructor => /= x Hx.
  + rewrite Fv.get0 (@ewrite_rvalP _ (sevm s)) /k1 /k2 /i'.
    + by rewrite sifP /= seqP /= Msv.setP_eq;case dir;rewrite sem_p2sp /= Msv.setP_eq.
    by move=> ?;rewrite Mv.get0.
  rewrite Msv.get0 Msv.setP_neq //;apply /eqP=> ?;subst x.
  by apply: fresh_svarP Hx.
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

Definition sx := (SVar sword 2%positive).

Definition w0 : N := 0.
Definition w1 : N := 1.

Definition c := 
  [:: assgn x w0;
      assgn y w1;
      Cif (Papp2 Oeq x w1) [::assgn z x] [::assgn z y] ].

Definition pm0 := @Msv.empty sst2pred (fun x (_:sst2ty x.(svtype)) => True).

Lemma c_ok : 
  hoare (f2h pm0 msv0 (Fbool true)) c (f2h pm0 msv0 (Fbool (Eapp2 Oand (Eapp2 Oeq x 0%num) 
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
  hoare (f2h pm0 msv0 (Fbool true)) c' 
        (f2h pm0 msv0 (Fbool (Eapp2 Oand (Eapp2 Oeq x 0%num) 
                                           (Eapp2 Oeq z 0%num)))).
Proof.
  wp_core. by skip.
Qed.
*)

End SEM.