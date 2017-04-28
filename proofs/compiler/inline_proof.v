(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils type var expr 
               memory sem compiler_util allocation inline.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section INLINE.

Variable rename_fd : funname -> fundef -> fundef.

Lemma get_funP p ii f fd : 
  get_fun p ii f = ok fd -> get_fundef p f = Some fd.
Proof. by rewrite /get_fun;case:get_fundef => // ? [->]. Qed.

Local Notation inline_i' := (inline_i rename_fd).
Local Notation inline_fd' := (inline_fd rename_fd).
Local Notation inline_prog' := (inline_prog rename_fd).

Section INCL.

  Variable p p': prog.  

  Hypothesis Incl : forall f fd, 
    get_fundef p f = Some fd -> get_fundef p' f = Some fd.

  Let Pi i := forall X1 c' X2,
    inline_i' p  i X2 = ok (X1, c') ->
    inline_i' p' i X2 = ok (X1, c').

  Let Pr i := forall ii, Pi (MkI ii i).

  Let Pc c :=  forall X1 c' X2, 
    inline_c (inline_i' p)  c X2 = ok (X1, c') ->
    inline_c (inline_i' p') c X2 = ok (X1, c').
 
  Lemma inline_c_incl c : Pc c.
  Proof.
    apply (@cmd_rect Pr Pi Pc) => // {c}.
    + move=> i c Hi Hc X1 c' X2 /=.
      apply:rbindP => -[Xc cc] /Hc -> /=.
      by apply:rbindP => -[Xi ci] /Hi ->.
    + by move=> * ?. 
    + by move=> * ?.
    + move=> e c1 c2 Hc1 Hc2 ii X1 c' X2 /=.
      apply: rbindP => -[Xc1 c1'] /Hc1 -> /=.
      by apply: rbindP => -[Xc2 c2'] /Hc2 -> /= [] <- <-.
    + move=> i dir lo hi c Hc ii X1 c0 X2 /=.
      by apply: rbindP => -[Xc c'] /Hc -> /=.     
    + move=> c e c' Hc Hc' ii X1 c0 X2 /=.
      apply: rbindP => -[Xc1 c1] /Hc -> /=.
      by apply: rbindP => -[Xc1' c1'] /Hc' -> /=.
    move=> i xs f es ii X1 c' X2 /=.
    case: i => //;apply: rbindP => fd /get_funP -/Incl.
    by rewrite /get_fun => ->.
  Qed.

  Lemma inline_incl fd fd' :
    inline_fd' p fd = ok fd' ->
    inline_fd' p' fd = ok fd'.
  Proof.
    by case: fd => fi fp fb fr /=;apply: rbindP => -[??] /inline_c_incl -> [<-].
  Qed.

End INCL. 

Lemma inline_prog_fst p p' :
  inline_prog' p = ok p' ->
  [seq x.1 | x <- p] = [seq x.1 | x <- p'].
Proof.
  elim: p p' => [ ?[<-] | [f fd] p Hrec p'] //=. 
  by apply: rbindP => ? /Hrec -> /=;apply:rbindP => ?? [] <-.
Qed.

Lemma inline_progP p p' f fd' :
  uniq [seq x.1 | x <- p] ->
  inline_prog' p = ok p' ->
  get_fundef p' f = Some fd' ->
  exists fd, get_fundef p f = Some fd /\ inline_fd' p' fd = ok fd'.
Proof.
  elim: p p' => [ | [f1 fd1] p Hrec] p' /=. 
  + by move=> _ [<-].
  move=> /andP [] Hf1 Huniq.
  apply: rbindP => p1 Hp1 /=.
  apply: rbindP => fd1';apply: add_finfoP => Hinl [] <-.
  rewrite !get_fundef_cons /=;case: eqP => [? [?]| Hne].
  + subst f1 fd';exists fd1;split=>//.
    apply: inline_incl Hinl => f0 fd0;rewrite get_fundef_cons /=.
    case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
    by move: Hf1;rewrite (inline_prog_fst Hp1) H.
  move=> /(Hrec   _ Huniq Hp1) [fd [? H]];exists fd;split=>//.
  apply: inline_incl H => f0 fd0;rewrite get_fundef_cons /=.
  case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
  by move: Hf1;rewrite (inline_prog_fst Hp1) H.
Qed.

Lemma inline_progP' p p' f fd :
  uniq [seq x.1 | x <- p] ->
  inline_prog' p = ok p' ->
  get_fundef p f = Some fd ->
  exists fd', get_fundef p' f = Some fd' /\ inline_fd' p' fd = ok fd'.
Proof.
  elim: p p' => [ | [f1 fd1] p Hrec] p' //. 
  rewrite /= => /andP [] Hf1 Huniq.
  apply: rbindP => p1 Hp1.
  apply: rbindP => fd1';apply: add_finfoP => Hinl [] <-.
  rewrite !get_fundef_cons /=;case: eqP => [? [?]| Hne].
  + subst f1 fd1;exists fd1';split=>//.
    apply: inline_incl Hinl => f0 fd0;rewrite get_fundef_cons /=.
    case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
    by move: Hf1;rewrite (inline_prog_fst Hp1) H.
  move=> /(Hrec   _ Huniq Hp1) [fd' [? H]];exists fd';split=>//.
  apply: inline_incl H => f0 fd0;rewrite get_fundef_cons /=.
  case: eqP => // -> H; have := (get_fundef_in H)=> {H}H.
  by move: Hf1;rewrite (inline_prog_fst Hp1) H.
Qed.

Section SUBSET.

  Variable p : prog.  

  Let Pi i := forall X2 Xc,
    inline_i' p i X2 = ok Xc -> Sv.Equal Xc.1 (Sv.union (read_I i) X2).

  Let Pr i := forall ii, Pi (MkI ii i).

  Let Pc c := 
    forall X2 Xc,
      inline_c (inline_i' p) c X2 = ok Xc -> Sv.Equal Xc.1 (Sv.union (read_c c) X2).

  Local Lemma Smk    : forall i ii, Pr i -> Pi (MkI ii i).
  Proof. done. Qed.

  Local Lemma Snil   : Pc [::].
  Proof. by move=> X2 Xc [<-]. Qed.

  Local Lemma Scons  : forall i c, Pi i -> Pc c -> Pc (i::c).
  Proof. 
    move=> i c Hi Hc X2 Xc /=.
    apply:rbindP=> Xc' /Hc ?;apply:rbindP => Xi /Hi ? [<-] /=.
    rewrite read_c_cons;SvD.fsetdec.
  Qed.

  Local Lemma Sasgn  : forall x t e, Pr (Cassgn x t e).
  Proof. by move=> ??? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sopn   : forall xs o es, Pr (Copn xs o es).
  Proof. by move=> ??? ii X2 Xc /= [<-]. Qed.

  Local Lemma Sif    : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof. 
    move=> e c1 c2 Hc1 Hc2 ii X2 Xc /=.
    apply: rbindP => Xc1 /Hc1 ?;apply:rbindP=> Xc2 /Hc2 ? [<-] /=.
    rewrite read_Ii read_i_if read_eE;SvD.fsetdec.
  Qed.

  Local Lemma Sfor   : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof. by move=> i d lo hi c Hc ii X2 Xc;apply:rbindP => Xc' /Hc ? [<-]. Qed.

  Local Lemma Swhile : forall c e c', Pc c -> Pc c' -> Pr (Cwhile c e c').
  Proof.
    move=> c e c' Hc Hc' ii X2 Xc;apply:rbindP=> Xc' /Hc ?.
    by apply: rbindP=> Hc'' /Hc' ? [<-].
  Qed.

  Local Lemma Scall  : forall i xs f es, Pr (Ccall i xs f es).
  Proof. 
    move=> i xs f es ii X2 Xc /=;case: i => [ | [<-] //].
    by apply:rbindP => fd _;apply: rbindP => ?? [<-].
  Qed. 

  Lemma inline_c_subset c : Pc c.
  Proof.
    by apply (@cmd_rect Pr Pi Pc Smk Snil Scons Sasgn Sopn Sif Sfor Swhile Scall).
  Qed.

  Lemma inline_i_subset i : Pr i.
  Proof.
    by apply (@instr_r_Rect Pr Pi Pc Smk Snil Scons Sasgn Sopn Sif Sfor Swhile Scall).
  Qed.
  
  Lemma inline_i'_subset i : Pi i.
  Proof.
    by apply (@instr_Rect Pr Pi Pc Smk Snil Scons Sasgn Sopn Sif Sfor Swhile Scall).
  Qed.
  
End SUBSET.

Lemma assgn_tuple_Lvar p ii (xs:seq var_i) es vs s s' :
  let xs := map Lvar xs in
  disjoint (vrvs xs) (read_es es) ->  
  sem_pexprs s es = ok vs ->
  write_lvals s xs vs = ok s' ->
  sem p s (assgn_tuple ii xs es) s'.
Proof.
  rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  elim: xs es vs s s' => [ | x xs Hrec] [ | e es] [ | v vs] s s' //=.
  + by move=> _ _ [<-];constructor.
  + by move=> _;apply: rbindP => ??;apply:rbindP.
  rewrite vrvs_cons vrv_var read_es_cons=> Hempty.
  apply: rbindP => ve Hse;apply:rbindP => vz Hses [??]; subst ve vz.
  apply: rbindP => s1 Hw Hws. 
  apply Eseq with s1;first by constructor;constructor;rewrite Hse.
  apply : Hrec Hws;first by SvD.fsetdec.
  apply:rbindP Hw => vm;apply: rbindP => z ? [<-] [<-] /=.
  rewrite -Hses=> {Hse Hses};case:s => sm svm /=. apply read_es_eq_on with Sv.empty.
  rewrite read_esE => y Hy;rewrite Fv.setP_neq //;apply/eqP;SvD.fsetdec.
Qed.

Lemma assgn_tuple_Pvar p ii xs rxs vs s s' :
  let es := map Pvar rxs in
  disjoint (vrvs xs) (read_es es) -> 
  mapM (fun x : var_i => get_var (evm s) x) rxs = ok vs ->
  write_lvals s xs vs = ok s' ->
  sem p s (assgn_tuple ii xs es) s'.
Proof.
  rewrite /disjoint /assgn_tuple /is_true Sv.is_empty_spec.
  have : evm s = evm s [\vrvs xs] by done.
  have : Sv.Subset (vrvs xs) (vrvs xs) by done.
  move: {1 3}s => s0;move: {2 3 4}(vrvs xs) => X.
  elim: xs rxs vs s s' => [ | x xs Hrec] [ | rx rxs] [ | v vs] s s' //=.
  + by move=> _ _ _ _ [<-];constructor.
  + by move=> _ _ _;apply: rbindP => ??;apply:rbindP.
  rewrite vrvs_cons read_es_cons read_e_var => Hsub Heqe Hempty.
  apply: rbindP => ve Hse;apply:rbindP => vz Hses [??]; subst ve vz.
  apply: rbindP => s1 Hw Hws; apply Eseq with s1. 
  + constructor;constructor;rewrite /=.
    have /get_var_eq_on: evm s0 =[Sv.singleton rx] evm s. 
      move=> y ?;apply: Heqe;SvD.fsetdec.
    by move=> <-;[rewrite Hse | SvD.fsetdec].
  apply: Hrec Hses Hws;[SvD.fsetdec| |SvD.fsetdec].
  by move=> y Hy;rewrite Heqe //;apply (vrvP Hw);SvD.fsetdec.
Qed.

Section WF.

  Definition wf_vm (vm:vmap) := 
    forall x,
      match vm.[x], vtype x with
      | Error _, sarr n => False
      | _, _            => True
      end.

  Lemma wf_set_var x ve vm1 vm2 :
    wf_vm vm1 -> set_var vm1 x ve = ok vm2 -> wf_vm vm2.
  Proof.
    move=> Hwf;apply: rbindP => v ? [<-] /= z.
    case: (x =P z) => [ <- | /eqP Hne];first by rewrite Fv.setP_eq.
    by rewrite Fv.setP_neq //;apply (Hwf z).
  Qed.
  
  Lemma wf_write_var x ve s1 s2 :
    wf_vm (evm s1) -> write_var x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof. 
    by move=> HWf; apply: rbindP => vm Hset [<-] /=;apply: wf_set_var Hset. 
  Qed.
 
  Lemma wf_write_vars x ve s1 s2 :
    wf_vm (evm s1) -> write_vars x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof. 
    elim: x ve s1 s2=> [ | x xs Hrec] [ | e es] //= s1 s2.
    + by move=> ? [<-].
    by move=> Hwf; apply: rbindP => vm /(wf_write_var Hwf) -/Hrec H/H.
  Qed.
  
  Lemma wf_write_lval x ve s1 s2 :
    wf_vm (evm s1) -> write_lval x ve s1 = ok s2 -> wf_vm (evm s2).
  Proof.
    case: x => [vi|v|v e|v e] /= Hwf.
    + by move=> [<-]. + by apply wf_write_var. + by t_rbindP => -[<-].
    apply: on_arr_varP => n t ? ?.   
    apply:rbindP => ??;apply:rbindP => ??;apply:rbindP => ??.
    by apply:rbindP=>? Hset [<-] /=;apply: wf_set_var Hset.
  Qed.
  
  Lemma wf_write_lvals xs vs s1 s2 :
    wf_vm (evm s1) -> write_lvals s1 xs vs = ok s2 -> wf_vm (evm s2).
  Proof.
    elim: xs vs s1 => [ | x xs Hrec] [ | v vs] s1 //= Hwf => [[<-]//| ].
    apply: rbindP => s1' /(wf_write_lval Hwf);apply Hrec.
  Qed.

  Lemma wf_sem p s1 c s2 :
    sem p s1 c s2 -> wf_vm (evm s1) -> wf_vm (evm s2).
  Proof.
    apply (@cmd_rect 
             (fun i => forall s1 s2, sem_i p s1 i s2 -> wf_vm (evm s1) -> wf_vm (evm s2))
             (fun i => forall s1 s2, sem_I p s1 i s2 -> wf_vm (evm s1) -> wf_vm (evm s2))
             (fun c => forall s1 s2, sem   p s1 c s2 -> wf_vm (evm s1) -> wf_vm (evm s2)))=>
      {s1 s2 c}.
    + by move=> i ii Hrec s1 s2 H;sinversion H;apply Hrec.
    + by move=> s1 s2 H;sinversion H.
    + by move=> i c Hi Hc s1 s2 H;sinversion H => /(Hi _ _ H3);apply Hc.
    + move=> x t e s1 s2 H;sinversion H.
      by apply:rbindP H5 => v ? Hw ?; apply: wf_write_lval Hw.
    + move=> xs o es s1 s2 H;sinversion H. 
      by apply:rbindP H5 => ?? Hw ?;apply: wf_write_lvals Hw.
    + by move=> e c1 c2 Hc1 Hc2 s1 s2 H;sinversion H;[apply Hc1 | apply Hc2].
    + move=> i dir lo hi c Hc s1 s2 H;sinversion H.
      elim: H9 Hc => // ???? ???? Hw Hsc Hsf Hrec Hc.
      by move=> /wf_write_var -/(_ _ _ _ Hw) -/(Hc _ _ Hsc);apply: Hrec Hc.
    + move=> c e c' Hc Hc' s1 s2 H.
      move: {1 2}(Cwhile c e c') H (refl_equal (Cwhile c e c'))=> i;elim=> //=.
      move=> ??????? Hsc ? Hsc' Hsw Hrec [???];subst.
      move=> /(Hc _ _ Hsc).
      by move=> /(Hc' _ _ Hsc'); apply Hrec.
    + move=> ????? Hsc ? [???];subst.
      exact: (Hc _ _ Hsc).
    move=> i xs f es s1 s2 H;sinversion H=> Hwf.
    by apply: wf_write_lvals H8.
  Qed. 

  Lemma wf_vm_uincl vm : wf_vm vm -> vm_uincl vmap0 vm.
  Proof.
    move=> Hwf x;have := Hwf x;rewrite /vmap0 Fv.get0.
    case: vm.[x];case:(vtype x) => //=.
    by move=> ????? H;have := Array.getP_empty H.
  Qed.
  
  Lemma wf_vmap0 : wf_vm vmap0.
  Proof. by move=> x;rewrite /vmap0 Fv.get0;case:vtype. Qed.

End WF.
  
Section PROOF.

  Variable p p' : prog.

  Hypothesis uniq_funname : uniq [seq x.1 | x <- p].

  Hypothesis Hp : inline_prog' p = ok p'.

  Let Pi_r s1 (i:instr_r) s2:= 
    forall ii X1 X2 c', inline_i' p' (MkI ii i) X2 = ok (X1, c') ->
    forall vm1, wf_vm vm1 -> evm s1 =[X1] vm1 -> 
    exists vm2, [/\ wf_vm vm2, evm s2 =[X2] vm2 &
       sem p' (Estate (emem s1) vm1) c' (Estate (emem s2) vm2)].

  Let Pi s1 (i:instr) s2:= 
    forall X1 X2 c', inline_i' p' i X2 = ok (X1, c') ->
    forall vm1, wf_vm vm1 -> evm s1 =[X1] vm1 -> 
    exists vm2, [/\ wf_vm vm2, evm s2 =[X2] vm2 &
      sem p' (Estate (emem s1) vm1) c' (Estate (emem s2) vm2)].

  Let Pc s1 (c:cmd) s2:= 
    forall X1 X2 c', inline_c (inline_i' p') c X2 = ok (X1, c') ->
    forall vm1, wf_vm vm1 -> evm s1 =[X1] vm1 -> 
    exists vm2, [/\ wf_vm vm2, evm s2 =[X2] vm2 &
      sem p' (Estate (emem s1) vm1) c' (Estate (emem s2) vm2)].

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall X1 X2 c', 
    inline_c (inline_i' p') c X2 = ok (X1, c') ->
    Sv.Equal X1 X2 ->
    forall vm1, wf_vm vm1 -> evm s1 =[X1] vm1 -> 
    exists vm2, [/\ wf_vm vm2, evm s2 =[X2] vm2 &
      sem_for p' i vs (Estate (emem s1) vm1) c' (Estate (emem s2) vm2)].

  Let Pfun (mem:Memory.mem) fn vargs (mem':Memory.mem) vres :=
    sem_call p' mem fn vargs mem' vres.

  Local Lemma Hskip s: Pc s [::] s.
  Proof. move=> X1 X2 c' [<- <-] vm1 Hwf Hvm1;exists vm1;split=>//;constructor. Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p s1 i s2 ->
    Pi s1 i s2 -> sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> _ Hi _ Hc X1 X2 c0 /=;apply: rbindP => -[Xc c'] /Hc Hic.
    apply:rbindP => -[Xi i'] /Hi Hii [<- <-] vm1 /Hii H/H{H} [vm2 []].
    move=> /Hic H/H{H} [vm3 [Hwf3 Hvm3 Hsc']] ?.
    by exists vm3;split=> //;apply: sem_app Hsc'.
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. by move=> _ Hi ??? /Hi. Qed.

  Local Lemma Hassgn s1 s2 x tag e :
    Let v := sem_pexpr s1 e in write_lval x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.
  Proof.
    case: s1 s2 => sm1 svm1 [sm2 svm2].
    apply: rbindP => ve Hse Hw ii X1 X2 c' [] <- <- vm1.
    rewrite read_i_assgn => Hwf Hvm.
    have /read_e_eq_on H: svm1 =[read_e e] vm1 by apply: eq_onI Hvm;SvD.fsetdec.
    rewrite H in Hse.
    have [ | vm2 [/=Hvm2 Hw']]:= write_lval_eq_on _ Hw Hvm; first by SvD.fsetdec.
    have /(_ Hwf):= wf_write_lval _ Hw'.
    exists vm2;split=>//; first by apply: eq_onI Hvm2;SvD.fsetdec.   
    by apply: sem_seq1;constructor;constructor;rewrite Hse.
  Qed.

  Local Lemma Hopn s1 s2 o xs es : 
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_lvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    case: s1 s2 => sm1 svm1 [sm2 svm2].
    apply: rbindP => ve Hse Hw ii X1 X2 c' [] <- <- vm1.
    rewrite read_i_opn => Hwf Hvm.
    have /read_es_eq_on H: svm1 =[read_es es] vm1 by apply: eq_onI Hvm;SvD.fsetdec.
    rewrite H in Hse.
    have [ | vm2 [Hvm2 Hw']]:= write_lvals_eq_on _ Hw Hvm; first by SvD.fsetdec.
    have /(_ Hwf):= wf_write_lvals _ Hw'.
    exists vm2;split=>//; first by apply: eq_onI Hvm2;SvD.fsetdec.   
    by apply: sem_seq1;constructor;constructor;rewrite Hse.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    case: s1 => sm1 svm1.
    apply: rbindP => ve Hse Hto _ Hc ii X1 X2 c'.
    apply: rbindP => -[Xc1 c1'] /Hc Hc1;apply: rbindP => -[Xc2 c2'] ? [<- <-] vm1.
    rewrite read_eE=> Hwf Hvm1.
    case: (Hc1 vm1 _)=>//;first by apply: eq_onI Hvm1;SvD.fsetdec.
    move=> vm2 [Hvm2 Hc1'];exists vm2;split=>//.
    apply sem_seq1;constructor;apply Eif_true => //.
    have /read_e_eq_on <-: svm1 =[read_e e] vm1 by apply: eq_onI Hvm1;SvD.fsetdec.
    by rewrite Hse.
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    case: s1 => sm1 svm1.
    apply: rbindP => ve Hse Hto _ Hc ii X1 X2 c'.
    apply: rbindP => -[Xc1 c1'] ?;apply: rbindP => -[Xc2 c2'] /Hc Hc2 [<- <-] vm1.
    rewrite read_eE=> Hwf Hvm1.
    case: (Hc2 vm1 _)=>//;first by apply: eq_onI Hvm1;SvD.fsetdec.
    move=> vm2 [Hvm2 Hc1'];exists vm2;split=>//.
    apply sem_seq1;constructor;apply Eif_false => //.
    have /read_e_eq_on <-: svm1 =[read_e e] vm1 by apply: eq_onI Hvm1;SvD.fsetdec.
    by rewrite Hse.
  Qed.
    
  Local Lemma Hwhile_true s1 s2 s3 s4 c e c':
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = Ok error true ->
    sem p s2 c' s3 -> Pc s2 c' s3 ->
    sem_i p s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> 
    Pi_r s1 (Cwhile c e c') s4.
  Proof.
    case: s1 => sm1 svm1 Hsc Hc Hse Hsc' Hc' _ Hw ii X1 X2 cw Hi.
    move: (Hi) => /=;set X3 := Sv.union _ _;apply: rbindP => -[Xc c1] Hc1.
    apply: rbindP => -[Xc' c1'] Hc1' [] ??;subst X1 cw => vm1 Hwf Hvm1.
    case : (Hc _ _ _ Hc1 _ Hwf) => [| vm2 [Hwf2 Hvm2 Hsc1]].
    + apply: eq_onI Hvm1; have /= -> := inline_c_subset Hc1.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    case : (Hc' _ _ _ Hc1' _ Hwf2) => [| vm3 [Hwf3 Hvm3 Hsc2]].
    + apply: eq_onI Hvm2; have /= -> := inline_c_subset Hc1'.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    have [vm4 [Hwf4 Hvm4 Hsw]]:= Hw _ _ _ _ Hi _ Hwf3 Hvm3.
    exists vm4;split => //;apply sem_seq1;constructor.
    sinversion Hsw; sinversion H4;sinversion H2.
    apply: (Ewhile_true Hsc1) Hsc2 H4.
    have /read_e_eq_on <- : (evm s2) =[read_e e] vm2. 
    + by apply: eq_onI Hvm2;rewrite /X3 read_i_while;SvD.fsetdec.
    by case: (s2) Hse.
  Qed.

  Local Lemma Hwhile_false s1 s2 c e c':
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = Ok error false ->
    Pi_r s1 (Cwhile c e c') s2.
  Proof.
    case: s1 s2 => sm1 svm1 [sm2 svm2] Hsc Hc Hse ii X1 X2 cw /=.
    set X3 := Sv.union _ _;apply: rbindP => -[Xc c1] Hc1.
    apply: rbindP => -[Xc' c1'] Hc1' [] ??;subst X1 cw => vm1 Hwf Hvm1.
    case : (Hc _ _ _ Hc1 _ Hwf) => [| vm2 [Hwf2 Hvm2 Hsc1]].
    + apply: eq_onI Hvm1; have /= -> := inline_c_subset Hc1.
      by rewrite /X3 read_i_while;SvD.fsetdec.
    exists vm2;split=>//. 
    + by apply: eq_onI Hvm2;rewrite /X3;SvD.fsetdec.
    apply sem_seq1;constructor;apply Ewhile_false => //.
    have /read_e_eq_on <- //: svm2 =[read_e e] vm2.
    apply: eq_onI Hvm2;rewrite /X3 read_i_while;SvD.fsetdec.
  Qed.
 
  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for p i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    case: s1 => sm1 svm1.
    apply: rbindP => zlo Hlo Tlo;apply: rbindP => zhi Hhi Thi _ Hf ii X1 X2 cf Hi.
    apply: rbindP Hi => -[Xc' c'] Hi [??] vm1 Hwf Hvm1;subst.
    have Hxc': Sv.Equal Xc' (Sv.union (read_i (Cfor i (d, lo, hi) c)) X2).
    + by have /= -> := inline_c_subset Hi;rewrite read_i_for;SvD.fsetdec.
    have [ /=| vm2 [Hwf2 Hvm2 Hsf]]:= Hf _ _ _ Hi Hxc' _ Hwf.
    + by apply: eq_onI Hvm1;rewrite Hxc'.
    exists vm2;split=>//;first by apply: eq_onI Hvm2;SvD.fsetdec.
    move: Hvm1;rewrite read_i_for => Hvm1.
    apply sem_seq1;constructor;eapply Efor;eauto=> /=.
    + have /read_e_eq_on <-: svm1 =[read_e lo] vm1 by apply: eq_onI Hvm1; SvD.fsetdec.
      by rewrite Hlo.   
    have /read_e_eq_on <-: svm1 =[read_e hi] vm1 by apply: eq_onI Hvm1; SvD.fsetdec.
    by rewrite Hhi.   
  Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof.
    move=> X1 X2 c' Hc HX vm1 Hwf Hvm1;exists vm1;split=>//;first by rewrite -HX.
    constructor.
  Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem p s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
    move=> Hwi _ Hc _ Hfor X1 X2 c' Hic HX vm1 Hwf Hvm1.
    have [vm1' [Hvm1' Hw]]:= write_var_eq_on Hwi Hvm1.
    have /(_ Hwf)Hwf' := wf_write_var _ Hw.
    have [|vm2 [] ]:= Hc _ _ _ Hic _ Hwf';first by apply: eq_onI Hvm1';SvD.fsetdec.
    rewrite -{1}HX => Hwf2 Hvm2 Hsc'.
    have [vm3 [?? Hsf']] := Hfor _ _ _ Hic HX _ Hwf2 Hvm2.
    by exists vm3;split=>//;apply: EForOne Hsc' Hsf'.
  Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs s1 args = Ok error vargs ->
    sem_call p (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_lvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    case:s1 => sm1 svm1 /= Hes Hsc Hfun Hw ii' X1 X2 c' /=;case:ii;last first.
    + move=> [<- <-] vm1 Hwf1 Hvm1. 
      have [|vm2 /= [Hvm2 Hxs]]:= write_lvals_eq_on _ Hw Hvm1.
      + by rewrite read_i_call;SvD.fsetdec.
      exists vm2;split.
      + by apply: wf_write_lvals Hxs.
      + by apply: eq_onI Hvm2;rewrite read_i_call;SvD.fsetdec.
      apply sem_seq1;constructor;eapply Ecall;eauto.
      symmetry;rewrite -Hes;apply read_es_eq_on with Sv.empty.
      by apply: eq_onI Hvm1;rewrite read_esE read_i_call;SvD.fsetdec.
    apply: rbindP => fd' /get_funP Hfd'.
    have [fd [Hfd Hinline]] := inline_progP uniq_funname Hp Hfd'.
    apply: rbindP => -[];apply:rbindP => -[];apply: add_infunP => Hcheckf.
    sinversion Hfun. move: H;rewrite Hfd' => -[?];subst f.
    have [s1' [vm2' [Hwv Hbody Hvs]]]:= CheckAllocReg.alloc_funP_eq Hcheckf H0 H1 H2 H3. 
    move=> /=;case: ifP => //= Hdisj _ [<- <-] vm1 Hwf1.
    move=> {H0 H1 H2 Hfd' Hfd Hcheckf Hsc Hinline}.
    move: Hdisj; rewrite read_i_call vrvs_recE write_c_recE.
    move: Hvs Hwv Hbody;set rfd := rename_fd _ => Hvs Hwv Hbody Hdisjoint Hvm1.
    rewrite write_vars_lvals in Hwv.
    have [||/= vm1' [Wvm1' Uvm1']]:= @writes_uincl _ _ vm1 _ vargs vargs _ _ Hwv.
    + by apply wf_vm_uincl. + by apply List_Forall2_refl.
    have [vm3 [Hsem' Uvm3]]:= sem_uincl Uvm1' Hbody.
    have [vs' [Hvs' /(is_full_array_uincls H3) Uvs]]:= get_vars_uincl Uvm3 Hvs;subst vs'.
    move=> {Hvs Hbody Hwv}.
    have Heqvm : svm1 =[Sv.union (read_rvs xs) X2] vm3.
    + apply eq_onT with vm1;first by apply: eq_onI Hvm1;SvD.fsetdec.
      apply eq_onT with vm1'.
      + apply: disjoint_eq_ons Wvm1'.
        by move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec;SvD.fsetdec.
      move=> z Hz;apply (writeP Hsem').
      by move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec;SvD.fsetdec.
    have [|vm4 [/= Hvm4 Hw']]:= write_lvals_eq_on _ Hw Heqvm;first by SvD.fsetdec.
    exists vm4;split.
    + by apply: wf_write_lvals Hw';apply: (wf_sem Hsem');apply: wf_write_lvals Wvm1'.
    + by apply: eq_onI Hvm4;SvD.fsetdec.
    apply sem_app with {| emem := emem s1'; evm := vm1' |}.
    + apply: assgn_tuple_Lvar Wvm1'.
      + by move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec;SvD.fsetdec.
      have /read_es_eq_on -/(_ sm1) <- // : svm1 =[read_es args] vm1.
      by apply: eq_onI Hvm1;SvD.fsetdec.
    apply: (sem_app Hsem');apply: assgn_tuple_Pvar Hw' => //.
    by move: Hdisjoint;rewrite /disjoint /is_true !Sv.is_empty_spec;SvD.fsetdec.
  Qed.

  Local Lemma Hproc m1 m2 fn fd vargs s1 vm2 vres: 
    get_fundef p fn = Some fd ->
    write_vars (f_params fd) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem p s1 (f_body fd) {| emem := m2; evm := vm2 |} -> 
    Pc s1 (f_body fd) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res fd) = ok vres ->
    List.Forall is_full_array vres -> 
    Pfun m1 fn vargs m2 vres.
  Proof.
    move=> Hget Hw Hsem Hc Hres Hfull.
    have [fd' [Hfd]{Hget}] := inline_progP' uniq_funname Hp Hget.
    case: fd Hw Hsem Hc Hres => /= fi fx fc fxr Hw Hsem Hc Hres.
    apply: rbindP => -[X fc'] /Hc{Hc} -/(_ (evm s1)) [] => //.
    + by apply: wf_write_vars Hw;apply wf_vmap0.
    move=> vm1 /= [Hwf1 Heq Hsem'] [?];subst fd'=> {Hsem}.
    case: s1 Hw Hsem' => /= sm1 svm1 Hw Hsem'.
    apply: (EcallRun Hfd Hw Hsem')=>//=.
    have /= <- := @sem_pexprs_get_var (Estate m2 vm1).
    have <- := @read_es_eq_on _ Sv.empty m2 _ _ Heq.
    by rewrite sem_pexprs_get_var.
  Qed.

  Lemma inline_callP f mem mem' va vr: 
    sem_call p mem f va mem' vr -> 
    sem_call p' mem f va mem' vr.
  Proof.
    apply (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End PROOF.

End INLINE.
