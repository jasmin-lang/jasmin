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

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem compiler_util.
Require Export makeReferenceArguments.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Section Section.

  Context (is_reg_ptr : var -> bool) (fresh_id : glob_decls -> var -> Ident.ident).

  Lemma make_referenceprog_globs (p p' : uprog) :
    makereference_prog is_reg_ptr fresh_id p = ok p' ->
      p.(p_globs) = p'.(p_globs).
  Proof.
    case: p p' => [???] [???]; t_xrbindP.
    by rewrite /makereference_prog; t_xrbindP.
  Qed.

  Context (p p' : uprog).
  Context (ev : unit).

 (* Hypothesis uniq_funname : uniq [seq x.1 | x <- p_funcs p]. *)

  Hypothesis Hp : makereference_prog is_reg_ptr fresh_id p = ok p'.

  (*Should be shown by assuming other hypotheses or admitted?*)
  Lemma eq_globs : p_globs p = p_globs p'.
  Proof.
   case : p Hp => /= p_funcs p_globs extra.
   rewrite /makereference_prog.
   (*But Let x in ...*)
   t_xrbindP => /=.
   by move => y _ <-.
  Qed.

  Definition get_sig n :=
   if get_fundef p.(p_funcs) n is Some fd then
     (fd.(f_params), fd.(f_res))
   else ([::], [::]).

  Let Pi s1 (i:instr) s2:=
    forall (X:Sv.t) c', update_i is_reg_ptr fresh_id p get_sig X i = ok c' ->
     Sv.Subset (Sv.union (read_I i) (write_I i)) X ->
     forall vm1, evm s1 =[X] vm1 ->
     exists vm2, [/\ evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pi_r s1 (i:instr_r) s2 :=
    forall ii, Pi s1 (MkI ii i) s2.

  Let Pc s1 (c:cmd) s2:=
    forall (X:Sv.t) c', update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok c' ->
     Sv.Subset (Sv.union (read_c c) (write_c c)) X ->
     forall vm1, evm s1 =[X] vm1 ->
     exists vm2, [/\ evm s2 =[X] vm2 &
        sem p' ev (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pfor (i:var_i) vs s1 c s2 :=
    forall X c',
    update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok c' ->
    Sv.Subset (Sv.add i (Sv.union (read_c c) (write_c c))) X ->
    forall vm1,  evm s1 =[X] vm1 ->
    exists vm2, [/\ evm s2 =[X] vm2  & 
      sem_for p' ev i vs (with_vm s1 vm1) c' (with_vm s2 vm2)].

  Let Pfun m fn vargs m' vres :=
    sem_call p' ev m fn vargs m' vres.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    move => s X.
    move => _ [<-].
    move => Hs vm1 Hvm1.
    exists vm1.
    split => //.
    by constructor.
    (*by move=> s X _ [<-] hs vm1 hvm1; exists vm1; split => //; constructor.*)
  Qed.

  Local Lemma Hcons : sem_Ind_cons p ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ hi _ hc X c'.
    rewrite /update_c /=.
    t_xrbindP.
    move => lc ci {}/hi hi cc hcc.
    (*Difference between <- and [<-]?*)
    (*move =>h ; rewrite - h ; clear h.*)
    (*[] is just case*)
    (*What is {}/hi again?*)
    (*{}h makes a clear of h*)
    move => <- <-.
    rewrite read_c_cons.
    rewrite write_c_cons.
    move => hsub vm1 hvm1.
    have [|vm2 [hvm2 hs2]]:= hi _ vm1 hvm1; first by SvD.fsetdec.
    have /hc : update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok (flatten cc).
    + by rewrite /update_c hcc.
    move=> /(_ _ vm2 hvm2) [|vm3 [hvm3 hs3]]; first by SvD.fsetdec.
    exists vm3; split => //=.
    apply: sem_app hs2 hs3.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
  Proof. by move=> ii i s1 s2 _ Hi X c' /Hi. Qed.

  Local Lemma Hassgn : sem_Ind_assgn p Pi_r.
  Proof.
    move=> s1 s2 x t ty e v v' he htr hw ii X c' [<-].
    rewrite read_Ii /write_I /= vrv_recE read_i_assgn => hsub vm1 hvm1.
    move: he.
    rewrite (read_e_eq_on _ (s:=Sv.empty) (vm' := vm1)); last first.
    + by apply: eq_onI hvm1; rewrite read_eE; SvD.fsetdec.
    rewrite eq_globs => he.
    
    (*I am supposed to use this, but can't figure out how: how can I get anything of type glob_decls?*)
    have ? := write_lval_eq_on.
    Print glob_decls.
    Print progT.
    Print with_vm.
  Admitted.

  Local Lemma Hopn : sem_Ind_opn p Pi_r.
  Proof.
    move => s1 s2 t o xs es He ii X c'.
    rewrite /update_i.
    move => [<-].
    rewrite read_Ii read_i_opn.
    rewrite /write_I /= vrvs_recE => hsub vm1 hvm1.
    Print update_c.
    (*hsub should be simplifiable*)
    (*have /hc : update_c (update_i is_reg_ptr fresh_id p get_sig X) c = ok (c').*)

    exists vm1.
    split.
  Admitted.

  Lemma write_Ii ii i : write_I (MkI ii i) = write_i i.
  Proof. by []. Qed.

  Local Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 He Hs Hc ii X c' /=.
    t_xrbindP => i_then i_thenE i_else i_elseE {c'}<-.
    rewrite !(read_Ii, write_Ii) !(read_i_if, write_i_if) => le_X.
    move=> vm1 eq_s1_vm1; case: (Hc X _ i_thenE _ vm1 eq_s1_vm1).
    + by SvD.fsetdec.
    move=> vm2 [eq_s2_vm2 sem_i_then]; exists vm2; split=> //.
    apply/sem_seq1/EmkI; apply: Eif_true => //.
    rewrite -(make_referenceprog_globs Hp) -He.
    rewrite -(@read_e_eq_on _ Sv.empty) // -/(read_e _).
    by apply: (eq_onI _ eq_s1_vm1); SvD.fsetdec.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
  Proof.
  Admitted.

  Local Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
  Proof.
  Admitted.

  Local Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
  Proof.
  Admitted.

  Local Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
  Proof.
  Admitted.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
  Admitted.

  Local Lemma Hfor_cons : sem_Ind_for_cons p ev Pc Pfor.
  Proof.
  Admitted.

  Local Lemma Hcall : sem_Ind_call p ev Pi_r Pfun.
  Proof.
  Admitted.

  Local Lemma Hproc : sem_Ind_proc p ev Pc Pfun.
  Proof.
  Admitted.

  Lemma makeReferenceArguments_callP f mem mem' va vr:
    sem_call p ev mem f va mem' vr ->
    sem_call p' ev mem f va mem' vr.
  Proof.
    move=> Hsem.
    apply (@sem_call_Ind _ _ _ p ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
               Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc
               mem f va mem' vr Hsem).
  Qed.

End Section.

  (*I should have something more specific than s1 and s2*)
  (*
  Lemma mkrefargs_c_incl s1 c s2 : Pc s1 c s2.
  Proof.
    move => X c' up vm1 eq.
    
  Qed.
  *)
