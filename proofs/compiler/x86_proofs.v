(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import expr linear compiler_util low_memory.
(* ------- *) Require Import sem linear linear_sem x86 x86_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Variant dup_spec (P : Prop) :=
| Dup of P & P.

Lemma dup (P : Prop) : P -> dup_spec P.
Proof. by move=> ?; split. Qed.

(* -------------------------------------------------------------------- *)
Lemma drop_add {T : Type} (s : seq T) (n m : nat) :
  drop n (drop m s) = drop (n+m) s.
Proof.
elim: s n m => // x s ih [|n] [|m] //;
  by rewrite !(drop0, drop_cons, addn0, addnS).
Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_drop {T : Type} (s : seq T) (n m : nat) :
  n <= size s -> m <= size s -> drop n s = drop m s -> n = m.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Parameter rflags_of_lvm : vmap -> rflagmap.
Parameter regs_of_lvm : vmap -> regmap.

(* -------------------------------------------------------------------- *)
Inductive xs86_equiv (c : lcmd) (s : lstate) (xs : x86_state) :=
| XS86Equiv of
    s.(lmem) = xs.(xmem)
  & assemble_c c = ok xs.(xc)
  & assemble_c s.(lc) = ok (drop xs.(xip) xs.(xc))
  & xs.(xip) <= size xs.(xc)
  & rflags_of_lvm s.(lvm) = xs.(xrf)
  & regs_of_lvm s.(lvm) = xs.(xreg).

(* -------------------------------------------------------------------- *)
Lemma xs86_equiv_cons li1 li c s xs :
     s.(lc) = li1 :: li
  -> xs86_equiv c s xs
  -> xs86_equiv c
       {| lmem := s.(lmem); lvm := s.(lvm); lc := li |}
       (st_write_ip xs.(xip).+1 xs).
Proof.
case: s=> /= lm lvm _ -> [/= -> eqc eqd]; split => //.
+ move: eqd; rewrite /assemble_c /=; t_xrbindP.
  move=> a _ sa -> eqd; congr ok; move/(congr1 behead): eqd.
  by move=> /= ->; rewrite -addn1 addnC -drop_add drop1.
+ rewrite /st_write_ip /= ltnNge; apply/negP => le.
  move: eqd; rewrite drop_oversize // /assemble_c /=.
  by case: assemble_i => //= a; case: mapM.
Qed.

(* -------------------------------------------------------------------- *)
Lemma xread_ok ii v e op c s xs :
   xs86_equiv c s xs
-> oprd_of_pexpr ii e = ok op
-> sem_pexpr (to_estate s) e = ok v
-> read_oprd op xs = to_word v.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Lemma xeval_cond {ii e v c ct s xs} :
    xs86_equiv c s xs
 -> assemble_cond ii e = ok ct
 -> sem_pexpr (to_estate s) e = ok v
 -> eval_cond ct xs.(xrf) = to_bool v.
Proof.
move=> eqv; case: e => //.
+ move=> x /=; case: (rflag_of_var _) => rf /=.
  case: rf => // -[//<-] //=.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma xfind_label (c c' : lcmd) xc lbl :
     linear.find_label lbl c = Some c'
  -> assemble_c c = ok xc
  -> exists i,
       [/\ find_label lbl xc = ok i
         , i < size xc
         & assemble_c c' = ok (drop i.+1 xc)].
Proof.
elim: c c' xc => [|i c ih] c' xc //=; case: ifPn.
+ case: i => ii [] //= lbl'; rewrite /is_label /= => /eqP<-.
  case=> [<-] /=; rewrite /assemble_c /=; case: mapM => //=.
  move=> sa [<-]; exists 0; split=> //=; rewrite ?drop0 //.
  by rewrite /find_label /= eqxx ltnS.
move=> Nlbl eqc'; rewrite /assemble_c /=.
case E: assemble_i => [a|] //=; case E': mapM => [sa|] //=.
case=> <-; case/(ih _ sa): eqc' => // j [h1 h2 h3].
exists j.+1; split=> //; rewrite /find_label /=.
case: eqP => [|_]; last first.
  by move: h1; rewrite ltnS /find_label; case: ifP => // _ [->].
case: a E => //= pa E [paE]; move: Nlbl E; rewrite paE.
case: i => ii /=; rewrite /is_label /=; case=> //=.
+ by move=> lv _ p _; case: oprd_of_lval => //= ?; case: oprd_of_pexpr.
+ move=> lv op es _. admit.
+ by move=> lbl2 /eqP nq [[/esym]].
+ by move=> p l _; case: assemble_cond.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma assemble_i_ok (c : lcmd) (s1 s2 : lstate) (xs1 xs2 : x86_state) :
     xs86_equiv c s1 xs1
  -> xs86_equiv c s2 xs2
  -> lsem1 c s1 s2
  -> fetch_and_eval xs1 = ok xs2.
Proof.
move=> eqv1 eqv2 h; case: h eqv1 eqv2 => {s1 s2}.
+ case=> lm vm [|i li] //= s2 ii x tg e cs [-> <-] /= {cs}.
  rewrite /to_estate /=; t_xrbindP => v ok_v ok_s2.
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /=; t_xrbindP => a op1 ok_op1 op2 ok_op2.
  case=> ok_a tla ok_tla drop_xc _ xfE xrE eqv1 eqv2.
  rewrite /fetch_and_eval /=; have lt_ip: ip < size xc.
  * by rewrite leqNgt; apply/negP=> /drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth a) // -{}ok_a => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /eval_MOV /=; move/(xs86_equiv_cons _): eqv1 => /=.
  move/(_ _ _ (erefl _)) => /= /xread_ok /(_ ok_op2 ok_v) /=.
  rewrite /st_write_ip /= => ->. admit.
+ admit.
+ case=> lv vm [|_ _] //= ii lbl cs [-> ->].
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /=; t_xrbindP => sa ok_sa drop_xc le_ip_c <- <-.
  move=> eqv1 eqv2; rewrite /fetch_and_eval /=; have lt_ip: ip < size xc.
  * by rewrite leqNgt; apply/negP=> /drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth (LABEL lbl)) // => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  congr ok; rewrite /st_write_ip /=; move: eqv2; rewrite /setc /=.
  case=> /= ->; rewrite ok_xc /assemble_c ok_sa => -[eq_xc] ok_sa2.
  move=> le_ip2_c -> ->; move: ok_sa2; rewrite tlaE => -[].
  rewrite eq_xc; move/inj_drop=> ->//; first by rewrite -eq_xc.
  by case: {+}xs2.
+ case=> [lv vm] [|_ _] //= ii lbl cs csf [-> ->] /=.
  move=> ok_csf; case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /setc /=; t_xrbindP => tla ok_tla drop_xc.
  move=> le_ip <- <- eqv1 eqv2; rewrite /fetch_and_eval /=.
  have lt_ip: ip < size xc; first (rewrite leqNgt; apply/negP).
  * by move/drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth (JMP lbl)) // => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /eval_JMP /st_write_ip /=.
  case: (xfind_label ok_csf ok_xc) => ip' [-> lt_ip' ok_tl] /=; congr ok.
  case: xs2 eqv2 => xm2 xr2 xf2 xc2 ip2 [/= ->].
  rewrite ok_xc => -[<-] ok_drop le_ip2 <- <-; f_equal.
  by move: ok_drop; rewrite ok_tl => -[] => /inj_drop -> //; apply/ltnW. 
+ move=> ii [lv vm] [|i li] //= e lbl cst csf [-> ->] {li} /=.
  rewrite /to_estate /=; t_xrbindP=> v ok_v vl_v ok_csf.
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /setc /=; t_xrbindP=> a ct ok_ct [ok_a] /=.
  move=> tla ok_tla drop_xc le_ip <- <- eqv1 eqv2; rewrite /fetch_and_eval /=.
  have lt_ip: ip < size xc; first (rewrite leqNgt; apply/negP).
  * by move/drop_oversize; rewrite -drop_xc.
  move: drop_xc; rewrite (drop_nth a) // -{}ok_a => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /= /eval_Jcc /= /eval_JMP.
  rewrite (xeval_cond eqv1 ok_ct ok_v) vl_v /= /st_write_ip /=.
  case: (xfind_label ok_csf ok_xc) => ip' [-> lt_ip' ok_tl] /=; congr ok.
  case: xs2 eqv2 => xm2 xr2 xf2 xc2 ip2 [/= ->].
  rewrite ok_xc => -[<-] ok_drop le_ip2 <- <-; f_equal.
  by move: ok_drop; rewrite ok_tl => -[] => /inj_drop -> //; apply/ltnW. 
+ move=> ii [lv vm] [|i li] //= e lbl cs [-> ->] {li} /=.
  rewrite /to_estate /=; t_xrbindP => v ok_v ok_bv; rewrite /setc /=.
  case: xs1 => xm xr xf xc ip -/dup[] [/= <-] ok_xc.
  rewrite /assemble_c /setc /=; t_xrbindP=> a ct ok_ct [ok_a] /=.
  move=> tla ok_tla drop_xc le_ip <- <- eqv1 eqv2; rewrite /fetch_and_eval /=.
  have lt_ip: ip < size xc; first (rewrite leqNgt; apply/negP).
  * by move/drop_oversize; rewrite -drop_xc. 
  move: drop_xc; rewrite (drop_nth a) // -{}ok_a => -[h tlaE].
  have {h} := congr1 some h; rewrite -(nth_map _ None) // => <- /=.
  rewrite /st_write_ip /= /eval_Jcc /= /eval_JMP.
  rewrite (xeval_cond eqv1 ok_ct ok_v) ok_bv /= /st_write_ip /=.
  case: eqv2 => /= ->; rewrite ok_xc /assemble_c ok_tla.
  case=> [eq_xc] [tlaE2] le_ip2 -> ->; congr ok.
  move: tlaE2; rewrite tlaE eq_xc => /inj_drop -> //.
  + by rewrite -eq_xc. + by case: {+}xs2.
Admitted.









 


  











