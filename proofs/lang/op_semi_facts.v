(* * Facts about the conditions of the operators.

   [op_semi.v] is in the extraction cone and contains definitions only; what
   is proved about the well-formed conditions ([safety_cond_wf],
   [safety_cond_total]), which need the conditions of the operators, is here. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Import op_semi safety_cond_facts values.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** Well-formed conditions                                             *)

Lemma safety_cond_wf_wt tin c : safety_cond_wf tin c -> safety_cond_wt tin c.
Proof. by move=> /andP []. Qed.

Lemma safety_cond_wf_total tin c : safety_cond_wf tin c -> safety_cond_total c.
Proof. by move=> /andP []. Qed.

Lemma all_safety_cond_wf_wt tin l : all (safety_cond_wf tin) l -> all (safety_cond_wt tin) l.
Proof. by apply: sub_all; apply: safety_cond_wf_wt. Qed.

Lemma all_safety_cond_wf_total tin l : all (safety_cond_wf tin) l -> all safety_cond_total l.
Proof. by apply: sub_all; apply: safety_cond_wf_total. Qed.

(* A well-typed total condition evaluates to a value on arguments of the
   announced types. *)
Lemma safety_cond_type_ok tin (vs : values) c t :
  List.Forall2 (fun (t : ctype) v => exists x : sem_t t, v = to_val x) tin vs ->
  safety_cond_total c ->
  safety_cond_type tin c = Some t ->
  exists x : sem_t t, sem_safety_cond vs c = ok (to_val x).
Proof.
move=> hall; elim: c t => /=.
1,2: by move=> x t _ [<-]; eexists.
+ move=> k t _; case: ifP => // hk [<-].
  by have [x hx] := Forall2_nth hall cbool undef_b hk; exists x; rewrite hx.
+ move=> o c ih t /andP [hto htot].
  case heq: (safety_cond_type tin c) => [t1|] //=; case: ifP => // hsub [<-].
  have [x1 ->] := ih _ htot heq.
  have [y hy] := of_val_subctype_ok x1 hsub.
  by rewrite /= hy /=; eexists.
move=> o c1 ih1 c2 ih2 t /and3P [hto ht1 ht2].
case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
case: ifP => // /andP [hsub1 hsub2] [<-].
have [x1 ->] := ih1 _ ht1 heq1; have [x2 ->] := ih2 _ ht2 heq2.
have [y1 hy1] := of_val_subctype_ok x1 hsub1.
have [y2 hy2] := of_val_subctype_ok x2 hsub2.
by rewrite /= hy1 /= hy2 /=; eexists.
Qed.
