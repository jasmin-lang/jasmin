From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import expr label linear.
Require Import seq_extra compiler_util.
Require Import linear_util.
Notation map_cflprog_name := (map_cfprog_name_gen lfd_info).
Notation map_cflprog := (map_cfprog_gen lfd_info).

Section ASM_OP.
Context {asm_op} {asmop : asmOp asm_op}.

Lemma max_map_monotonic {A B} `{Cmp B} (f : A -> option B) s acc :
  exists2 acc', max_map f s (Some acc) = Some acc' & (acc <= acc')%CMP.
Proof.
  elim: s acc => [|a s ih] acc /=.
  + by exists acc.
  case: (f a) => [b|//].
  case: (ih (cmp_max b acc)) => acc' hmax hle.
  exists acc' => //.
  apply: cmp_le_trans hle.
  by apply cmp_max_geR.
Qed.

Lemma max_map_None {A B} `{Cmp B} (f : A -> option B) s acc :
  max_map f s acc = None ->
  all (fun x => match f x with | None => true | Some y => false end) s.
Proof.
  elim: s acc => //= a s ih acc.
  case: (f a) => [b|] /=; last by apply ih.
  by case:
    (max_map_monotonic f s (match acc with
                            | Some z => cmp_max b z
                            | None => b
                            end)) => _ -> _ //.
Qed.

Lemma max_map_Some {A B} `{Cmp B} (f : A -> option B) s m :
  max_map f s None = Some m ->
  all (fun x => match f x with | None => true | Some y => (y <= m)%CMP end) s.
Proof.
  elim: s None m => //= a s ih acc max.
  case: (f a) => [b|] /=; last by apply ih.
  move=> hmax.
  apply /andP; split; last by apply (ih _ _ hmax).
  move: hmax.
  case:
    (max_map_monotonic f s (match acc with
                            | Some z => cmp_max b z
                            | None => b
                            end)) => {}max -> hle [<-].
  case: acc hle => [acc|//] hle.
  apply: cmp_le_trans hle.
  by apply cmp_max_geL.
Qed.

Lemma max_lfd_lbl_None lfd lbl :
  max_lfd_lbl lfd = None ->
  ~ has (is_label lbl) (lfd_body lfd).
Proof.
  rewrite /max_lfd_lbl /max_lcmd_lbl.
  move=> /max_map_None hall hhas.
  have [i _ /andP [h1 h2]] := all_has hall hhas.
  move: h1 h2; rewrite /is_label.
  by case: (li_i i).
Qed.

Lemma max_lfd_lbl_Some lfd max_lbl lbl :
  max_lfd_lbl lfd = Some max_lbl ->
  has (is_label lbl) (lfd_body lfd) ->
  (lbl <= max_lbl)%CMP.
Proof.
  rewrite /max_lfd_lbl /max_lcmd_lbl => hmax hhas.
  have hall := max_map_Some hmax.
  have [i _ /andP [h1 h2]] := all_has hall hhas.
  move: h1 h2; rewrite /is_label.
  by case: (li_i i) => // lk l ? /eqP ->.
Qed.

Lemma next_lfd_lblP lfd : ~ has (is_label (next_lfd_lbl lfd)) (lfd_body lfd).
Proof.
  rewrite /next_lfd_lbl.
  case hmax: max_lfd_lbl => [max|].
  + move=> /(max_lfd_lbl_Some hmax).
    rewrite /cmp_le /gcmp /next_lbl.
    case: Pos.compare_spec => //; Lia.lia.
  by apply max_lfd_lbl_None.
Qed.

End ASM_OP.
