(* * Facts about the instruction descriptors of an architecture.

   [arch_decl.v] is in the extraction cone and contains definitions only; what
   is proved about the zero-extension of a descriptor is here. *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import Utf8.

Require Import arch_decl safety_cond_facts sopn_semi sopn_semi_facts values.

Section DECL.

Context {reg regx xreg rflag cond} `{arch : arch_decl reg regx xreg rflag cond}.
Context `{asm_op_d : asm_op_decl}.

(* Zero-extension commutes with the filtering of the undefined outputs:
   [filter_ot] is the identity on the non-boolean components and
   [wextend_size] is the identity on the boolean ones. *)
Lemma extend_filter_tuple ws tout mask (t : sem_ltuple_t tout) :
  extend_tuple ws (filter_tuple (map eval_ltype tout) mask t)
  = filter_tuple (map eval_ltype (map (extend_size ws) tout)) mask (extend_tuple_t ws t).
Proof.
  elim: tout mask t => // t1 tout hrec mask t.
  case: tout hrec t => [ | t2 tout] hrec t.
  + by case: t1 t => //= ws1 w; case: (ws1 <= ws)%CMP.
  case: t => x ts /=; congr pair.
  + by case: t1 x => //= ws1 w; case: (ws1 <= ws)%CMP.
  apply hrec.
Qed.

Lemma apply_lprod_mk_semi_aux {T T' T''} (P : values.values -> T -> exec T')
    (g : exec T' -> exec T'') vs tin (f : sem_prod tin T) :
  sem_prod_eq tin (apply_lprod g (mk_semi_aux P vs tin f))
                  (mk_semi_aux (fun vs t => g (P vs t)) vs tin f).
Proof. by elim: tin vs f => //= t tin hrec vs f v; apply hrec. Qed.

Lemma mk_semi_aux_apply_lprod {T T' T''} (Q : values.values -> T'' -> exec T')
    (h : T -> T'') vs tin (f : sem_prod tin T) :
  sem_prod_eq tin (mk_semi_aux Q vs tin (apply_lprod h f))
                  (mk_semi_aux (fun vs t => Q vs (h t)) vs tin f).
Proof. by elim: tin vs f => //= t tin hrec vs f v; apply hrec. Qed.

(* Extending the generic construction is the generic construction of the
   extended total semantics. *)
Lemma mk_semi_extend tin tout ws safe err init (f : sem_lprod tin (sem_ltuple_t tout)) :
  sem_prod_eq (map eval_ltype tin)
    (extend_sem ws (mk_semi safe err init f))
    (mk_semi safe err init (extend_sem_t ws f)).
Proof.
  rewrite /extend_sem /extend_sem_t /mk_semi.
  apply: sem_prod_eq_trans; first by apply: apply_lprod_mk_semi_aux.
  apply: sem_prod_eq_trans; last by apply: sem_prod_eq_sym; apply: mk_semi_aux_apply_lprod.
  apply: mk_semi_aux_eq => vs t.
  by case: check_safe => //= _; rewrite extend_filter_tuple.
Qed.

End DECL.
