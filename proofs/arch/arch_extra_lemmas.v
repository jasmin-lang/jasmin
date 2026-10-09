From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import xseq strings utils var type values sopn expr fexpr arch_decl.
Require Import compiler_util.
Require Import arch_extra.
Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)

Section ARCH.
Context `{arch : arch_decl} {atoI : arch_toIdent}.

Lemma to_var_reg_neq_regx (r : reg_t) (x : regx_t) :
  to_var r <> to_var x.
Proof. rewrite /to_var => -[]; apply: inj_toI_reg_regx. Qed.

Lemma to_var_reg_neq_xreg (r : reg_t) (x : xreg_t) :
  to_var r <> to_var x.
Proof. move=> [] hsize _; apply/eqP/reg_size_neq_xreg_size:hsize. Qed.

Lemma to_var_regx_neq_xreg (r : regx_t) (x : xreg_t) :
  to_var r <> to_var x.
Proof. move=> [] hsize _; apply/eqP/reg_size_neq_xreg_size:hsize. Qed.

End ARCH.

Section AsmOpI.
Context `{asm_e : asm_extra}.

Lemma computational_eq_refl n (e : n = n) : computational_eq e = erefl.
Proof.
  by apply (Eqdep_dec.UIP_dec (List.list_eq_dec ctype_eqb_OK_sumbool)).
Qed.

End AsmOpI.
