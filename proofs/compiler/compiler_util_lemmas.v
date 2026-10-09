From Coq Require Import ZArith Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Require Import expr fexpr.
Require Import compiler_util.
Local Unset Elimination Schemes.
Notation pp_s    := PPEstring.
Notation pp_z    := PPEz.
Notation pp_var  := PPEvar.
Notation pp_e    := PPEexpr.
Notation pp_re   := PPErexpr.
Notation pp_fe   := PPEfexpr.
Notation pp_fn   := PPEfunname.
Notation pp_lv   := PPElval.

Section ASM_OP.
Context `{asmop:asmOp}.
Context {pT: progT}.

Lemma get_map_prog_name F p fn :
  get_fundef (p_funcs (map_prog_name F p)) fn =
  ssrfun.omap (F fn) (get_fundef (p_funcs p) fn).
Proof.
  rewrite /get_fundef /map_prog_name /=.
  by elim: p_funcs => // -[fn' fd] pfuns /= ->;case:eqP => [-> | ].
Qed.

Lemma get_map_prog F p fn :
  get_fundef (p_funcs (map_prog F p)) fn = ssrfun.omap F (get_fundef (p_funcs p) fn).
Proof. apply: get_map_prog_name. Qed.

End ASM_OP.
