(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From Coq Require Import ZArith Uint63.
Require Import values sopn pseudo_operator expr psem compiler_util.

Require Export typing_new.
Import E.

Local Open Scope seq_scope.
Section PROOF.

Context `{asmop : asmOp}.
Context {pd : wsize}.
Context {wsw : WithSubWord}.
Context {syscall_state : Type}.
Context {ep : EstateParams syscall_state}.
Context {spp : SemPexprParams}.

Lemma canonical_value (v : value) :
  is_defined v -> 
  match type_of_val v with
    | cbool => exists b : bool , v = Vbool b
    | cint => exists z : Z, v = Vint z
    | carr len => exists a : WArray.array len, v = Varr a
    | cword ws => exists w : word ws, v = Vword w
    end.
Proof.
   case : v => [b | z | len a | ws w | t H] //= _ ;
     [exists b | exists z | exists a | exists w]; reflexivity.
Qed.

Lemma truncate_val_subctype (ty : atype) (v0 : value) (v : value) :
  truncate_val (eval_atype ty) v0 = ok v ->
  subctype (type_of_val v) (eval_atype ty).
Proof.
  rewrite /truncate_val. t_xrbindP => vt Hof <-.
  case: ty vt Hof => //=.
Qed.

Lemma ty_expr_preserves (gd : glob_decls) (s : estate) e ty v :
  ty_expr (pd := pd) e = ok ty ->
  sem_pexpr true gd s e = ok v ->
  subctype (type_of_val v) (eval_atype ty).
Proof.
  destruct e as [? | ? | ?? | ? | ????? | ????? | ??? | op ? | op ?? | op ? | ????]. 
  1-3: by move => [<-] [<-].
  { move => [<-] /= . exact: type_of_get_gvar_sub. }
  { rewrite /= /ty_get_set.
   t_xrbindP => _ _ _ _ ?. subst ty.
   rewrite /on_arr_var. t_xrbindP. case=> //. by t_xrbindP => _ _ _ _ _ _ _ z1 _ <-. }
  { rewrite /= /ty_get_set_sub. t_xrbindP => _ _ _ _ ?. subst ty. rewrite /on_arr_var. t_xrbindP. case => //. t_xrbindP => _ _ _ _ _ _ _ z1 _ <-. by []. }
  { rewrite /= /ty_load_store. t_xrbindP => _ _ _ ? _ _ _ _ ? _ ?. by subst ty v. }
  { rewrite /= /type_of_op1 /sem_sop1.   
    by case: op => [ | | | | | | [] | ? []] //=; t_xrbindP => *; subst. }
  { rewrite /= /sem_sop2 /type_of_op2.
    by case: op => 
    [ | | | [] | [] | [] | ? [] | ? [] | | | | | [] | [] | | | [] | [] | | | 
    | | | | | | | | ?? [] ] //=;t_xrbindP => *; subst.    }
  { rewrite /= /sem_opN /type_of_opN. 
    by case: op => [ ?? | ? | ?] //=; t_xrbindP => *; subst. }
  { rewrite /= /check_expr. t_xrbindP => te1 _ _ te2 _ _ te3 _ _ ? valE1Bool valE1 _ HvalE1Bool valE2 valE2ty _ HvalE2ty valE3 valE3ty _ HvalE3ty ?. apply to_boolI in HvalE1Bool. subst. destruct valE1Bool.
  { exact: truncate_val_subctype HvalE2ty. }
  { exact: truncate_val_subctype HvalE3ty. } } 
Qed.

Lemma ty_expr_progress (gd : glob_decls) (s : estate) (e : pexpr) (ty : atype) :
    ty_expr (pd := pd) e = ok ty ->
    sem_pexpr true gd s e <> Error ErrType.
Proof.
  destruct e.
  { move => //=. }
  { move => //=. }
  { move => //=. }
  { move => //=. rewrite /ty_gvar /ty_var /vtype /v_var /gv. case: g => -[[vt vn] vi] sc. rewrite /get_gvar /get_var /get_global /get_global_value. admit. }
Admitted.

End PROOF.
