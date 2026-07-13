(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From Coq Require Import ZArith Uint63.
Require Import values sopn pseudo_operator expr psem compiler_util word.

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
  ty_expr (pd := Uptr) e = ok ty ->
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

Lemma check_global_declP (gd: glob_decl) : check_global_decl gd = ok tt -> (type_of_val (gv2val gd.2)) = (eval_atype (vtype gd.1)). 
Proof.
  rewrite /check_global_decl. case: gd => x [ws w | len a] /=.
- case: (vtype x) => [||| xw] //=. 
    by case: ifP => //= /negbFE /eqP ->.
  - case: (vtype x) => [|| ws xlen |] //=.
    by case: ifP => // /negbFE /Pos.eqb_eq ->.
Qed.

(* Lemma get8_noerrty s m i : WArray.get8 (s:=s) m i <> Error ErrType.
Proof.
  rewrite /WArray.get8 /assert. case: ifP; case: ifP => //=.
Qed. *)

Lemma mapM_errty {aT bT} (f : aT -> result error bT) :
  (forall a, f a <> Error ErrType) ->
  forall l, mapM f l <> Error ErrType.
Proof.
  move => Hf. induction l.
    - by [].
    - simpl. case Hfa: (f a); case HmapM: (mapM f l) => //=; intros.
      + rewrite <- HmapM. apply IHl.
      + specialize Hf with a. rewrite Hfa in Hf. congruence.
      + specialize Hf with a. rewrite Hfa in Hf. congruence.
Qed.

Lemma warray_get_noerrty len al aa ws a p : WArray.get (len:=len) al aa ws a p <> Error ErrType.
Proof.
  rewrite /WArray.get /read /assert. 
  case: ifP => _ //. case Hmap: (mapM _ _) => [ | e] //=. 
  move => heq.
  case: heq => ?; subst.
move: Hmap. apply: mapM_errty => k. move=> h; exact: (get_noerrty h).
Qed.

Lemma warray_get_sub_noerrty lena al aa ws a p : WArray.get_sub (lena:=lena) al aa ws a p <> Error ErrType.
Proof.
  rewrite /WArray.get_sub. 
  case: ifP => _ //. 
Qed.

Lemma read_noerrty al ws i s : read (emem s) al i ws <> Error ErrType.
Proof.
  rewrite /read /assert. 
  case: ifP => _ //. case Hmap: (mapM _ _) => [ | e] //=. 
  move => heq.
  case: heq => ?; subst.
  move: Hmap. apply: mapM_errty => k. move=> h; exact: (get_noerrty h).
Qed.

Lemma sem_warray_get_noerrty len gd s e al aa sz t tye : ty_expr (pd := Uptr) e = ok tye ->
                                      check_int tye = ok tt -> 
                                      sem_pexpr true gd s e <> Error ErrType ->
                                      (Let i := Let x := sem_pexpr true gd s e in to_int x in 
                                       Let w := WArray.get (len:=len) al aa sz t i in ok (Vword w)) <> Error ErrType. 
Proof. 
  intros Htye HtyeInt Hne.
  case He: (sem_pexpr true gd s e) => [xx | err] //=. case Hi: (to_int xx) => [i | err] //=. case Hw: (WArray.get al aa sz t i) => [w | err] //=.  
      { move => Herr. case: Herr => ?; subst. apply (warray_get_noerrty Hw). } 
      { unfold to_int in Hi. rewrite /check_int /check_type in HtyeInt. simpl in HtyeInt. case Htye2: (aint != tye); rewrite Htye2 in HtyeInt. discriminate. simpl in Htye2. move: Htye2 => /negbFE /eqP ?; subst. 
      pose proof (ty_expr_preserves Htye He) as Hsub. have Hxx : type_of_val xx = cint by move: Hsub => /subctypeE.
      apply type_of_valI in Hxx. destruct Hxx as [Hxxundef | Hxxint].
        - rewrite Hxxundef in Hi. by move: Hi => -[<-].
        - destruct Hxxint as [i Hxxint]. rewrite Hxxint in Hi. discriminate. } 
      move => Herr. case: Herr => ?; subst. apply (Hne He).
Qed.

Lemma sem_warray_get_sub_noerrty lena len gd s e aa sz t tye : ty_expr (pd := Uptr) e = ok tye ->
                                      check_int tye = ok tt -> 
                                      sem_pexpr true gd s e <> Error ErrType ->
                                      Let i := Let x := sem_pexpr true gd s e in to_int x in (Let t' := WArray.get_sub (lena:=lena) aa sz len t i in ok (Varr t')) <> Error ErrType.
Proof. 
  intros Htye HtyeInt Hne.
  case He: (sem_pexpr true gd s e) => [xx | err] //=. case Hi: (to_int xx) => [i | err] //=. case Hw: (WArray.get_sub aa sz len t i) => [w | err] //=.  
      { move => Herr. case: Herr => ?; subst. apply (warray_get_sub_noerrty Hw). } 
      { unfold to_int in Hi. rewrite /check_int /check_type in HtyeInt. simpl in HtyeInt. case Htye2: (aint != tye); rewrite Htye2 in HtyeInt. discriminate. simpl in Htye2. move: Htye2 => /negbFE /eqP ?; subst. 
      pose proof (ty_expr_preserves Htye He) as Hsub. have Hxx : type_of_val xx = cint by move: Hsub => /subctypeE.
      apply type_of_valI in Hxx. destruct Hxx as [Hxxundef | Hxxint].
        - rewrite Hxxundef in Hi. by move: Hi => -[<-].
        - destruct Hxxint as [i Hxxint]. rewrite Hxxint in Hi. discriminate. } 
      move => Herr. case: Herr => ?; subst. apply (Hne He).
Qed.

Lemma sem_read_noerrty tye gd s e ws al  : ty_expr (pd := Uptr) e = ok tye ->
                         check_ptr (pd := Uptr) tye = ok tt ->
                         sem_pexpr true gd s e <> Error ErrType ->
                         Let w2 := Let x := sem_pexpr true gd s e in to_pointer x in (Let w := read (emem s) al w2 ws in ok (Vword w)) <> Error ErrType.
Proof. 
  intros Htye HtyePtr Hne.
  case He: (sem_pexpr true gd s e) => [xx | err] //=. case Hi: (to_pointer xx) => [ptr | err] //=. case Hw: (read (emem s) al ptr ws) => [w | err] //=.  
      { move => Herr. case: Herr => ?; subst. apply (read_noerrty Hw). } 
      { unfold to_pointer in Hi. rewrite /check_ptr /check_type in HtyePtr. move: HtyePtr => //=. case: ifP => Htye2.  discriminate. move: Htye2 => /negbFE => Htye2. rewrite /subatype in Htye2. case tye eqn:E. discriminate. discriminate. discriminate. subst.
      (* have Heq : (type_of_val xx) = (eval_atype (aword w)) by admit. simpl in Heq.
      apply type_of_valI in Heq. destruct Heq as [Hxxundef | [ptr Hxxword]].
        - rewrite Hxxundef in Hi. by move: Hi => -[<-].
        - rewrite Hxxword in Hi. pose proof (truncate_word_errP Hi) as [Herr contra].
         move: Hi. rewrite truncate_word_le.
          + discriminate.
          + apply Htye2.  *)
      pose proof (ty_expr_preserves Htye He) as Hsub. move: Hsub => /subctypeE => //= [[sz [Hxx Hle]] Heq].
      apply type_of_valI in Hxx. destruct Hxx as [Hxxundef | [i Hxxword]].
        - rewrite Hxxundef in Hi. by move: Hi Heq => -[<-].
        - 
         rewrite Hxxword in Hi. pose proof (truncate_word_errP Hi) as [Herr contra]. move: Hi. rewrite truncate_word_le.
          + discriminate.
          + admit.
      }
      move => Herr. case: Herr => ?; subst. apply (Hne He).
Admitted.


(* elim: eqP eqxx getP_subctype*)
Lemma ty_expr_progress (gd : glob_decls) (s : estate) (e : pexpr) (ty : atype) :
    allM check_global_decl gd = ok tt ->
    ty_expr (pd := Uptr) e = ok ty ->
    sem_pexpr true gd s e <> Error ErrType.
Proof.
  move => /allMP Hgd. move: ty. induction e as [ | | | x | ??? x e IH | ??? x e IH | ? ws e IH | | | | ]; move => ty. 
  1-3: move => //=.
  { rewrite /= /ty_gvar /ty_var /vtype /v_var /gv /get_gvar /get_var /get_global /get_global_value => _ /=.
    case: (is_lvar x).
      - by case: (is_defined (evm s).[gv x]).
      - case E: (assoc gd (gv x)) => [p|] //.
        by move: (check_global_declP (Hgd _ (assoc_mem' E))) => /= /eqP ->.
  }
  { move => //=. rewrite /ty_get_set. t_xrbindP => tye Htye Htyx HtyeInt HtyWord. pose proof (IH _ Htye) as Hne. rewrite /on_arr_var.
    move: Htyx. rewrite /check_array /ty_gvar /get_gvar /ty_var /get_var /get_global /get_global_value => //=. 
    case Etyv: (vtype (gv x)) => [ | | ws n | w ] //= _. case E: (assoc gd (gv x)) => [p|] //.
      - move: (check_global_declP (Hgd _ (assoc_mem' E))) => /= ->. rewrite Etyv eqxx => //=. 
        case: (is_lvar x); case: (is_defined (evm s).[gv x]) => //=.

        { move: (Vm.getP (evm s) (v_var (gv x))) => //=. rewrite Etyv => //=. move=> Hcompat. apply compat_valEl in Hcompat. destruct Hcompat as [t Hcompat]. rewrite Hcompat. apply (sem_warray_get_noerrty Htye HtyeInt Hne). }

        1-2: apply assoc_mem' in E; apply Hgd in E; apply check_global_declP in E; simpl in E; rewrite Etyv in E; simpl in E; apply type_of_valI in E; destruct E as [a E]; rewrite E; apply (sem_warray_get_noerrty Htye HtyeInt Hne). 

      - case: (is_lvar x); case: (is_defined (evm s).[gv x]) => //=.  move: (Vm.getP (evm s) (v_var (gv x))) => //=. rewrite Etyv => //=. move=> Hcompat. apply compat_valEl in Hcompat. destruct Hcompat as [t Hcompat]. rewrite Hcompat. apply (sem_warray_get_noerrty Htye HtyeInt Hne). 
  }
  {
    move => //=. rewrite /ty_get_set_sub. t_xrbindP => tye Htye Htyx HtyeInt HtyArr. pose proof (IH _ Htye) as Hne. rewrite /on_arr_var.
    move: Htyx. rewrite /check_array /ty_gvar /get_gvar /ty_var /get_var /get_global /get_global_value => //=. 
    case Etyv: (vtype (gv x)) => [ | | ws n | w ] //= _. case E: (assoc gd (gv x)) => [p|] //.
      - move: (check_global_declP (Hgd _ (assoc_mem' E))) => /= ->. rewrite Etyv eqxx => //=. 
        case: (is_lvar x); case: (is_defined (evm s).[gv x]) => //=.

        { move: (Vm.getP (evm s) (v_var (gv x))) => //=. rewrite Etyv => //=. move=> Hcompat. apply compat_valEl in Hcompat. destruct Hcompat as [t Hcompat]. rewrite Hcompat. apply (sem_warray_get_sub_noerrty Htye HtyeInt Hne). }

        1-2: apply assoc_mem' in E; apply Hgd in E; apply check_global_declP in E; simpl in E; rewrite Etyv in E; simpl in E; apply type_of_valI in E; destruct E as [a E]; rewrite E; apply (sem_warray_get_sub_noerrty Htye HtyeInt Hne). 

      - case: (is_lvar x); case: (is_defined (evm s).[gv x]) => //=.  move: (Vm.getP (evm s) (v_var (gv x))) => //=. rewrite Etyv => //=. move=> Hcompat. apply compat_valEl in Hcompat. destruct Hcompat as [t Hcompat]. rewrite Hcompat. apply (sem_warray_get_sub_noerrty Htye HtyeInt Hne). 
  }
  {
    move => //=. rewrite /ty_load_store. t_xrbindP => tye Htye HtyePtr HtyWord. pose proof (IH _ Htye) as Hne. apply (sem_read_noerrty Htye HtyePtr Hne). 
  }
Admitted.

End PROOF.
