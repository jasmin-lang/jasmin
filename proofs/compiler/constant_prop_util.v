(* ** Imports and settings *)
From CoqWord Require Import ssrZ.
Require Import expr ZArith psem.
Require Import dead_code.
Require Export low_memory.
Require Export constant_prop.
Import all_ssreflect all_algebra.
Import Utf8.
Import oseq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.
Local Open Scope Z_scope.

Section SEM_PEXPR_E.

Context (gd: glob_decls).

Fixpoint sem_pexpr_e (s:estate) (e : pexpr) : exec (value * leak_e_tree) :=
  match e with
  | Pconst z => ok (Vint z, LEmpty)
  | Pbool b  => ok (Vbool b, LEmpty)
  | Parr_init n => ok (Varr (WArray.empty n), LEmpty)
  | Pvar x => Let v := get_var s.(evm) x in 
              ok (v, LEmpty)
  | Pglobal g => Let v := get_global gd g in 
                 ok (v, LEmpty)
  | Pget ws x e =>
      Let (n, t) := s.[x] in
      Let vl := sem_pexpr_e s e in 
      Let i := to_int vl.1 in 
      Let w := WArray.get ws t i in
      ok ((Vword w), LSub [ :: vl.2 ; (LIdx i)])
  | Pload sz x e =>
    Let w1 := get_var s.(evm) x >>= to_pointer in
    Let vl2 := sem_pexpr_e s e in 
    Let w2 := to_pointer vl2.1 in
    let adr := (w1 + w2)%R in 
    Let w  := read_mem s.(emem) adr sz in
    ok (@to_val (sword sz) w, LSub [ :: vl2.2;  (LAdr adr)])
  | Papp1 o e1 =>
    Let vl := sem_pexpr_e s e1 in
    Let v := sem_sop1 o vl.1 in 
    ok (v, vl.2)
  | Papp2 o e1 e2 =>
    Let vl1 := sem_pexpr_e s e1 in
    Let vl2 := sem_pexpr_e s e2 in
    Let v := sem_sop2 o vl1.1 vl2.1 in
    ok (v, LSub [:: vl1.2; vl2.2])
  | PappN op es =>
    Let vs := mapM (sem_pexpr_e s) es in
    Let v := sem_opN op (unzip1 vs) in
    ok (v, LSub (unzip2 vs))
  | Pif t e e1 e2 =>
    Let vl := sem_pexpr_e s e in
    Let b := to_bool vl.1in
    Let vl1 := sem_pexpr_e s e1 in
    Let vl2 := sem_pexpr_e s e2 in
    Let v1 := truncate_val t vl1.1 in
    Let v2 := truncate_val t vl2.1 in
    ok (if b then v1 else v2, LSub [:: vl.2 ; vl1.2; vl2.2])
  end.

Definition sem_pexprs_e s es :=
  Let vls := mapM (sem_pexpr_e s) es in
  ok (unzip1 vls, LSub (unzip2 vls)).

Definition write_lval_e (l:lval) (v:value) (s:estate) : exec (estate * leak_e_tree) :=
  match l with
  | Lnone _ ty => Let x := write_none s ty v in ok (x, LEmpty)
  | Lvar x => Let v' := write_var x v s in ok(v', LEmpty)
  | Lmem sz x e =>
    Let vx := get_var (evm s) x >>= to_pointer in
    Let vl := sem_pexpr_e s e in 
    Let ve := to_pointer vl.1 in
    let p := (vx + ve)%R in
    Let w := to_word sz v in
    Let m :=  write_mem s.(emem) p sz w in
    ok ({| emem := m;  evm := s.(evm) |}, LSub [:: vl.2; (LAdr p)])
  | Laset ws x i =>
    Let (n,t) := s.[x] in
    Let vl := sem_pexpr_e s i in 
    Let i := to_int vl.1 in
    Let v := to_word ws v in
    Let t := WArray.set t i v in
    Let vm := set_var s.(evm) x (@to_val (sarr n) t) in
    ok ({| emem := s.(emem); evm := vm |}, LSub [:: vl.2; (LIdx i)])
  end.

Definition write_lvals_e (s:estate) xs vs :=
   fold2 ErrType (fun l v sl => Let sl' := write_lval_e l v sl.1 in ok (sl'.1, LSub [:: sl.2 ; sl'.2]))
      xs vs (s, LEmpty).


End SEM_PEXPR_E.

Section Sem_e_Leakages_proof.

Context (gd: glob_decls).

Context (s:estate).

Definition flatten_exec (p : exec (value * leak_e_tree)) := 
Let v := p in 
ok (v.1, lest_to_les v.2).

Definition flatten_estate (p : exec (estate * leak_e_tree)) := 
Let v := p in 
ok (v.1, lest_to_les v.2).

Definition flatten_range (p : exec (seq Z * leak_e_tree)) := 
Let v := p in 
ok (v.1, lest_to_les v.2).

Fixpoint vlest_to_vles (p : seq (value * leak_e_tree)) := 
match p with 
| [::] => ([::])
| x :: xl => ((x.1, lest_to_les x.2) :: vlest_to_vles xl)
end.

Definition flatten_execs (p : exec (seq (value * leak_e_tree))) := 
Let v := p in 
ok (vlest_to_vles v).


Let P e : Prop := forall v, sem_pexpr_e gd s e = ok v -> 
            sem_pexpr gd s e = ok (v.1, lest_to_les v.2).

Let Q es : Prop := forall vs, mapM (sem_pexpr_e gd s) es = ok vs ->
           mapM (sem_pexpr gd s) es = ok (zip (unzip1 vs) (map (lest_to_les) (unzip2 vs))).

Let Q'' es : Prop := forall vs, sem_pexprs_e gd s es = ok vs ->
           sem_pexprs gd s es = ok (vs.1, lest_to_les vs.2).

  Lemma sem_pexpr_e_sim : (∀ e, P e) ∧ (∀ es, Q es).
  Proof.
  apply: pexprs_ind_pair ; split ; subst P Q => //=.
  + move=> vs He. by case: He => <- /=.
  + move=> e H es Hm vs. t_xrbindP.
    move=> [yv yl] Hs ho Hm' <- /=. move: (H (yv, yl) Hs) => -> /=.
    by move: (Hm ho Hm') => -> /=.
  + move=> z [v l] He /=. by case: He => -> <- /=.
  + move=> b [v l] He /=. by case: He => -> <- /=.
  + move=> z [v l] He /=. by case: He => -> <- /=.
  + t_xrbindP. move=> v [hv hl] y -> He /=. by case: He => -> <- /=.
  + t_xrbindP. move=> h [hv hl] y -> He /=. by case: He => -> <- /=.
  + move=> sz x e H [v l] /=. apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => Hg.
    t_xrbindP. move=> [yv yl] Hs z Hi w Ha <- <- /=.
    move: (H (yv, yl) Hs) => -> /=. rewrite Hi /=. rewrite Hg /=.
    rewrite Ha /=. rewrite /lests_to_les /=. by rewrite cats1.
  + move=> sz x e H [v l] /=. t_xrbindP.
    move=> y h -> /= -> /= [hv hl] Hs h' Hp' /= w Hr He <- /=.
    move: (H (hv, hl) Hs) => -> /=. rewrite Hp' /=. rewrite Hr /=.
    rewrite He /=. rewrite /lests_to_les /=.
    by rewrite cats1.
  + move=> op e Hs. t_xrbindP.
    move=> [hv hl] [yv yl] Hse h1 Hop He. move: (Hs (yv, yl) Hse) => -> /=.
    rewrite Hop /=. case: He => -> <- /=. by rewrite /lests_to_les /=.
  + move=> op e1 H1 e2 H2 [v l]. t_xrbindP.
    move=> [yv yl] Hs [hv hl] Hs' v' Hop <- <- /=.
    move: (H1 (yv, yl) Hs) => -> /=. move: (H2 (hv, hl) Hs') => -> /=.
    rewrite Hop /=. rewrite /lests_to_les /=. by rewrite cats0.
  + move=> op es Hes. t_xrbindP. move=> [yv yl] ys Hm. move=> h1 Ho.
    move=> [] Hh Hl. move: (Hes ys Hm) => Hm'. rewrite Hm' /=.
    assert ((unzip1
        (zip (unzip1 ys) [seq lest_to_les i | i <- unzip2 ys])) = unzip1 ys).
    apply unzip1_zip. elim: (ys) => //= x s. rewrite H /=. rewrite Ho /=.
    assert ((unzip2
       (zip (unzip1 ys)
          [seq lest_to_les i | i <- unzip2 ys])) = [seq lest_to_les i | i <- unzip2 ys]).
    apply unzip2_zip. elim: (ys) => //= x s. rewrite H0 Hh -Hl /=. by rewrite /lests_to_les /=. 
  move=> t e H e1 H1 e2 H2 [v l]. t_xrbindP.
  move=> [yv yl] Hs b Hb [hv hl] He1 [hv' hl'] He2 he1 Hhe1 he2 Hhe2 He <- /=.
  move: (H (yv, yl) Hs) => -> /=.
  move: (H1 (hv, hl) He1) => -> /=.
  move: (H2 (hv', hl') He2) => -> /=.
  rewrite Hb /=. rewrite Hhe1 /=. rewrite Hhe2 /=. rewrite He /=.
  rewrite /lests_to_les /=. by rewrite cats0.
  Qed.

  Lemma sem_pexpr_e_sim' : (∀ e, P e) ∧ (∀ es, Q'' es).
  Proof.
  rewrite /Q''. rewrite /sem_pexprs. rewrite /sem_pexprs_e.
  move:  sem_pexpr_e_sim => [] H1 H2. rewrite /Q in H2.
  split; auto. move=> es vs. t_xrbindP => y Hm <-. move: (H2 es y) => H1'. 
  move: (H1' Hm) => H. rewrite H /=.
  assert ((unzip1
     (zip (unzip1 y) [seq lest_to_les i | i <- unzip2 y])) = unzip1 y).
  apply unzip1_zip. elim: (y) => //= x s. rewrite H0 /=.
  assert ((unzip2
       (zip (unzip1 y)
          [seq lest_to_les i | i <- unzip2 y])) = [seq lest_to_les i | i <- unzip2 y]).
    apply unzip2_zip. elim: (y) => //= x s. by rewrite H3 /lests_to_les /=.
  Qed.

End Sem_e_Leakages_proof.

Definition const_prop_e_esP_sem_pexpr_e gd s e v:=
  (@sem_pexpr_e_sim gd s).1 e v.

Definition const_prop_e_esP_sem_pexprs_e gd s es v:=
  (@sem_pexpr_e_sim gd s).2 es v.

Definition const_prop_e_esP_sem_pexprs_e' gd s es v:=
  (@sem_pexpr_e_sim' gd s).2 es v.

  Lemma sem_pexpr_e_to_sem_pexpr gd s e v l':
  sem_pexpr gd s e = ok (v, l') ->
  exists l, l' = lest_to_les l /\ sem_pexpr_e gd s e = ok (v, l).
  Proof.
  elim: e v l'.
  + move=> z v l' [] <- <- /=. exists LEmpty. split; auto.
  + move=> b v l' [] <- <- /=. exists LEmpty. split; auto.
  + move=> n v l' [] <- <- /=. exists LEmpty. split; auto.
  + move=> x v l'. rewrite /sem_pexpr. t_xrbindP.
    move=> y Hg <- <- /=. rewrite Hg /=. exists LEmpty. split; auto.
  + move=> g v l. rewrite /sem_pexpr. t_xrbindP.
    move=> y Hg <- <- /=. rewrite Hg /=. exists LEmpty. split; auto.
  + move=> sz x e He v l' /=. apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => Hg.
    t_xrbindP. move=> [yv yl] He' z Hi w Ha Hv Hl /=.
    move: (He yv yl He') => [] l [] Hs Hs'. rewrite Hs' /=.
    rewrite Hg /=. rewrite Hi /=. rewrite Ha /=. 
    exists (LSub [:: l; (LIdx z)]). split. rewrite -Hl /=.
    rewrite Hs /=. rewrite /lests_to_les /=. by rewrite cats1.
    by rewrite -Hv.
  + move=> sz x e He /=. t_xrbindP.
    move=> v l y v1 Hg Hp [yv yl] He' h6 Hp' h8 Hr Hv Hl /=.
    move: (He yv yl He') => [] l' [] Hs Hs'. rewrite Hg /=.
    rewrite Hp /=. rewrite Hs' /=. rewrite Hp' /=. rewrite Hr /=.
    exists (LSub [:: l' ; (LAdr (y + h6))]). split. rewrite -Hl /=.
    rewrite /lests_to_les /=. rewrite -Hs /=. by rewrite cats1.
    by rewrite -Hv.
  + move=> op e He /=. t_xrbindP.
    move=> v l [yv yl] He' h2 Ho Hv Hl.
    move: (He yv yl He') => [] l' [] Hs Hs'. rewrite Hs' /=.
    rewrite Ho /=. exists l'. split.
    rewrite -Hl /=. rewrite Hs /=. by rewrite /lests_to_les /=.
    by rewrite Hv.
  + move=> op e1 He1 e2 He2 /=. t_xrbindP.
    move=> v l' [yv yl] He1' [yv' yl'] He2' v' Ho Hv Hl /=.
    move: (He1 yv yl He1') => [] l1 [] Hs1 Hs1'. rewrite Hs1' /=.
    move: (He2 yv' yl' He2') => [] l2 [] Hs2 Hs2'. rewrite Hs2' /=.
    exists (LSub [:: l1; l2]). split.
    rewrite -Hl /=. rewrite Hs1 Hs2 /=. rewrite /lests_to_les /=. by rewrite cats0.
    rewrite Ho /=. by rewrite Hv.
  + move=> op es He /=. t_xrbindP. move: (const_prop_e_esP_sem_pexprs_e) => H h1 h0 y0 Hm.
    move: (H gd s es) => H1. move=> h2 Ho <- /= <- /=.
    move: (const_prop_e_esP_sem_pexpr_e)=> H2. 
    admit.
  + move=> t e He e1 He1 e2 He2 /=. t_xrbindP.
    move=> h h0 [yv yl] He' b Hb [yv' yl'] He1' [yv'' yl''] He2' h8 Ht h9 Ht' Hv Hl.
    move: (He yv yl He') => [] x [] Hs Hs'. rewrite Hs' /=.
    rewrite Hb /=. move: (He1 yv' yl' He1') => [] x0 [] Hs1 Hs1'. rewrite Hs1' /=.
    move: (He2 yv'' yl'' He2') => [] x0' [] Hs2 Hs2'. rewrite Hs2' /=. 
    rewrite Ht /=. rewrite Ht' /=. rewrite Hv /=.
    exists (LSub [:: x; x0; x0']). split. rewrite -Hl /=. rewrite Hs Hs1 Hs2 /=.
    rewrite /lests_to_les /=. by rewrite cats0. auto.
  Admitted.

  Lemma sem_pexprs_to_sem_pexprs_e s gd es vs:
    mapM (sem_pexpr gd s) es = ok vs ->
    exists vs', vs =  (zip (unzip1 vs') (map (lest_to_les) (unzip2 vs'))) /\
                mapM (sem_pexpr_e gd s) es = ok vs'.
  Proof.
    elim: es vs.
    - move=> vs Hm. exists [::]. rewrite /=. case: Hm.
      move=> ->. by split.
    - move=> a l vs Hm Hms.
  Admitted.

    Lemma sem_pexprs_to_sem_pexprs_e' s gd es vs:
    sem_pexprs gd s es = ok vs ->
    exists vs', vs.1 = vs'.1 /\ vs.2 = (lest_to_les vs'.2) /\
                sem_pexprs_e gd s es = ok vs'.
  Proof.
    rewrite /sem_pexprs. rewrite /sem_pexprs_e.
    t_xrbindP. move=> y Hm Hv. move: (sem_pexprs_to_sem_pexprs_e).
    move=> H. move: (H s gd es y Hm) => [] x [] Hv' Hl'. rewrite Hl' /=.
    exists  (unzip1 x, LSub (unzip2 x)). rewrite /=. rewrite -Hv /=. split.
    rewrite Hv' /=. apply unzip1_zip. elim: (x) => //= x s. split.
    rewrite /lests_to_les /=. rewrite Hv' /=.
    assert ((unzip2
       (zip (unzip1 x)
          [seq lest_to_les i | i <- unzip2 x])) = [seq lest_to_les i | i <- unzip2 x]).
    apply unzip2_zip. elim: (x) => //= x s. by rewrite H0 /=. auto.
  Qed.
                                                          
 Lemma write_lval_cp gd s1 x v s2 l:
  write_lval_e gd x v s1 = ok (s2, l) ->
  write_lval gd x v s1 = ok (s2, lest_to_les l).
  Proof.
  case : x => /=.
  - move=> _ ty. rewrite /write_none. t_xrbindP.
    move=> y H <- <- /=. by rewrite H /=.
  - move=> x. rewrite /write_var. t_xrbindP.
    move=> y h Hs Hy He <- /=. rewrite Hs /=. rewrite -Hy in He.
    by rewrite -He /=.
  - move=> sz x e. t_xrbindP.
    move=> y h -> /= -> /= [v' l'] He h4 Hw h8 Hw' m Hm <- <- /=.
    move: (const_prop_e_esP_sem_pexpr_e). move=> H.
    move: (H gd s1 e (v', l') He) => -> /=. rewrite Hw /=.
    rewrite Hw' /=. rewrite Hm /=. rewrite /lests_to_les /=.
    by rewrite cats1.
  - move=> sz x e /=. apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => Hg.
    t_xrbindP. move=> [yv yl] Hs z Hi w Hw a Ha h6 Hs' <- <- /=.
    rewrite Hg /=. move: (const_prop_e_esP_sem_pexpr_e). move=> H.
    move: (H gd s1 e (yv, yl) Hs) => -> /=.
    rewrite Hi /=. rewrite Hw /=. rewrite Ha /=. rewrite Hs' /=.
    rewrite /lests_to_les /=. by rewrite cats1.
  Qed.

  Lemma write_lvals_cp gd s1 xs vs s2 l:
  write_lvals_e gd s1 xs vs = ok (s2, l) ->
  write_lvals gd s1 xs vs = ok (s2, lest_to_les l).
  Proof.
  rewrite /write_lvals. rewrite /write_lvals_e.
  elim: xs vs s1 [::] l s2 => [|x xs Hrec] [|v vs] s1 lw0 lw s2 //=.
  + by move=> [] <- <- /=.
  t_xrbindP => ? [s lw1] /write_lval_cp -> <- /=. move=> H.
  Admitted.

  Lemma write_lval_e_cp gd s1 x v s2 l:
  write_lval gd x v s1 = ok (s2, l) ->
  exists l', l = (lest_to_les l') /\ write_lval_e gd x v s1 = ok (s2, l').
  Proof.
    case : x => /=.
  - move=> _ ty. rewrite /write_none. t_xrbindP.
    move=> y H <- <- /=. rewrite H /=. exists LEmpty.
    rewrite /=. by split.
  - move=> x. rewrite /write_var. t_xrbindP.
    move=> y h Hs Hy He <- /=. rewrite Hs /=. rewrite -Hy in He.
    rewrite -He /=. exists LEmpty. rewrite /=. by split.
  - move=> sz x e. t_xrbindP.
    move=> y h -> /= -> /= [v' l'] He h4 Hw h8 Hw' m Hm <- <- /=.
    move: (sem_pexpr_e_to_sem_pexpr). move=> H.
    move: (H gd s1 e v' l' He) => [] x0 [] Hl He'. exists (LSub [:: x0; (LAdr (y+h4))]).
    rewrite Hl /=. rewrite /lests_to_les /=. split. by rewrite cats1. 
    rewrite He' /=. rewrite Hw /=.
    rewrite Hw' /=. by rewrite Hm /=.
  - move=> sz x e /=. apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => Hg.
    t_xrbindP. move=> [yv yl] Hs z Hi w Hw a Ha h6 Hs' <- <- /=.
    rewrite Hg /=. move: (sem_pexpr_e_to_sem_pexpr). move=> H.
    move: (H gd s1 e yv yl Hs) => [] x0 [] Hl He'. exists (LSub [:: x0; (LIdx z)]).
    rewrite Hl /=. rewrite /lests_to_les /=. split. by rewrite cats1.
    rewrite He' /=. rewrite Hi /=. rewrite Hw /=. rewrite Ha /=. by rewrite Hs' /=.
  Qed.

  Lemma write_lval_es_cp gd s1 xs vs s2 l:
  write_lvals gd s1 xs vs = ok (s2, l) ->
  exists l', l = (lest_to_les l') /\ write_lvals_e gd s1 xs vs = ok (s2, l').
  Proof.
  rewrite /write_lvals. rewrite /write_lvals_e.
  elim: xs vs s1 [::] l s2 => [|x xs Hrec] [|v vs] s1 lw0 lw s2 //=.
  Admitted.

Section SEM_I.
Variable P:prog.
Notation gd := (p_globs P).

Definition sem_range_e (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  Let vl1 := sem_pexpr_e gd s pe1 in 
  Let i1 := to_int vl1.1 in 
  Let vl2 := sem_pexpr_e gd s pe2 in 
  Let i2 := to_int vl2.1 in
  ok (wrange d i1 i2, LSub [:: vl1.2 ; vl2.2]).

Definition sem_sopn_e gd o m lvs args := 
  Let vas := sem_pexprs_e gd m args in
  Let vs := exec_sopn o vas.1 in 
  Let ml := write_lvals_e gd m lvs vs in
  ok (ml.1, LSub [ :: vas.2 ; ml.2]).


Inductive sem_c_i : estate -> cmd -> seq leak_i_tree -> estate -> Prop :=
| Eskip_i s :
    sem_c_i s [::] [::] s

| Eseq_i s1 s2 s3 i c li lc :
    sem_I_i s1 i li s2 -> sem_c_i s2 c lc s3 -> sem_c_i s1 (i::c) (li :: lc) s3

with sem_I_i : estate -> instr -> leak_i_tree -> estate -> Prop :=
| EmkI_i ii i s1 s2 li:
    sem_i_i s1 i li s2 ->
    sem_I_i s1 (MkI ii i) li s2

with sem_i_i : estate -> instr_r -> leak_i_tree -> estate -> Prop :=
| Eassgn_i s1 s2 (x:lval) tag ty e v v' l1 l2:
    sem_pexpr_e gd s1 e = ok (v,l1)  ->
    truncate_val ty v = ok v' →
    write_lval_e gd x v' s1 = ok (s2, l2) ->
    sem_i_i s1 (Cassgn x tag ty e) (LTassgn (LSub [:: l1 ; l2])) s2

| Eopn_i s1 s2 t o xs es lo:
    sem_sopn_e gd o s1 xs es = ok (s2, lo) ->
    sem_i_i s1 (Copn xs t o es) (LTopn lo) s2

| Eif_true_i s1 s2 e c1 c2 le lc:
    sem_pexpr_e gd s1 e = ok (Vbool true, le) ->
    sem_c_i s1 c1 lc s2 ->
    sem_i_i s1 (Cif e c1 c2) (LTcond le true lc) s2

| Eif_false_i s1 s2 e c1 c2 le lc:
    sem_pexpr_e gd s1 e = ok (Vbool false, le) ->
    sem_c_i s1 c2 lc s2 ->
    sem_i_i s1 (Cif e c1 c2) (LTcond le false lc) s2

| Ewhile_true_i s1 s2 s3 s4 a c e c' lc le lc' lw:
    sem_c_i s1 c lc s2 ->
    sem_pexpr_e gd s2 e = ok (Vbool true, le) ->
    sem_c_i s2 c' lc' s3 ->
    sem_i_i s3 (Cwhile a c e c') lw s4 ->
    sem_i_i s1 (Cwhile a c e c') (LTwhile_true lc le lc' lw) s4

| Ewhile_false_i s1 s2 a c e c' lc le:
    sem_c_i s1 c lc s2 ->
    sem_pexpr_e gd s2 e = ok (Vbool false, le) ->
    sem_i_i s1 (Cwhile a c e c') (LTwhile_false lc le) s2

| Efor_i s1 s2 (i:var_i) r c wr lr lf:
    sem_range_e s1 r = ok (wr, lr) ->
    sem_for_i i wr s1 c lf s2 ->
    sem_i_i s1 (Cfor i r c) (LTfor lr lf) s2

| Ecall_i s1 m2 s2 ii xs f args vargs vs l1 lf l2:
    sem_pexprs_e gd s1 args = ok (vargs, l1) ->
         sem_call_i s1.(emem) f vargs lf m2 vs ->
    write_lvals_e gd {|emem:= m2; evm := s1.(evm) |} xs vs = ok (s2, l2) ->
    sem_i_i s1 (Ccall ii xs f args) (LTcall l1 lf l2) s2

with sem_for_i : var_i -> seq Z -> estate -> cmd -> seq (seq leak_i_tree) -> estate -> Prop :=
| EForDone_i s i c :
    sem_for_i i [::] s c [::] s

| EForOne_i s1 s1' s2 s3 i w ws c lc lw :
    write_var i (Vint w) s1 = ok s1' ->
    sem_c_i s1' c lc s2 ->
    sem_for_i i ws s2 c lw s3 ->
    sem_for_i i (w :: ws) s1 c (lc :: lw) s3

with sem_call_i : Memory.mem -> funname -> seq value -> (funname * seq leak_i_tree) -> Memory.mem -> seq value -> Prop :=
| EcallRun_i m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc :
    get_fundef (p_funcs P) fn = Some f ->
    mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
    write_vars f.(f_params) vargs (Estate m1 vmap0) = ok s1 ->
    sem_c_i s1 f.(f_body) lc (Estate m2 vm2) ->
    mapM (fun (x:var_i) => get_var vm2 x) f.(f_res) = ok vres ->
    mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
    sem_call_i m1 fn vargs' (fn, lc) m2 vres'.

End SEM_I.

Section SEM_IND_I.

  Variable P:prog.
  Notation gd := (p_globs P).

  Variables
    (Pci  : estate -> cmd -> seq leak_i_tree -> estate -> Prop)
    (Pi_ri : estate -> instr_r -> leak_i_tree -> estate -> Prop)
    (Pi_i : estate -> instr -> leak_i_tree -> estate -> Prop)
    (Pfor_i : var_i -> seq Z -> estate -> cmd -> seq (seq leak_i_tree) -> estate -> Prop)
    (Pfun_i : Memory.mem -> funname -> seq value -> funname * seq leak_i_tree -> Memory.mem -> seq value -> Prop).

  Definition sem_Ind_nil_i : Prop :=
    forall s : estate, Pci s [::] [::] s.

  Definition sem_Ind_cons_i : Prop :=
    forall (s1 s2 s3 : estate) (i : instr) (c : cmd) (li : leak_i_tree) (lc : seq leak_i_tree),
      sem_I_i P s1 i li s2 -> Pi_i s1 i li s2 -> sem_c_i P s2 c lc s3 ->
      Pci s2 c lc s3 -> Pci s1 (i :: c) (li :: lc) s3.

  Hypotheses
    (Hnil_i: sem_Ind_nil_i)
    (Hcons_i: sem_Ind_cons_i).

  Definition sem_Ind_mkI_i : Prop :=
    forall (ii : instr_info) (i : instr_r) (s1 s2 : estate) (li : leak_i_tree),
      sem_i_i P s1 i li s2 -> Pi_ri s1 i li s2 -> Pi_i s1 (MkI ii i) li s2.

  Hypothesis HmkI : sem_Ind_mkI_i.

  Definition sem_Ind_assgn_i : Prop :=
    forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v' (le lw : leak_e_tree),
      sem_pexpr_e gd s1 e = ok (v, le) ->
      truncate_val ty v = ok v' →
      write_lval_e gd x v' s1 = Ok error (s2, lw) ->
      Pi_ri s1 (Cassgn x tag ty e) (LTassgn (LSub [:: le ; lw])) s2.

  Definition sem_Ind_opn_i : Prop :=
    forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs) (lo : leak_e_tree),
      sem_sopn_e gd o s1 xs es = Ok error (s2, lo) ->
      Pi_ri s1 (Copn xs t o es) (LTopn lo) s2.

  Definition sem_Ind_if_true_i : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) (le : leak_e_tree) (lc : seq leak_i_tree),
      sem_pexpr_e gd s1 e = ok (Vbool true, le) ->
      sem_c_i P s1 c1 lc s2 -> Pci s1 c1 lc s2 -> Pi_ri s1 (Cif e c1 c2) (LTcond le true lc) s2.

  Definition sem_Ind_if_false_i : Prop :=
    forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) (le : leak_e_tree) (lc : seq leak_i_tree),
      sem_pexpr_e gd s1 e = ok (Vbool false, le) ->
      sem_c_i P s1 c2 lc s2 -> Pci s1 c2 lc s2 -> Pi_ri s1 (Cif e c1 c2) (LTcond le false lc) s2.

  Definition sem_Ind_while_true_i : Prop :=
    forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd) (lc : seq leak_i_tree) 
           (le : leak_e_tree) (lc' : seq leak_i_tree) (li : leak_i_tree),
      sem_c_i P s1 c lc s2 -> Pci s1 c lc s2 ->
      sem_pexpr_e gd s2 e = ok (Vbool true, le) ->
      sem_c_i P s2 c' lc' s3 -> Pci s2 c' lc' s3 ->
      sem_i_i P s3 (Cwhile a c e c') li s4 -> 
      Pi_ri s3 (Cwhile a c e c') li s4 -> 
      Pi_ri s1 (Cwhile a c e c') (LTwhile_true lc le lc' li) s4.

  Definition sem_Ind_while_false_i : Prop :=
    forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd) (lc : seq leak_i_tree) (le : leak_e_tree),
      sem_c_i P s1 c lc s2 -> Pci s1 c lc s2 ->
      sem_pexpr_e gd s2 e = ok (Vbool false, le) ->
      Pi_ri s1 (Cwhile a c e c') (LTwhile_false lc le) s2.

  Hypotheses
    (Hasgn_i: sem_Ind_assgn_i)
    (Hopn_i: sem_Ind_opn_i)
    (Hif_true_i: sem_Ind_if_true_i)
    (Hif_false_i: sem_Ind_if_false_i)
    (Hwhile_true_i: sem_Ind_while_true_i)
    (Hwhile_false_i: sem_Ind_while_false_i).

  Definition sem_Ind_for_i : Prop :=
    forall (s1 s2 : estate) (i : var_i) r wr (c : cmd) (lr : leak_e_tree) (lf: seq (seq leak_i_tree)),
      sem_range_e P s1 r = ok (wr, lr) ->
      sem_for_i P i wr s1 c lf s2 ->
      Pfor_i i wr s1 c lf s2 -> Pi_ri s1 (Cfor i r c) (LTfor lr lf) s2.

  Definition sem_Ind_for_nil_i : Prop :=
    forall (s : estate) (i : var_i) (c : cmd),
      Pfor_i i [::] s c [::] s.

  Definition sem_Ind_for_cons_i : Prop :=
    forall (s1 s1' s2 s3 : estate) (i : var_i) (w : Z) (ws : seq Z) (c : cmd) (lc : seq leak_i_tree)
           (lf : seq (seq leak_i_tree)),
      write_var i w s1 = Ok error s1' ->
      sem_c_i P s1' c lc s2 -> Pci s1' c lc s2 ->
      sem_for_i P i ws s2 c lf s3 -> Pfor_i i ws s2 c lf s3 -> Pfor_i i (w :: ws) s1 c (lc :: lf) s3.

  Hypotheses
    (Hfor_i: sem_Ind_for_i)
    (Hfor_nil_i: sem_Ind_for_nil_i)
    (Hfor_cons_i: sem_Ind_for_cons_i).

  Definition sem_Ind_call_i : Prop :=
    forall (s1 : estate) (m2 : Memory.mem) (s2 : estate)
           (ii : inline_info) (xs : lvals)
           (fn : funname) (args : pexprs) (vargs vs : seq value) (l1 : leak_e_tree)
           (lf : funname * seq leak_i_tree) (lw : leak_e_tree),
      sem_pexprs_e gd s1 args = Ok error (vargs, l1) ->
      sem_call_i P (emem s1) fn vargs lf m2 vs -> Pfun_i (emem s1) fn vargs lf m2 vs ->
      write_lvals_e gd {| emem := m2; evm := evm s1 |} xs vs = Ok error (s2, lw) ->
      Pi_ri s1 (Ccall ii xs fn args) (LTcall l1 lf lw) s2.

  Definition sem_Ind_proc_i : Prop :=
    forall (m1 m2 : Memory.mem) (fn:funname) (f : fundef) (vargs vargs': seq value)
           (s1 : estate) (vm2 : vmap) (vres vres': seq value) (lc : seq leak_i_tree),
      get_fundef (p_funcs P) fn = Some f ->
      mapM2 ErrType truncate_val f.(f_tyin) vargs' = ok vargs ->
      write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
      sem_c_i P s1 (f_body f) lc {| emem := m2; evm := vm2 |} ->
      Pci s1 (f_body f) lc {| emem := m2; evm := vm2 |} ->
      mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
      mapM2 ErrType truncate_val f.(f_tyout) vres = ok vres' ->
      Pfun_i m1 fn vargs' (fn, lc) m2 vres'.

  Hypotheses
    (Hcall_i: sem_Ind_call_i)
    (Hproc_i: sem_Ind_proc_i).

  Fixpoint sem_Ind_i (e : estate) (l : cmd) (le : seq leak_i_tree) (e0 : estate) (s : sem_c_i P e l le e0) {struct s} :
    Pci e l le e0 :=
    match s in (sem_c_i _ e1 l0 l1 e2) return (Pci e1 l0 l1 e2) with
    | Eskip_i s0 => Hnil_i s0
    | @Eseq_i _ s1 s2 s3 i c li lc s0 s4 =>
        @Hcons_i s1 s2 s3 i c li lc s0 (@sem_I_Ind_i s1 i li s2 s0) s4 (@sem_Ind_i s2 c lc s3 s4) 
    end

  with sem_i_Ind_i (e : estate) (i : instr_r) (li : leak_i_tree) (e0 : estate) (s : sem_i_i P e i li e0) {struct s} :
    Pi_ri e i li e0 :=
    match s in (sem_i_i _ e1 i0 le1 e2) return (Pi_ri e1 i0 le1 e2) with
    | @Eassgn_i _ s1 s2 x tag ty e1 v v' l1 l2 h1 h2 h3 => @Hasgn_i s1 s2 x tag ty e1 v v' l1 l2 h1 h2 h3
    | @Eopn_i _ s1 s2 t o xs es lo e1 => @Hopn_i s1 s2 t o xs es lo e1
    | @Eif_true_i _ s1 s2 e1 c1 c2 le lc e2 s0 =>
      @Hif_true_i s1 s2 e1 c1 c2 le lc e2 s0 (@sem_Ind_i s1 c1 lc s2 s0)
    | @Eif_false_i _ s1 s2 e1 c1 c2 le lc e2 s0 =>
      @Hif_false_i s1 s2 e1 c1 c2 le lc e2 s0 (@sem_Ind_i s1 c2 lc s2 s0)
    | @Ewhile_true_i _ s1 s2 s3 s4 a c e1 c' lc le lc' lw h1 h2 h3 h4 =>
      @Hwhile_true_i s1 s2 s3 s4 a c e1 c' lc le lc' lw h1 (@sem_Ind_i s1 c lc s2 h1) h2 h3 (@sem_Ind_i s2 c' lc' s3 h3) 
          h4 (@sem_i_Ind_i s3 (Cwhile a c e1 c') lw s4 h4)
    | @Ewhile_false_i _ s1 s2 a c e1 c' lc le s0 e2 =>
      @Hwhile_false_i s1 s2 a c e1 c' lc le s0 (@sem_Ind_i s1 c lc s2 s0) e2
    | @Efor_i _ s1 s2 i0 r c wr lr lf s0 sf =>
      @Hfor_i s1 s2 i0 r wr c lr lf s0 sf
        (@sem_for_Ind_i i0 wr s1 c lf s2 sf)
    | @Ecall_i _ s1 m2 s2 ii xs f13 args vargs vs l1 lf l2 e2 s0 e3 =>
      @Hcall_i s1 m2 s2 ii xs f13 args vargs vs l1 lf l2 e2 s0
        (@sem_call_Ind_i (emem s1) f13 vargs m2 vs lf s0) e3
    end

  with sem_I_Ind_i (e : estate) (i : instr) (li : leak_i_tree) (e0 : estate) (s : sem_I_i P e i li e0) {struct s} :
    Pi_i e i li e0 :=
    match s in (sem_I_i _ e1 i0 le e2) return (Pi_i e1 i0 le e2) with
    | @EmkI_i _ ii i0 s1 s2 li s0 => @HmkI ii i0 s1 s2 li s0 (@sem_i_Ind_i s1 i0 li s2 s0)
    end

  with sem_for_Ind_i (v : var_i) (l : seq Z) (e : estate) (l0 : cmd) (lf : seq (seq leak_i_tree))
                     (e0 : estate) (s : sem_for_i P v l e l0 lf e0) {struct s} : Pfor_i v l e l0 lf e0 :=
    match s in (sem_for_i _ v0 l1 e1 l2 le e2) return (Pfor_i v0 l1 e1 l2 le e2) with
    | EForDone_i s0 i c => Hfor_nil_i s0 i c
    | @EForOne_i _ s1 s1' s2 s3 i w ws c lc lw e1 s0 s4 =>
      @Hfor_cons_i s1 s1' s2 s3 i w ws c lc lw e1 s0 (@sem_Ind_i s1' c lc s2 s0)
         s4 (@sem_for_Ind_i i ws s2 c lw s3 s4)
    end

  with sem_call_Ind_i (m : Memory.mem) (f13 : funname) (l : seq value) (m0 : Memory.mem)
                    (l0 : seq value) (lf : funname * seq leak_i_tree) (s : sem_call_i P m f13 l lf m0 l0) {struct s} :
                    Pfun_i m f13 l lf m0 l0 :=
    match s with
    | @EcallRun_i _ m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hctin Hw Hsem Hvres Hctout =>
       @Hproc_i m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hget Hctin Hw Hsem (sem_Ind_i Hsem) Hvres Hctout
    end.

End SEM_IND_I.

Lemma sem_sopn_cp gd o s1 xs es s2 l:
  sem_sopn_e gd o s1 xs es = ok (s2, l) ->
  sem_sopn gd o s1 xs es = ok (s2, lest_to_les l).
  Proof.
    rewrite /sem_sopn_e. t_xrbindP.
    move=> [yv yl] He h0 Hex [yv' yl'] Hw <- <-.
    rewrite /sem_sopn. t_xrbindP.
    move: const_prop_e_esP_sem_pexprs_e'. move=> H.
    move: (H gd s1 es (yv, yl) He). move=> -> /=.
    rewrite /= in Hex. rewrite Hex /=.
    move: (write_lvals_cp). move=> Hw'. move: (Hw' gd s1 xs h0 yv' yl' Hw).
    move=> -> /=. rewrite /lests_to_les /=. by rewrite cats0.
  Qed.

Lemma sem_sopn_e_cp gd o s1 xs es s2 l:
  sem_sopn gd o s1 xs es = ok (s2, l) ->
  exists l', l = (lest_to_les l') /\ sem_sopn_e gd o s1 xs es = ok (s2, l').
  Proof.
    rewrite /sem_sopn. t_xrbindP.
    move=> [yv yl] He h0 Hex [yv' yl'] Hw <- <-.
    rewrite /sem_sopn_e. t_xrbindP.
    move: sem_pexprs_to_sem_pexprs_e'. move=> H.
    move: (H s1 gd es (yv, yl) He). move=> [] vs' [] Hv [] /= Hl -> /=.
    rewrite -Hv /=. rewrite /= in Hex. rewrite Hex /=.
    move: (write_lval_es_cp). move=> Hw'. move: (Hw' gd s1 xs h0 yv' yl' Hw).
    move=> [] l' [] Hl' Hws. rewrite Hws /=. exists (LSub [:: vs'.2; l']).
    rewrite /=. rewrite /lests_to_les /=. rewrite -Hl' Hl. rewrite cats0. by split.
  Qed.

 Lemma sem_range_cp gd s r s2 l:
  sem_range_e gd s r = ok (s2, l) ->
  sem_range gd s r = ok (s2, lest_to_les l).
  Proof.
    rewrite /sem_range_e /=. elim: r. move=> [d e1] e2. t_xrbindP.
    move=> [yv yl] He h0 Hi [yv' yl'] He' h4 Hi' Hs Hl.
    rewrite /sem_range. move: const_prop_e_esP_sem_pexpr_e. move=> H.
    move: (H (p_globs gd) s e1 (yv, yl) He). move=> -> /=. rewrite Hi /=.
    move: const_prop_e_esP_sem_pexpr_e. move=> H'.
    move: (H' (p_globs gd) s e2 (yv', yl') He'). move=> -> /=. rewrite Hi' /=.
    rewrite -Hs -Hl /=. rewrite /lests_to_les /=. by rewrite cats0.
  Qed.

  Lemma sem_range_e_cp gd s r s2 l:
  sem_range gd s r = ok (s2, l) ->
  exists l', l = (lest_to_les l') /\ sem_range_e gd s r = ok (s2, l').
  Proof.
    rewrite /sem_range /=. elim: r. move=> [d e1] e2. t_xrbindP.
    move=> [yv yl] He h0 Hi [yv' yl'] He' h4 Hi' <- Hl.
    rewrite /sem_range_e. move: sem_pexpr_e_to_sem_pexpr. move=> H.
    move: (H (p_globs gd) s e1 yv yl He). move=> [] l0 [] Hl' Hee.
    move: sem_pexpr_e_to_sem_pexpr. move=> H'.
    move: (H' (p_globs gd) s e2 yv' yl' He'). move=> [] l1 [] Hl1 He2 /=.
    rewrite Hee /=. rewrite He2 /=. rewrite Hi /=. rewrite Hi' /=.
    exists ( LSub [:: l0; l1]). rewrite -Hl /=. rewrite Hl' Hl1 /=.
    rewrite /lests_to_les /=. rewrite cats0. by split. 
  Qed.
  
  
Section Sem_I_Leakages_proof.

Variable P:prog.
  
Notation gd := (p_globs P).

Let Pci s1 c lc s2 := exists lc', sem P s1 c lc' s2 /\ lc' = map lit_to_li lc.

Let Pi_ri s1 i li s2 := exists li', sem_i P s1 i li' s2 /\ li' = lit_to_li li.

Let Pi_i s1 i li s2 := exists li', sem_I P s1 i li' s2 /\ li' =  lit_to_li li.

Let Pfor_i i zs s1 c lc s2 := exists lc', sem_for P i zs s1 c lc' s2
                                          /\ lc' = litss_to_liss lit_to_li lc.

Let Pfun_i m1 fd vargs lf m2 vres := exists lf', sem_call P m1 fd vargs (lf.1, lf') m2 vres
                                                 /\ lf' =  map lit_to_li lf.2.

Local Lemma Hnil_i : sem_Ind_nil_i Pci.
Proof.
  rewrite /sem_Ind_nil_i. move=> s. rewrite /Pci.
  exists [::]. split. constructor.
  rewrite /lits_to_lis /=. auto.
Qed.

Local Lemma Hcons_i : sem_Ind_cons_i P Pci Pi_i.
Proof.
  rewrite /sem_Ind_cons_i.
  move=> s1 s2 s3 i c li lc Hi HPi Hc HPc.
  rewrite /Pi_i in HPi. rewrite /Pci in HPc.
  move: (HPi). move=> [] x [] Hx Hlx. move: (HPc).
  move=> [] x' [] Hx' Hlx'. rewrite /Pci.
  exists (x :: x'). split. apply Eseq with s2. auto.
  auto. rewrite Hlx Hlx' /=. auto.
Qed.

Local Lemma HmkI_i : sem_Ind_mkI_i P Pi_ri Pi_i.
Proof.
  rewrite /sem_Ind_mkI_i /=.
  move=> ii i s1 s2 li Hi Hpi.
  rewrite /Pi_i.
  rewrite /Pi_ri in Hpi. move: (Hpi).
  move=> [] li' [] Hii Hl. rewrite /Pi_i.
  exists li'. split.
  apply EmkI. auto. auto.
Qed.

Local Lemma Hasgn_i : sem_Ind_assgn_i P Pi_ri.
Proof.
  rewrite /sem_Ind_assgn_i.
  move=> s1 s2 x tag ty e v v' le lw He Ht Hw.
  rewrite /Pi_ri /=. exists (Lassgn (lests_to_les lest_to_les [:: le; lw])).
  rewrite /lests_to_les /=. rewrite cats0. split. apply Eassgn with v v'.
  move: const_prop_e_esP_sem_pexpr_e. move=> Hc.
  move: (Hc (p_globs P) s1 e (v, le) He). move=> /= He'. auto. auto.
  move: (write_lval_cp). move=> Hw'. move: (Hw' (p_globs P) s1 x v' s2 lw Hw).
  move=> ->. auto. auto.
Qed.

Local Lemma Hopn_i : sem_Ind_opn_i P Pi_ri.
Proof.
  rewrite /sem_Ind_opn_i. move=> s1 s2 t o xs es lo Ho.
  rewrite /Pi_ri. exists (lit_to_li (LTopn lo)).
  split. apply Eopn. move: sem_sopn_cp. move=> Ho'.
  move: (Ho' gd o s1 xs es s2 lo Ho). by move=> -> /=. auto.
Qed.

Local Lemma Hif_true_i : sem_Ind_if_true_i P Pci Pi_ri.
Proof.
  rewrite /sem_Ind_if_true_i. move=> s1 s2 e c1 c2 le lc He Hc Hp.
  rewrite /Pci in Hp. move: (Hp). move=> [] lc' [] Hi Hl /=. rewrite /Pi_ri /=.
  rewrite -Hl /=. exists (Lcond (lest_to_les le) true lc').
  split. apply Eif_true. move: const_prop_e_esP_sem_pexpr_e.
  move=> He'. move: (He' gd s1 e (Vbool true, le) He). by move=> -> /=.
  auto. auto.
Qed.

Local Lemma Hif_false_i : sem_Ind_if_false_i P Pci Pi_ri.
Proof.
  rewrite /sem_Ind_if_true_i. move=> s1 s2 e c1 c2 le lc He Hc Hp.
  rewrite /Pci in Hp. move: (Hp). move=> [] lc' [] Hi Hl /=. rewrite /Pi_ri /=.
  rewrite -Hl. exists (Lcond (lest_to_les le) false lc').
  split. apply Eif_false. move: const_prop_e_esP_sem_pexpr_e.
  move=> He'. move: (He' gd s1 e (Vbool false, le) He). by move=> -> /=.
  auto. auto.
Qed.

Local Lemma Hwhile_true_i : sem_Ind_while_true_i P Pci Pi_ri.
Proof.
  rewrite /sem_Ind_while_true_i.
  move=> s1 s2 s3 s4 a c e c' lc le lc' li Hc Hci He Hc' Hci' Hi Hii.
  rewrite /Pci in Hci'. rewrite /Pi_ri in Hii. rewrite /Pi_ri.
  move: (Hci'). move=> [] lc'0 [] Hs Hsl /=.
  move: (Hii). move=> [] li' [] Hsi Hsli /=. rewrite -Hsli -Hsl /=.
  exists (Lwhile_true [seq lit_to_li i | i <- lc] (lest_to_les le) lc'0 li').
  split. apply Ewhile_true with s2 s3. rewrite /Pci in Hci.
  move: (Hci). move=> [] lc'1 [] Hp <- /=. auto.
  move: const_prop_e_esP_sem_pexpr_e. move=> Hhe.
  move: (Hhe gd s2 e (Vbool true, le) He). by move=> -> /=.
  auto. auto. auto.
Qed.

Local Lemma Hwhile_false_i : sem_Ind_while_false_i P Pci Pi_ri.
Proof.
  rewrite /sem_Ind_while_false_i.
  move=> s1 s2 a c e c' lc le Hci Hpi He. rewrite /Pi_ri.
  rewrite /Pci in Hpi. move: (Hpi).
  move=> [] lc' [] Hs Hsl /=. rewrite -Hsl /=.
  exists (Lwhile_false lc' (lest_to_les le)). split.
  apply Ewhile_false. auto. move: const_prop_e_esP_sem_pexpr_e. move=> Hhe.
  move: (Hhe gd s2 e (Vbool false, le) He). by move=> -> /=. auto.
Qed.

Local Lemma Hfor_i : sem_Ind_for_i P Pi_ri Pfor_i.
Proof.
  rewrite /sem_Ind_for_i. move=> s1 s2 i r wr c lr lf.
  move=> /sem_range_cp Hr Hf. rewrite /Pfor_i /=.
  move=> H. move: (H). move=> []  lc' [] Hf' Hl.
  rewrite /Pi_ri /=. rewrite -Hl /=.
  exists (Lfor (lest_to_les lr) lc').  split. by apply Efor with wr. auto.
Qed.

Local Lemma Hfor_nil_i : sem_Ind_for_nil_i Pfor_i.
Proof.
  rewrite /sem_Ind_for_nil_i. move=> s i c.
  rewrite /Pfor_i. exists [::].
  split. by apply EForDone. auto.
Qed.

Local Lemma Hfor_cons_i : sem_Ind_for_cons_i P Pci Pfor_i.
Proof.
  rewrite /sem_Ind_for_cons_i. move=> s1 s1' s2 s3 i w ws c lc lf Hw Hc Hpi.
  move=> Hf Hpi'. rewrite /Pci in Hpi. rewrite /Pfor_i in Hpi'. rewrite /Pfor_i.
  move: (Hpi). move=> [] lc' [] Hs Hl. move: (Hpi').
  move=> [] lc'0 [] Hs' Hl' /=.
  exists (lits_to_lis (lit_to_li) lc :: litss_to_liss (lit_to_li) lf).
  split. rewrite -Hl' /=. rewrite /lits_to_lis /=. rewrite -Hl /=.
  apply EForOne with s1' s2. auto. auto. auto. auto.
Qed.
  
Local Lemma Hcall_i : sem_Ind_call_i P Pi_ri Pfun_i.
Proof.
  rewrite /sem_Ind_call_i. move=> s1 m2 s2 ii xs fn args vargs vs l1 lf lw.
  move=> Hes Hc Hpi Hws. rewrite /Pi_ri. rewrite /Pfun_i in Hpi.
  move: (Hpi). move=> [] lf' [] Hc' Hl /=. rewrite /=.
  move: (const_prop_e_esP_sem_pexprs_e'). move=> Hes'.
  move: (Hes' gd s1 args (vargs, l1) Hes). move=> Hes''.
  move: (write_lvals_cp). move=> Hws'.
  move: (Hws' gd {| emem := m2; evm := evm s1 |} xs vs s2 lw Hws). move=> Hws''.
  exists (Lcall (lest_to_les l1) (lf.1, lf') (lest_to_les lw)). split. apply Ecall with m2 vargs vs.
  auto. auto. auto. rewrite Hl /=. subst. auto.
Admitted.

Local Lemma Hproc_i : sem_Ind_proc_i P Pci Pfun_i.
Proof.
  rewrite /sem_Ind_proc_i.
  move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hg Hm.
  move=> Hws Hci Hpi Hm' Hm''. rewrite /Pfun_i.
  rewrite /Pci in Hpi. move: (Hpi). move=> [] lc' [] Hpi' Hl.
  rewrite /=. rewrite -Hl /=. exists lc'. rewrite /=.
  split. apply EcallRun with f vargs s1 vm2 vres. auto.
  auto. auto. auto. auto. auto. auto.
Qed.


End Sem_I_Leakages_proof.

Section Sem_I_Sem_Leakages_proof.

Variable P:prog.
  
Notation gd := (p_globs P).

Let Pc s1 c lc s2 := exists lc',  lc = lits_to_lis lit_to_li lc' /\ sem_c_i P s1 c lc' s2.

Let Pi_r s1 i li s2 := exists li', li = lit_to_li li' /\ sem_i_i P s1 i li' s2.

Let Pi s1 i li s2 := exists li', li =  lit_to_li li' /\ sem_I_i P s1 i li' s2.

Let Pfor i zs s1 c lc s2 := exists lc',  lc = litss_to_liss lit_to_li lc' /\
                                           sem_for_i P i zs s1 c lc' s2.
                                          
Let Pfun m1 fd vargs lf m2 vres := exists lf', lf.2 = lits_to_lis lit_to_li (lf') /\
                                                 sem_call_i P m1 fd vargs (lf.1, lf') m2 vres.

Local Lemma Hnil : sem_Ind_nil Pc.
Proof.
  rewrite /sem_Ind_nil. move=> s. rewrite /Pc.
  exists [::]. split. auto. constructor.
Qed.


Local Lemma Hcons : sem_Ind_cons P Pc Pi.
Proof.
  rewrite /sem_Ind_cons.
  move=> s1 s2 s3 i c li lc Hi HPi Hc HPc.
  rewrite /Pi in HPi. rewrite /Pc in HPc.
  move: (HPi). move=> [] x [] Hx Hlx. move: (HPc).
  move=> [] x' [] Hx' [] Hlx'. rewrite /Pc.
  exists (x :: x'). split. rewrite /lits_to_lis /=.
  rewrite /lits_to_lis in Hx'. by rewrite -Hx Hx' /=.
  apply Eseq_i with s2. auto.
  admit. 
  (*apply Eseq with s2. auto. auto.
  rewrite Hlx Hlx'. admit.*)
Admitted.

Local Lemma HmkI : sem_Ind_mkI P Pi_r Pi.
Proof.
  rewrite /sem_Ind_mkI. move=> ii i s1 s2 li Hs H.
  rewrite /Pi_r in H. move: (H). move=> [] li' [] Hl Hi.
  rewrite /Pi. exists li'. split. rewrite -Hl /=. auto.
  constructor. auto.
Qed.

Local Lemma Hasgn : sem_Ind_assgn P Pi_r.
Proof.
  rewrite /sem_Ind_assgn. move=> s1 s2 x tag ty e v v' le lw He Ht Hw.
  rewrite /Pi_r /=.
  move:sem_pexpr_e_to_sem_pexpr. move=> Hc.
  move: (Hc (p_globs P) s1 e v le He). move=> [] x0 [] Hl He'. 
  move: (write_lval_e_cp). move=> Hw'. move: (Hw' (p_globs P) s1 x v' s2 lw Hw).
  move=> [] l' [] Hl' Hww. exists (LTassgn (LSub [:: x0 ; l'])). rewrite /=.
  rewrite /lests_to_les /=. split. rewrite Hl Hl'. by rewrite cats0.
  apply Eassgn_i with v v'. auto. auto. auto.
Qed.

Local Lemma Hopn : sem_Ind_opn P Pi_r.
Proof.
  rewrite /sem_Ind_opn. move=> s1 s2 t o xs es lo Ho.
  rewrite /Pi_r.
  move: (sem_sopn_e_cp). move=> Ho'.
  move: (Ho' gd o s1 xs es s2 lo Ho). move=> [] l' [] Hl Hs.
  exists (LTopn l'). rewrite /=. rewrite -Hl. split. auto.
  apply Eopn_i. auto.
Qed.

Local Lemma Hif_true : sem_Ind_if_true P Pc Pi_r.
Proof.
  rewrite /sem_Ind_if_true. move=> s1 s2 e c1 c2 le lc He Hc Hp.
  rewrite /Pc in Hp. move: (Hp). move=> [] lc' [] Hi Hl /=.
  move:sem_pexpr_e_to_sem_pexpr. move=> Hc'. move: (Hc' gd s1 e (Vbool true) le He).
  move=> [] l [] Hle Hee. exists (LTcond l true lc'). split. rewrite /=.
  rewrite -Hle. rewrite /lits_to_lis in Hi. by rewrite -Hi.
  apply Eif_true_i. auto. auto.
Qed.

Local Lemma Hif_false : sem_Ind_if_false P Pc Pi_r.
Proof.
  rewrite /sem_Ind_if_false. move=> s1 s2 e c1 c2 le lc He Hc Hp.
  rewrite /Pc in Hp. move: (Hp). move=> [] lc' [] Hi Hl /=.
  move:sem_pexpr_e_to_sem_pexpr. move=> Hc'. move: (Hc' gd s1 e (Vbool false) le He).
  move=> [] l [] Hle Hee. exists (LTcond l false lc'). split. rewrite /=.
  rewrite -Hle. rewrite /lits_to_lis in Hi. by rewrite -Hi. apply Eif_false_i. auto. auto.
Qed.

Local Lemma Hwhile_true : sem_Ind_while_true P Pc Pi_r.
Proof.
  rewrite /sem_Ind_while_true.
  move=> s1 s2 s3 s4 a c e c' lc le lc' li Hc Hci He Hc' Hci' Hi Hii.
  rewrite /Pc in Hci'. rewrite /Pi_r in Hii. rewrite /Pi_r.
  move: (Hci'). move=> [] lc'0 [] Hs Hsl /=.
  move: (Hii). move=> [] li' [] Hsi Hsli /=.
  move: (sem_pexpr_e_to_sem_pexpr). move=> Hp.
  move: (Hp gd s2 e (Vbool true) le He). move=> [] l [] Hl Hee.
  rewrite /Pc in Hci. move: (Hci). move=> [] lc'1 [] Hp' Hpl /=.
  exists (LTwhile_true lc'1 l lc'0 li'). rewrite /=. split.
  rewrite /lits_to_lis in Hp'. rewrite /lits_to_lis in Hs.
  by rewrite -Hs -Hp' -Hl -Hsi /=. apply Ewhile_true_i with s2 s3.
  auto. auto. auto. auto.
Qed.

Local Lemma Hwhile_false : sem_Ind_while_false P Pc Pi_r.
Proof.
  rewrite /sem_Ind_while_false.
  move=> s1 s2 a c e c' lc le Hci Hpi He. rewrite /Pi_r.
  rewrite /Pc in Hpi. move: (Hpi).
  move=> [] lc' [] Hs Hsl /=.
  move: sem_pexpr_e_to_sem_pexpr. move=> Hhe.
  move: (Hhe gd s2 e (Vbool false) le He).
  move=> [] l [] Hl Hee /=. exists (LTwhile_false lc' l).
  rewrite /=. split. rewrite /lits_to_lis in Hs. by rewrite -Hl -Hs /=.
  apply Ewhile_false_i. auto. auto.
Qed.

Local Lemma Hfor : sem_Ind_for P Pi_r Pfor.
Proof.
  rewrite /sem_Ind_for. move=> s1 s2 i r wr c lr lf.
  move=> /sem_range_e_cp Hr Hf. rewrite /Pfor /=.
  move=> H. move: (H). move=> []  lc' [] Hf' Hl.
  rewrite /Pi_r /=. move: Hr. move=> [] l' [] Hlr Hr'.
  exists (LTfor l' lc'). rewrite /=. split. by rewrite -Hf' -Hlr.
  apply Efor_i with wr. auto. auto.
Qed.

Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
Proof.
  rewrite /sem_Ind_for_nil. move=> s i c.
  rewrite /Pfor. exists [::].
  split. by rewrite /=. apply EForDone_i.
Qed.

Local Lemma Hfor_cons : sem_Ind_for_cons P Pc Pfor.
Proof.
  rewrite /sem_Ind_for_cons. move=> s1 s1' s2 s3 i w ws c lc lf Hw Hc Hpi.
  move=> Hf Hpi'. rewrite /Pfor. rewrite /Pc in Hpi.
  rewrite /Pfor in Hpi'. move: (Hpi). move=> [] lc' [] Hlc Hcc.
  move: (Hpi'). move=> [] lc'0 [] Hlf Hsc.
  exists (lc':: lc'0). rewrite /=. split.
  rewrite /lits_to_lis /=. rewrite Hlc Hlf.
  by rewrite /lits_to_lis.
  apply EForOne_i with s1' s2. auto. auto. auto.
Qed.

Local Lemma Hcall : sem_Ind_call P Pi_r Pfun.
Proof.
  rewrite /sem_Ind_call. move=> s1 m2 s2 ii xs fn args vargs vs l1 lf lw.
  move=> Hes Hc Hpi Hws. rewrite /Pi_r. rewrite /Pfun in Hpi.
  move: (Hpi). move=> [] lf' [] Hc' Hl /=.
  move: (sem_pexprs_to_sem_pexprs_e'). move=> Hs.
  move: (Hs s1 gd args (vargs, l1) Hes). move=> [] vs' [] Hv [] Hl' Hes'.
  move: (write_lval_es_cp). move=> Hws'.
  move: (Hws' gd {| emem := m2; evm := evm s1 |} xs vs s2 lw Hws).
  move=> [] li' [] Hlw Hws''. exists (LTcall vs'.2 (lf.1, lf') li'). split.
  rewrite /=. rewrite /lits_to_lis in Hc'. rewrite -Hc' -Hlw /=.
  rewrite /= in Hl'. rewrite -Hl'.
  case lf. rewrite /=. auto. 
  apply Ecall_i with m2 vargs vs. auto. auto. rewrite /= in Hv.
  rewrite Hv /=. assert (vs' = (vs'.1, vs'.2)). destruct vs'. rewrite /=. auto.
  rewrite -H. auto. auto. auto.
Qed.

Local Lemma Hproc : sem_Ind_proc P Pc Pfun.
Proof.
  rewrite /sem_Ind_proc. move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc Hg Hm.
  move=> Hws Hci Hpi Hm' Hm''. rewrite /Pfun.
  rewrite /Pc in Hpi. move: (Hpi). move=> [] lc' [] Hpi' Hl.
  rewrite /=. rewrite Hpi'. exists lc'. split. auto.
  apply EcallRun_i with f vargs s1 vm2 vres. auto.
  auto. auto. auto. auto. auto.
Qed.

End Sem_I_Sem_Leakages_proof.

Lemma sem_seq1_i P i li s1 s2:
  sem_I_i P s1 i li s2 -> sem_c_i P s1 [::i] [::li] s2.
Proof.
  move=> Hi. apply Eseq_i with s2. auto. constructor.
Qed.

Lemma sem_app_i P l1 l2 s1 s2 s3 ls1 ls2:
  sem_c_i P s1 l1 ls1 s2 -> sem_c_i P s2 l2 ls2 s3 ->
  sem_c_i P s1 (l1 ++ l2) (ls1 ++ ls2) s3.
Proof.
  elim: l1 s1 ls1. move=> s1 ls1 Hs1 Hs2 /=.
Admitted.
