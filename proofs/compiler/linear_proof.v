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

(* * Syntax and semantics of the linear language *)

(* ** Imports and settings *)
Require Import Setoid Morphisms.

From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith Utf8.
        Import Relations.

Require Import psem compiler_util stack_alloc stack_sem.
Require Export linear linear_sem trelation.
        Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Lemma align_bind ii a p1 l ltc:
  Let p := align ii a p1 in ciok (p.1.1, p.1.2 ++ l, p.2 ++ ltc) =
  align ii a (Let p := p1 in ciok (p.1.1, p.1.2 ++ l, p.2 ++ ltc)).
Proof. by rewrite /align; case: a => //; case: p1. Qed.

Section CAT.

  Let Pi (i:instr) :=
    forall lbl l,
     linear_i i lbl l =
     linear_i i lbl [::] >>= (fun (p:label * lcmd * leak_i_il_tr) => ok (p.1.1, p.1.2 ++ l, p.2)).

  Let Pr (i:instr_r) :=
    forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall lbl l,
     linear_c linear_i c lbl l =
     linear_c linear_i c lbl [::] >>= (fun (p:label * lcmd * seq leak_i_il_tr) => ok (p.1.1, p.1.2 ++ l, p.2)).

  Let Pf (fd:fundef) := True.

  Let HmkI: forall i ii, Pr i -> Pi (MkI ii i).
  Proof. by []. Qed.

  Let Hskip : Pc [::].
  Proof. by []. Qed.

  Let Hseq : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc lbl l /=.
    rewrite Hc !bindA;apply bind_eq => //= p.
    rewrite Hi (Hi p.1.1 p.1.2) bindA.
    by case heqi : linear_i=> //=; rewrite catA.
  Qed.

  Let Hassgn : forall x tg ty e, Pr (Cassgn x tg ty e).
  Proof. by move => x tg [] // sz e ii lbl c /=; case: assert. Qed.

  Let Hopn : forall xs t o es, Pr (Copn xs t o es).
  Proof. by []. Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii lbl l /=.
    case Heq1: (c1)=> [|i1 l1].
    + by rewrite Hc2 (Hc2 _ [::_]) !bindA;apply bind_eq => //= p; rewrite -catA.
    rewrite -Heq1=> {Heq1 i1 l1};case Heq2: (c2)=> [|i2 l2].
    + by rewrite Hc1 (Hc1 _ [::_]) !bindA;apply bind_eq => //= p;rewrite -catA.
    rewrite -Heq2=> {Heq2 i2 l2}.
    rewrite Hc1 (Hc1 _ [::_]) !bindA;apply bind_eq => //= p.
    rewrite Hc2 (Hc2 _ [::_ & _])!bindA;apply bind_eq => //= p1.
    by rewrite -!catA /= -catA.
  Qed.

  Let Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir, lo, hi) c).
  Proof. by []. Qed.

  Let Hwhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    move=> a c e c' Hc Hc' ii lbl l /=.
    case: is_bool => [ [] | ].
    + case: c' Hc' => [ _ | i c'].
      + rewrite Hc (Hc _ [:: _]) /=. case: linear_c=> //=.
        case: a=> //=. move=> p. 
        by rewrite -!catA /=. move=> p. by rewrite -!catA.
      move: (i :: c') => { i c' } c' Hc'.
      rewrite Hc (Hc _ [:: _]) !bindA; apply bind_eq => //= p.
      rewrite Hc' (Hc' _ (_ :: _)) !bindA; apply bind_eq=> //= p'.
      by case: a => /=; rewrite -catA /= -catA /=.
    + move: (Hc lbl l). move=> -> /=. by case: linear_c => //=.
    case: c' Hc' => [ _ | i c' ].
    + rewrite Hc (Hc _ [:: _]) /=. case: linear_c=> //=.
        case: a=> //=. move=> p. 
        by rewrite -!catA /=. move=> p. by rewrite -!catA.
    move: (i :: c') => { i c' } c' Hc'.
    rewrite Hc (Hc _ [:: _]) !bindA; apply bind_eq => //= p.
    rewrite Hc' (Hc' _ (_ :: _)) !bindA; apply bind_eq=> //= p'.
    by case: a => /=; rewrite -catA /= -catA /=.
  Qed.

  Let Hcall : forall i xs f es, Pr (Ccall i xs f es).
  Proof. by []. Qed.

  Lemma linear_i_nil i lbl l :
     linear_i i lbl l =
     linear_i i lbl [::] >>= (fun (p:label * lcmd * leak_i_il_tr) => ok (p.1.1, p.1.2 ++ l, p.2)).
  Proof.
    apply (@instr_Rect Pr Pi Pc HmkI Hskip Hseq Hassgn Hopn Hif Hfor Hwhile Hcall).
  Qed.

  Lemma linear_c_nil c lbl l :
     linear_c linear_i c lbl l =
     linear_c linear_i c lbl [::] >>= (fun (p:label * lcmd * seq leak_i_il_tr) =>
     ok (p.1.1, p.1.2 ++ l, p.2)).
  Proof.
    apply (@cmd_rect Pr Pi Pc HmkI Hskip Hseq Hassgn Hopn Hif Hfor Hwhile Hcall).
  Qed.

End CAT.

(* checks the range of label *)
Definition valid min max lc :=
  all (fun (i: linstr) => let (ii, ir) := i in match ir with
       | Lilabel   lbl => ((min <=? lbl) && (lbl <? max))%positive
       | Ligoto    lbl => ((min <=? lbl) && (lbl <? max))%positive
       | Licond _  lbl => ((min <=? lbl) && (lbl <? max))%positive
       | _            => true
       end) lc.

Lemma valid_cat min max lc1 lc2 :
  valid min max (lc1 ++ lc2) = valid min max lc1 && valid min max lc2.
Proof. by rewrite /valid all_cat. Qed.


Lemma valid_add_align lbl1 lbl2 ii a c :
  valid lbl1 lbl2 (add_align ii a c) = valid lbl1 lbl2 c.
Proof. by rewrite /add_align; case: a. Qed.

Lemma valid_le_min min2 min1 max lc :
  (min1 <=? min2)%positive ->
  valid min2 max lc ->
  valid min1 max lc.
Proof.
  by move=> Hle1; apply: sub_all=> -[ii [||lbl|lbl|e lbl]] //= /andP [] Hle2 ->;
  rewrite (Pos_leb_trans Hle1 Hle2).
Qed.

Lemma valid_le_max max2 max1 min lc :
  (max1 <=? max2)%positive ->
  valid min max1 lc ->
  valid min max2 lc.
Proof.
  by move=> Hle1; apply sub_all=> -[ii [||lbl|lbl|e lbl]] //= /andP [] -> Hlt1 /=;
   rewrite (Pos_lt_leb_trans Hlt1 Hle1).
Qed.

Lemma le_next lbl : (lbl <=? next_lbl lbl)%positive.
Proof.
  by apply Pos.leb_le; have: (Zpos lbl <= Zpos lbl + 1)%Z by omega.
Qed.

Lemma lt_next lbl : (lbl <? next_lbl lbl)%positive.
Proof.
  by apply Pos.ltb_lt; have: (Zpos lbl < Zpos lbl + 1)%Z by omega.
Qed.

Lemma find_label_cat_tl c2 c1 lbl p:
  find_label lbl c1 = ok p -> find_label lbl (c1++c2) = ok p.
Proof.
  rewrite /find_label;case:ifPn => // Hs [<-].
  by rewrite find_cat size_cat has_find Hs (ltn_addr _ Hs).
Qed.

(* TODO move this *)
Lemma onth_cat T (s1 s2 : seq T) n :
  oseq.onth (s1 ++ s2) n = (if n < size s1 then oseq.onth s1 n else oseq.onth s2 (n - size s1)).
Proof. by rewrite !oseq.onth_nth map_cat nth_cat size_map. Qed.

Lemma find_instr_cat_tl c s i :
  find_instr s = Some i ->
  find_instr (setc s (lc s ++ c)) = Some i.
Proof.
  rewrite /setc /find_instr /= => /(oseq.onthP i) /andP [Hs Hnth].
  by apply /(oseq.onthP i);rewrite size_cat nth_cat Hs (ltn_addr _ Hs).
Qed.

Lemma to_estate_setc s c : to_estate (setc s c) = to_estate s.
Proof. by case: s. Qed.

Section Section.

Context {LO: LeakOp}.

Lemma lsem_cat_tl c2 gd s1 s2 l1: lsem gd s1 l1 s2 ->
  lsem gd (setc s1 (s1.(lc)++c2)) l1 (setc s2 (s2.(lc)++c2)).
Proof.
  move=> H; elim H using lsem_ind; clear. once (econstructor; fail).
  move=> s1 l1 s2 l2 s3 Hsem1 Hsem.
  apply: lsem_step.
  move: Hsem1;rewrite /lsem1 /step.
  case Heq : find_instr => [i |//].
  rewrite (find_instr_cat_tl c2 Heq) /eval_instr => {Heq}; case: i => [ii [lv o e||l|l|e l]] /=;
    rewrite ?to_estate_setc;t_xrbindP.
  + by move=> [[m vm] l] /= -> <- <- /=;case: s1=> //=.
  + by move=> <- <- ;case:s1.
  + by move=> <- <-;case:s1.
  + by move=> y /(find_label_cat_tl c2) -> <- <- /=;case:s1.
  move=> -[vb lb] -> b /= -> /= ;case:b.
  + by t_xrbindP => pc /(find_label_cat_tl c2) -> <- <- /=;case:s1.
  by move=> [<- <-];case:s1.
Qed.

End Section.

Definition is_jump lbl (i:linstr) :=
 let (ii, ir) := i in
 match ir with
 | Ligoto lbl' => lbl == lbl'
 | Licond _ lbl' => lbl == lbl'
 | _ => false
end.

Lemma find_label_cat_hd lbl c1 c2:
  ~~ has (is_label lbl) c1 ->
  find_label lbl (c1 ++ c2) =
  (Let pc := find_label lbl c2 in ok (size c1 + pc)).
Proof.
  rewrite /find_label find_cat size_cat => /negbTE ->.
  by rewrite ltn_add2l;case:ifP.
Qed.

Definition disjoint_lbl c1 c2 :=
  forall lbl, ~~(has (is_label lbl) c1 && has (is_jump lbl) c2).

Lemma disjoint_lbl_cons i c1 c2:
  disjoint_lbl c1 (i :: c2) -> disjoint_lbl c1 c2.
Proof.
  by move=> Hd lbl;apply: contra (Hd lbl)=> /= /andP[]->->;rewrite orbC.
Qed.

Definition add_hd_c c s := {| lmem := lmem s; lvm := lvm s; lc := c ++ s.(lc); lpc := size c + s.(lpc) |}.

Lemma lsem1_lc {LO: LeakOp} gb s1 s2 l1: lsem1 gb s1 l1 s2 -> lc s1 = lc s2.
Proof.
  rewrite /lsem1 /step;case: find_instr => // -[ii [lv o e||l|l|e l]] /=;
    rewrite /eval_instr /=;t_xrbindP.
  + by move=> ?? <-.
  + by move=> <-.
  + by move=> <-.
  + by move=> ?? <-.
  move=> ????;case:ifP => [ ? | ? [<-] //].
  by t_xrbindP => ?? <-.
Qed.

Lemma find_instr_add_hd_c c s : find_instr (add_hd_c c s) = find_instr s.
Proof.
  rewrite /find_instr /add_hd_c /= !oseq.onth_nth map_cat nth_cat size_map.
  rewrite ltnNge leq_addr /=;f_equal;rewrite -minusE -plusE; omega.
Qed.

Lemma to_estate_add_hd_c c s : to_estate (add_hd_c c s) = to_estate s.
Proof. by case: s. Qed.

Lemma find_instr_has (p:linstr->bool) s i :
  find_instr s = Some i -> p i -> has p (lc s).
Proof.
  rewrite /find_instr => /(oseq.onthP i) => /andP [H1 /eqP <-] Hp.
  apply /(has_nthP i);eauto.
Qed.

Lemma lsem_cat_hd {LO: LeakOp} c gd s1 s2 l1:
  disjoint_lbl c s1.(lc) ->
  lsem gd s1 l1 s2 ->
  lsem gd (add_hd_c c s1) l1 (add_hd_c c s2).
Proof.
  move=> Hdisj Hsem; revert Hdisj.
  elim/lsem_ind: Hsem; clear.
  (* reflexive case *)
  + by move=> s1 Hdisjc; apply: tc_refl.
  move=> s1 l1 s2 l2 s3 Hsem1 Hsem Hrec Hdisj.
  move: Hrec;rewrite -(lsem1_lc Hsem1) => /(_ Hdisj); apply: lsem_step.
  move: Hsem1;rewrite /lsem1 /step.
  have Hnext : forall s s1,
    of_estate s (c ++ lc s1) (size c + lpc s1).+1 = add_hd_c c (of_estate s (lc s1) (lpc s1).+1).
  + by move=> s [????];rewrite /of_estate /add_hd_c /= addnS.
  have Hset : forall pc s1,
    setpc (add_hd_c c s1) (size c + pc).+1 = add_hd_c c (setpc s1 pc.+1).
  + by move=> pc [????];rewrite /setpc /add_hd_c /= addnS.
  rewrite find_instr_add_hd_c;case Heq:find_instr => [ [ii [lv o e||l|l|e l]] | //];
    rewrite /eval_instr /= ?to_estate_add_hd_c;t_xrbindP.
  + by move=> ? -> <- <- /=;rewrite Hnext.
  + by move=> <- <-;rewrite Hset.
  + by move=> <- <-;rewrite Hset.
  + move=> pc' Hfind <- <-.
    rewrite find_label_cat_hd ?Hfind /= ? Hset //.
    + by rewrite -addnS !PoszD (GRing.addrC (Posz (size c))) GRing.addrKA.
    by move: (Hdisj l); rewrite /disjoint_lbl (@find_instr_has (is_jump l) _ _ Heq) ?andbT /is_jump.
  move=> -[vb lb] -> b /= -> /=;case:ifPn => Hb.
  + t_xrbindP => n Hfind <- <-.
    rewrite find_label_cat_hd ?Hfind /= ? Hset //.
    + by rewrite -addnS !PoszD (GRing.addrC (Posz (size c))) GRing.addrKA Hb.
    by move: (Hdisj l);rewrite /disjoint_lbl (@find_instr_has (is_jump l) _ _ Heq) ?andbT /is_jump. 
  by move=> [<- <-];rewrite Hset (negbTE Hb).
Qed.

Lemma valid_has c lbl p1 p2 :
  valid p1 p2 c -> has (is_label lbl) c || has (is_jump lbl) c ->
  ((p1 <=? lbl) && (lbl <? p2))%positive.
Proof.
  elim: c => //= i c Hrec /andP[] H /Hrec.
  by case: i H=>[ii [||lbl'|lbl'|e lbl']] //=;
  rewrite {2}/is_label /=; case: eqP=> [->|].
Qed.

Lemma valid_disjoint p1 p2 p3 p4 c1 c2 :
  ((p2 <=? p3) || (p4 <=? p1))%positive ->
  valid p1 p2 c1 ->
  valid p3 p4 c2 ->
  disjoint_lbl c1 c2.
Proof.
  move=> Hp Hv1 Hv2 lbl;apply /negP=>/andP[] H1 H2.
  have := @valid_has _ lbl _ _ Hv1;rewrite H1=> /(_ isT) /andP[]/P_leP ? /P_ltP ?.
  have := @valid_has _ lbl _ _ Hv2;rewrite H2 orbT => /(_ isT) /andP[]/P_leP ? /P_ltP ?.
  case/orP: Hp => /P_leP ?;omega.
Qed.

Lemma disjoint_cat_l c1 c2 c :
  disjoint_lbl (c1++c2) c <-> (disjoint_lbl c1 c /\ disjoint_lbl c2 c).
Proof.
  rewrite /disjoint_lbl;split.
  + move=> H1;split=> lbl;have := H1 lbl;rewrite has_cat;apply contra=>/andP[]->->//.
    by rewrite orbC.
  move=> [H1 H2] lbl;rewrite has_cat;apply /negP => /andP[]/orP []H H'.
  + by move: (H1 lbl);rewrite H H'.
  by move: (H2 lbl);rewrite H H'.
Qed.

Lemma disjoint_cat_r c1 c2 c :
  disjoint_lbl c (c1++c2) <-> (disjoint_lbl c c1 /\ disjoint_lbl c c2).
Proof.
  rewrite /disjoint_lbl;split.
  + move=> H1;split=> lbl;have := H1 lbl;rewrite has_cat;apply contra=>/andP[]->->//.
    by rewrite orbC.
  move=> [H1 H2] lbl;rewrite has_cat;apply /negP => /andP[] H /orP[]H'.
  + by move: (H1 lbl);rewrite H H'.
  by move: (H2 lbl);rewrite H H'.
Qed.

(** need to make proof shorter *)
Lemma snot_spec {LO: LeakOp} gd s e b le pstk:
  let r := (snot e) in
  sem_pexpr gd s e = ok (Vbool b, le) →
  sem_pexpr gd s r.1 = ok(Vbool (negb b), leak_E pstk r.2 le).
Proof.
elim: e b le=> //=; try auto.
(* Pbool *)
- by move=> b b0 le [] <- <-.
(* Pvar *)
- by move=> x b le; t_xrbindP=> vg -> -> <- /=.
(* Pglobal *)
- by move=> g b le; t_xrbindP=> vg -> -> <- /=.
(* Pget *)
- move=> sz x e He b le /=. 
  apply: on_arr_varP => n t Hsub; rewrite /on_arr_var => -> /=; t_xrbindP.
  move=> [v l] -> /= z -> sz' /= -> /= //=.
(* Pload *)
- move=> sz x e He b le /=. t_xrbindP. 
  move=> u v -> hp [v' l'] -> u' /= hp' sz' hm /=.
  move=> //=. 
(* Papp1 *)
- case=> // sz e //=.
  (* op = Oword_of_int *)
  + t_xrbindP. move=> He b le. rewrite /sem_sop1 /=.
    move=> [v l] -> /= vo. t_xrbindP. move=> z -> <- //=.
  (* op = Oint_of_word *)
  + t_xrbindP. move=> He b le. rewrite /sem_sop1 /=.
    move=> [v l] -> /= vo. t_xrbindP. move=> z hi <- //=.
  (* op = Osignnext *)
  + move=> e' He. rewrite /sem_sop1 /=.
    move=> b' le. t_xrbindP. move=>[v l] -> /= vo we -> //= <- //=. 
  (* op = Ozeronext *)
  + t_xrbindP. move=> e' He. rewrite /sem_sop1 /=.
    move=> b' le [v l] -> /= vo. t_xrbindP. move=> z -> <- //=.
  (* op = Onot *)
  + t_xrbindP. rewrite /sem_sop1 /=.
    move=> b le [v l] -> /= vo. t_xrbindP=> vb /to_boolI //= -> <- lo Hlo [] <- <- //=. by rewrite negbK.
  (* op = Olnot *)
  + t_xrbindP. move=> He b le. rewrite /sem_sop1 /=.
    move=> [v l] -> /= vo. t_xrbindP. by move=> z -> <- //=.
  (* op = Oneg *)
  by t_xrbindP; move=> He b le [v l] -> vo /= -> //= lo -> -> <- /=.
(* Papp2 *)
- case=> //=.
  + move=> e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo.
    move=>/sem_sop2I [b1 [b2 [b3]]] [] /to_boolI /= hb1 /to_boolI /= hb2 [h] h' lo Hlo h'' <- /=.
    rewrite hb1 in h1. rewrite hb2 in h2. move: (He1 b1 l1 h1). move=> -> /=.
    move: (He2 b2 l2 h2). move=> -> /=; apply: (f_equal (@Ok _ _)); rewrite /= ?negb_and ?negb_or /=.
    rewrite h'' in h'. case: h'=> h1'. rewrite -h1' in h. rewrite -h /= negb_and. auto.
    rewrite /leak_sop2 in Hlo. move: Hlo. by t_xrbindP=> st /= Hb b' Hb' [] <-.
  + move=> e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo.
    move=>/sem_sop2I [b1 [b2 [b3]]] [] /to_boolI /= hb1 /to_boolI /= hb2 [h] h' lo Hlo h'' <- /=.
    rewrite hb1 in h1. rewrite hb2 in h2. move: (He1 b1 l1 h1). move=> -> /=.
    move: (He2 b2 l2 h2). move=> -> /=; apply: (f_equal (@Ok _ _)); rewrite /= ?negb_and ?negb_or /=.
    rewrite h'' in h'. case: h'=> h1'. rewrite -h1' in h. rewrite -h /= negb_or. auto.
    rewrite /leak_sop2 in Hlo. move: Hlo. by t_xrbindP=> st /= Hb b' Hb' [] <-.
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo /= hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb /=. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o e1 He1 e2 He2 b le /=; t_xrbindP. 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=. rewrite h1 /= h2 /= ho /=.
    by rewrite /sem_sop1 /= Hlo hb. 
  + move=> o o' e1 He1 e2 He2 b le /=; t_xrbindP;
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=; rewrite h1 /= h2 /= ho /=;
    by rewrite /sem_sop1 /= Hlo hb.
  + move=> o o' e1 He1 e2 He2 b le /=; t_xrbindP; 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=; rewrite h1 /= h2 /= ho /=;
    by rewrite /sem_sop1 /= Hlo hb.
  + move=> o o' e1 He1 e2 He2 b le /=; t_xrbindP; 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=; rewrite h1 /= h2 /= ho /=;
    by rewrite /sem_sop1 /= Hlo hb.
  + move=> o o' e1 He1 e2 He2 b le /=; t_xrbindP; 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=; rewrite h1 /= h2 /= ho /=;
    by rewrite /sem_sop1 /= Hlo hb /=.
  + move=> o o' e1 He1 e2 He2 b le /=; t_xrbindP; 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=; rewrite h1 /= h2 /= ho /=;
    by rewrite /sem_sop1 /= Hlo hb /=.
  + move=> o o' e1 He1 e2 He2 b le /=; t_xrbindP; 
    move=>[v1 l1] h1 [v2 l2] h2; move=> vo //= ho lo Hlo hb <- /=; rewrite h1 /= h2 /= ho /=;
    by rewrite /sem_sop1 /= Hlo hb.
(* PopN *)
- move=> op es He b le. t_xrbindP.
  move=> vs -> vo ho lo Hlo hb <- /=. rewrite ho /=. by rewrite /sem_sop1 /= Hlo hb /=.
(* Pif *)
move => st p hp e1 he1 e2 he2 b l /=.
t_xrbindP => -[vp lp] -> /= bp -> /= [v1 l1] h1 [v2 l2] h2 trv1 htr1 trv2 htr2 /= h <-.
have : exists (b1 b2:bool), st = sbool /\ sem_pexpr gd s e1 = ok (Vbool b1, l1) /\ sem_pexpr gd s e2 = ok (Vbool b2, l2).
+ rewrite h1 h2;case: bp h => ?;subst.
  + have [h /= h']:= truncate_val_boolI htr1; subst st v1.
    by move: htr2; rewrite /truncate_val; t_xrbindP => /= b2 /to_boolI -> ?;eauto.
  have [h /= h']:= truncate_val_boolI htr2;subst st v2.
  by move: htr1; rewrite /truncate_val; t_xrbindP => /= b1 /to_boolI -> ?;eauto.
move=> [b1 [b2 [-> []/dup[]hb1 /he1 -> /dup[]hb2 /he2 ->]]] /=.
rewrite hb1 in h1. rewrite hb2 in h2. case: h1=> h11. case: h2=> h12. rewrite -h11 in htr1.
rewrite /= in htr1. rewrite -h12 in htr2. rewrite /= in htr2.
move: truncate_val_bool. move=> Ht. move: (Ht st b1 trv1 htr1). move=> [] _ hbb.
move: (Ht st b2 trv2 htr2). move=> [] _ hbb'. rewrite hbb in h. rewrite hbb' in h.
case: bp h => //=. by move=> [] ->. by move=> [] ->.
Qed.

Lemma lsem_add_align {LO: LeakOp} gd s c ii a s' li :
  lsem gd (of_estate s c 0) li (of_estate s' c (size c)) ->
  lsem gd (of_estate s (add_align ii a c) 0) (get_align_leak_il a ++ li)  
  (of_estate s' (add_align ii a c) (size (add_align ii a c))).
Proof.
  rewrite /add_align;case: a s s' => -[] m vm [] m' vm' h //.
  apply: lsem_step. constructor.
  by apply: (lsem_cat_hd (c:=[::{| li_ii := ii; li_i := Lialign |}]) _ h).
Qed.

Lemma add_align_nil ii a c : add_align ii a c = add_align ii a [::] ++ c.
Proof. by case: a. Qed.

Lemma find_label_add_align lbl ii a c :
  find_label lbl (add_align ii a c) =
  Let n := find_label lbl c in ok ((a == Align) + n).
Proof.
  case: a => /=;last by case: find_label.
  by rewrite /add_align -cat1s find_label_cat_hd.
Qed.

Section Linear_size.
Let Pi i := 
  forall lbl lbl' lc lc' ltc, 
    linear_i i lbl lc = ok (lbl', lc', ltc) ->
     size lc' = get_linear_size ltc + size lc.
Let Pr i := forall ii, Pi (MkI ii i).

Let Pc c := 
  forall lbl lbl' lc lc' ltc,
    linear_c linear_i c lbl lc = ok (lbl', lc', ltc) ->
    size lc' = get_linear_size_C ltc + size lc.

Local Lemma hmk i ii : Pr i → Pi (MkI ii i).
Proof. done. Qed.

Local Lemma hnil : Pc [::].
Proof. by move=> lbl lbl' lc lc' ltc /= [] _ <- <-. Qed.

Local Lemma hcons i c : Pi i → Pc c → Pc (i :: c).
Proof. 
  move=> hreci hrec lbl lbl' lc lc' ltc /=.
  t_xrbindP => -[[lbl1 lc1] ltc1] /hrec hlc1 [[lbl2 lc2] ltc2] /hreci /= hlc2 [] _ <- <-.
  by rewrite /= hlc2 hlc1 addnA.
Qed.

Local Lemma hassgn x tg ty e : Pr (Cassgn x tg ty e).
Proof. by move=> ii lbl lbl' lc lc' ltc /=; case: ty => // w [] _ <- <-. Qed.

Local Lemma hopn xs t o es : Pr (Copn xs t o es).
Proof. by move=> ii lbl lbl' lc lc' ltc /= [] _ <- <-. Qed.

Local Lemma hif e c1 c2 : Pc c1 → Pc c2 → Pr (Cif e c1 c2).
Proof.
  move=> hrec1 hrec2 ii lbl lbl' lc lc' ltc /=.
  case: c1 hrec1 => [ | i c1] hrec1.
  + t_xrbindP => -[[lbl1 lc1] ltc1] [[lbl2 lc2] ltc2] /= /hrec2 hlc2 [] _ <- <- [] _ <- <-.
    by rewrite /= hlc2 /= /get_linear_size_C; ring. 
  move: (i::c1) hrec1 => {i c1} c1 hrec1.
  case: c2 hrec2 => [ | i c2] hrec2.
  + t_xrbindP => -[[lbl1 lc1] ltc1] [[lbl2 lc2] ltc2] /= /hrec1 hlc1 [] _ <- <- [] _ <- <-.
    by rewrite /= hlc1 /= /get_linear_size_C; ring. 
  move: (i::c2) hrec2 => {i c2} c2 hrec2.
  t_xrbindP =>  -[[lbl1 lc1] ltc1] [[lbl2 lc2] ltc2] [[lbl3 lc3] ltc3] /hrec1 hlc1 /= [] _ <- <-.
  move=> [] _ <- <- [[lbl4 lc4] ltc4] [[lbl5 lc5] ltc5] /hrec2 hlc2 /= [] _ <- <- _ <- <-.
  rewrite /= hlc2 /= hlc1 /= /get_linear_size_C; ring.
Qed.

Local Lemma hfor v dir lo hi c :  Pc c → Pr (Cfor v (dir, lo, hi) c).
Proof. done. Qed.

Local Lemma hwhile a c e c' : Pc c → Pc c' → Pr (Cwhile a c e c').
Proof.
  move=> hrec1 hrec2 ii lbl lbl' lc lc' ltc /=.
  have h : 
    match c' with
    | [::] =>
        Let rs
        := align ii a
             ({| li_ii := ii; li_i := Lilabel lbl |} >;
              linear_c linear_i c (next_lbl lbl) ({| li_ii := ii; li_i := Licond e lbl |} :: lc))
        in ciok (rs.1.1, rs.1.2, LT_ilwhile_c'0 a rs.2)
    | _ :: _ =>
        Let rs1
        := {| li_ii := ii; li_i := Lilabel lbl |} >;
           linear_c linear_i c (next_lbl (next_lbl lbl))
             ({| li_ii := ii; li_i := Licond e (next_lbl lbl) |} :: lc)
        in (Let rs
            := {| li_ii := ii; li_i := Ligoto lbl |} >;
               align ii a
                 ({| li_ii := ii; li_i := Lilabel (next_lbl lbl) |} >; linear_c linear_i c' rs1.1.1 rs1.1.2)
            in ciok (rs.1.1, rs.1.2, LT_ilwhile a rs1.2 rs.2))
    end = ok (lbl', lc', ltc) → size lc' = get_linear_size ltc + size lc.
  + case: c' hrec2 => [ | i c'] hrec2.
    + rewrite /align; t_xrbindP => -[[lbl1 lc1] ltc1] [[lbl2 lc2] ltc2] [[lbl3 lc3] ltc3] /=.
      move=> /hrec1 hlc1 [] _ <- <- [] _ <- <- [] _ <- <- /=.
      by case: a => /=; rewrite hlc1 /= /get_linear_size_C; ring.
    move: (i::c') hrec2 => {i c'} c' hrec2.
    rewrite /align; t_xrbindP => -[[lbl1 lc1] ltc1] [[lbl2 lc2] ltc2] /hrec1 hlc1 [] _ <- <-.
    move=> [[lbl3 lc3] ltc3] [[lbl4 lc4] ltc4] [[lbl5 lc5] ltc5] [[lbl6 lc6] ltc6] /hrec2 hlc2 /=.
    move=> [] _ <- <- [] _ <- <- [] _ <- <- [] _ <- <- /=.
    by case: a => /=; rewrite hlc2 /= hlc1 /= /get_linear_size_C; ring.
  case: (is_bool e) => // -[] //.
  by t_xrbindP => -[[lbl1 lc1] ltc1] /hrec1 hlc1 [] _ <- <-.
Qed.

Lemma hcall i xs f es : Pr (Ccall i xs f es).
Proof. done. Qed.

Lemma linear_size c lbl lbl' lc ltc : 
  linear_c linear_i c lbl [::] = ok (lbl', lc, ltc) ->
  size lc = get_linear_size_C ltc.
Proof. by move=> /(cmd_rect hmk hnil hcons hassgn hopn hif hfor hwhile hcall) ->; rewrite /= addn0. Qed.

End Linear_size.

Section PROOF.

  Variable p:  sprog.
  Context {LO: LeakOp}.
  Context (gd: glob_decls).
  Variable p': lprog.
  Variable stk : pointer.
  Variable Fs : seq(funname * seq leak_i_il_tr).
  Hypothesis linear_ok : linear_prog p = ok (p', Fs).

  Let Pi (i:instr) :=
    forall lbl lbli li lti, linear_i i lbl [::] = ok (lbli, li, lti) ->
    [/\ (lbl <=? lbli)%positive,
     valid lbl lbli li &
     forall s1 s2 l, S.sem_I p gd s1 i l s2 ->
     leak_i_WF lti l /\
     lsem gd (of_estate s1 li 0) (leak_i_iL stk l lti) (of_estate s2 li (size li))].

  Let Pi_r (i:instr_r) :=
    forall ii lbl lbli li lti, linear_i (MkI ii i) lbl [::] = ok (lbli, li, lti) ->
    [/\ (lbl <=? lbli)%positive,
     valid lbl lbli li &
     forall s1 s2 l, S.sem_i p gd s1 i l s2 ->
       leak_i_WF lti l /\
       lsem gd (of_estate s1 li 0) (leak_i_iL stk l lti) (of_estate s2 li (size li))].

  Let Pc (c:cmd) :=
    forall lbl lblc lc ltc, linear_c linear_i c lbl [::] = ok (lblc, lc, ltc) ->
    [/\ (lbl <=? lblc)%positive,
     valid lbl lblc lc &
     forall s1 s2 l, S.sem p gd s1 c l s2 ->
      leak_is_WF ltc l /\
       lsem gd (of_estate s1 lc 0) (leak_i_iLs (leak_i_iL) stk ltc l) (of_estate s2 lc (size lc))].

  Let HmkI : forall i ii, Pi_r i -> Pi (MkI ii i).
  Proof.
    move=> i ii Hi_r lbl lbli li lti Hli.
    move: Hi_r=> /(_ ii lbl lbli li lti Hli) [H1 H2 H3]; split=> //.
    move=> s1 s2 l /S.sem_IE; apply H3.
  Qed.

  Let Hskip : Pc [::].
  Proof.
    move=> lbl lbli li ltc /= [] <- <- <-;split=> //. apply Pos.leb_refl.
    move=> s1 s2 l /S.semE [] -> ->; split. constructor.
    apply tc_refl.
  Qed.

  Lemma of_estate_add_hd_c s li lc pc:
    add_hd_c li (of_estate s lc pc) = of_estate s (li ++ lc) (size li + pc).
  Proof. done. Qed.

  Let Hseq : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc lbl lbl' l ltc /=.
    case Heqc : linear_c => [[[lblc lc] ltc']|] //=.
    rewrite /Pc in Hc. move: (Hc lbl lblc lc ltc' Heqc).
    move=> {Hc} [] Hle1 Hvc Hc.
    rewrite linear_i_nil.
    case Heqi: linear_i => [[[lbli li] lti]|] //= [] h1 h2 h3 ;subst lbl' l ltc.
    rewrite /Pi in Hi. move: (Hi lblc lbli li lti Heqi).
    move=> {Hi} [] Hle2 Hvi Hi; split.
    + by apply /P_leP;move/P_leP: Hle1;move/P_leP: Hle2=> ??;omega.
    + by rewrite valid_cat (valid_le_min Hle1 Hvi) (valid_le_max Hle2 Hvc).
    move=> -[m1 vm1] s2 l /S.semE [[m2 vm2]] [li'] [lc'] [] Hi' Hc' ->.
    rewrite /lsem /=.
    case: (Hi _ _ _ Hi') => {Hi} hwf Hi; case: (Hc _ _ _ Hc') => {Hc} Hwfc Hc; split.
    + by constructor.
    apply tc_trans  with (of_estate {| emem := m2; evm := vm2 |} (li++lc) (size li)).
    + by apply (lsem_cat_tl lc Hi).
    have Hvc1 : valid 1 lblc lc.
    apply: valid_le_min Hvc.
    + by rewrite /is_true Pos.leb_le;apply Pos.le_1_l.
    have /(@lsem_cat_hd LO li) := Hc.
    rewrite !of_estate_add_hd_c size_cat addn0;apply.
    by apply: valid_disjoint Hvi Hvc;rewrite Pos.leb_refl orbC.
  Qed.
    
  Lemma to_of_estate s c pc : to_estate (of_estate s c pc) = s.
  Proof. by case: s. Qed.

  Let Hassgn : forall x tag ty e, Pi_r (Cassgn x tag ty e).
  Proof.
    move=> x tag [] // sz e ii lbl lbl' l ltc /= [] <- <- <-;rewrite Pos.leb_refl; split => //.
    move=> -[m1 vm1] s2 l' /S.sem_iE' [v] [v'] [le] [lw] [ok_v].
    apply: rbindP => w /of_val_word [sz'] [w'] [hle h1 h2]; subst v w => - [<-] {v'} ok_s2 ->.
    split; first by constructor.
    rewrite /lsem /=. apply tc_step. rewrite /lsem1 /step /= /eval_instr /= !to_of_estate.
    case: ifP => hsz.
    + by rewrite /sem_sopn /sem_pexprs /= /exec_sopn /sopn_sem /= ok_v /= 
      /truncate_word hle /x86_MOV /check_size_8_64 hsz /= /leak_sopn /= /sopn_leak /=
      /truncate_word /= hle /= ok_s2 /=.
    by rewrite /sem_sopn /= /exec_sopn /sopn_sem /= ok_v /= /truncate_word hle /=
    /x86_VMOVDQU (wsize_nle_u64_check_128_256 hsz) /= /leak_sopn /= /sopn_leak /=
    /truncate_word /= hle /= ok_s2 /=. 
  Qed.

  Let Hopn : forall xs t o es, Pi_r (Copn xs t o es).
  Proof.
    move=> x t' e tag ii lbl lbl' l' lti [] <- <- <-;rewrite Pos.leb_refl;split=>//.
    move=> -[m1 vm1] s2 l /S.sem_iE' [] lo [] ok_s2 ->; split; first by constructor.
    rewrite /lsem. apply tc_step.
    by rewrite /lsem1 /step /= /eval_instr /= !to_of_estate /= ok_s2 /=.
  Qed.

  Lemma find_label_hd lbl ii c :
    find_label lbl ({|li_ii:= ii; li_i := Lilabel lbl|} :: c ) = ok 0.
  Proof. by rewrite /find_label /= /is_label /= eqxx. Qed.

  Lemma setc_of_estate s c pc c' :setc (of_estate s c pc) c' = of_estate s c' pc.
  Proof. done. Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi_r (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 ii lbl lbl' l' lti /=.
    case Heq1: (c1)=> [|i1 l1].
    (* case1: Cif e [::] c2 *) 
    + subst;rewrite linear_c_nil;case Heq: linear_c => [[[lbl2 lc2] ltc2]|] //= [] <- <- <-.
      have Hlen := le_next lbl.
      have [Hle Hv2 Hs2]:= Hc2 _ _ _ _ Heq;split.
      + by apply: Pos_leb_trans Hle.
      + rewrite /= valid_cat Pos.leb_refl (valid_le_min Hlen Hv2) /= Pos.leb_refl.
        by rewrite (Pos_lt_leb_trans (lt_next _) Hle).
      move => [m1 vm1] s2 l /S.sem_iE' [b] [le] [lc] [ok_b ok_s2] ->.
      case: b ok_b ok_s2 => ok_b.
      - move => /S.semE [] -> -> {s2}. 
        split; first by constructor.
        apply: lsem_step.
        * rewrite /lsem1 /step /= /eval_instr /= !to_of_estate ok_b {ok_b} /=.
          rewrite -cat_cons find_label_cat_hd.
          + by rewrite find_label_hd /= GRing.subr0 addn0 -PoszD -(linear_size Heq) addnC.
          apply /negP => /= H; have := @valid_has _ lbl _ _ Hv2.
          rewrite H => /(_ erefl) /andP [].
          by rewrite Pos.leb_antisym lt_next.
        rewrite /= size_cat /= addn1; exact: tc_refl.
      move => ok_s2.
      case: (Hs2 _ _ _ ok_s2) => hwf {Hs2} Hs2; split; first by constructor.
      apply: lsem_step.
      + by rewrite /lsem1 /step /= /eval_instr /= ?to_of_estate ok_b {ok_b} /=.
      have Hvc : valid lbl (next_lbl lbl) [:: MkLI ii (Licond e lbl)].
      + by rewrite /= Pos.leb_refl lt_next.
      have Hd: disjoint_lbl [:: MkLI ii (Licond e lbl)] lc2 by move=> ?.
      have /(@lsem_cat_tl LO [:: MkLI ii (Lilabel lbl)]):=
         @lsem_cat_hd LO [:: MkLI ii (Licond e lbl)] _ _ _ _ Hd Hs2.
      rewrite !of_estate_add_hd_c !addn0 /= => Hsem.
      apply (tc_trans Hsem) => {Hsem}.
      apply tc_step; rewrite /lsem1 /step /= /setc /find_instr /= onth_cat ltnn subnn /=.
      by rewrite /eval_instr /= size_cat /= addn1.
    rewrite -Heq1 => {Heq1 l1 i1};case Heq2: c2 => [|i2 l2].
    (* case 2: Cif e c1 [::] *)
    + subst; rewrite linear_c_nil; case Heq: linear_c=> [[[lbl1 lc1] ltc1]|] //= [] <- <- <-.
      have Hlen := le_next lbl.
      have [Hle Hv1 Hs1]:= Hc1 _ _ _ _ Heq;split.
      + by apply: Pos_leb_trans Hle.
      rewrite /= valid_cat Pos.leb_refl (valid_le_min Hlen Hv1) /= Pos.leb_refl.
      by rewrite (Pos_lt_leb_trans (lt_next _) Hle).
      case => m1 vm1 s2 l /S.sem_iE' [b] [le] [lc]; case: b => ok_b.
      case: ok_b.
      (* true case *)
      + move => ok_e /Hs1 [] Hwf{Hs1}Hs1 ->; split; first by constructor.
        apply: lsem_step.
        + rewrite /lsem1 /step /= /eval_instr /= ?to_of_estate. 
          have /(_ LO) /= Hsnot := snot_spec. 
          move: (Hsnot gd {| emem := m1; evm := vm1 |} e true le stk ok_e). move=> {Hsnot} -> /=.
          by rewrite /setpc /=. 
        + have Hvc : valid lbl (next_lbl lbl) [:: MkLI ii (Licond (Papp1 Onot e) lbl)].
          + by rewrite /= Pos.leb_refl lt_next.
          have Hd: disjoint_lbl [:: MkLI ii (Licond (snot e).1 lbl)] lc1 by move=> ?.
          have := @lsem_cat_hd LO [:: MkLI ii (Licond (snot e).1 lbl)] _ _ _ _ Hd Hs1.
          move=> /(@lsem_cat_tl LO [:: MkLI ii (Lilabel lbl)]) Hsem.
          eapply tc_trans. apply Hsem;case s2 => m2 vm2.
          apply tc_step.
          rewrite /lsem1 /step /setc /find_instr /= onth_cat ltnn subnn /=.
          by rewrite /eval_instr /= size_cat /= addn1.
      (* false case *)
      case: ok_b. move=> ok_e /S.semE [] -> -> -> /=.
      split; first by constructor.
      apply: lsem_step.
      + rewrite /lsem1 /step /= /eval_instr /= ?to_of_estate. 
        have /(_ LO) /= Hsnot := snot_spec. 
        move: (Hsnot gd {| emem := m1; evm := vm1 |} e false le stk ok_e). 
        move=> {Hsnot} -> /=. 
        rewrite -cat_cons find_label_cat_hd.
        + by rewrite find_label_hd /= addn0 GRing.subr0 -(linear_size Heq) -PoszD addnC.
        apply /negP => /= H. have := @valid_has _ lbl _ _ Hv1.
        rewrite H => /(_ erefl) /andP [].
        by rewrite Pos.leb_antisym lt_next.
      rewrite /= size_cat /= addn1;exact: tc_refl.
    (* case 3: Cif e c1 c2 *)
    rewrite -Heq2 => {Heq2 l2 i2}.
    rewrite linear_c_nil;case Heq1: linear_c => [[[lbl1 lc1] ltc1]|] //=.
    rewrite linear_c_nil;case Heq2: linear_c => [[[lbl2 lc2] ltc2]|] //= [] <- <- <-.
    have leL1 := le_next lbl; have leL2 := le_next (next_lbl lbl).
    have [Hle1 Hv1 Hs1]:= Hc1 _ _ _ _ Heq1;have [Hle2 Hv2 Hs2]:= Hc2 _ _ _ _ Heq2.
    have L2lbl2 := Pos_leb_trans Hle1 Hle2.
    have L1lbl2 := Pos_leb_trans leL2 L2lbl2.

    have lblL2 := Pos_leb_trans leL1 leL2.
    have lbllbl1 := Pos_leb_trans lblL2 Hle1;split.
    + by apply: Pos_leb_trans Hle2.
    + rewrite /= valid_cat /= valid_cat /=.
      rewrite Pos.leb_refl leL1 (Pos_lt_leb_trans (lt_next lbl) L1lbl2).
      rewrite (Pos_lt_leb_trans (lt_next _) L2lbl2).
      by rewrite (valid_le_min _ Hv2) // (valid_le_max Hle2 (valid_le_min lblL2 Hv1)).
    move=> [m1 vm1] s2 l /S.sem_iE' [b] [lc] [lc'] [].
    set C := (C in of_estate _ C _); rewrite -/C.
    case: b => ok_b. 
    + move=> /Hs1{Hs1}[] Hwf Hs1 ->; split; first by constructor.
      apply lsem_step with (of_estate {| emem := m1; evm := vm1 |} C ((size lc2) .+3)).
      + rewrite /lsem1 /step /= /eval_instr /=  ?to_of_estate ok_b /=.
        rewrite /C -cat_cons -cat_rcons find_label_cat_hd.
        + by rewrite find_label_hd size_rcons /= addn0 GRing.subr0 -PoszD addnC -(linear_size Heq2).
        rewrite has_rcons /=; apply /negP => H; have := @valid_has _ lbl _ _ Hv2. rewrite H=> /(_ isT) /andP[].
        have Hlt := Pos_leb_trans leL2 Hle1.
        by rewrite Pos.leb_antisym (Pos_lt_leb_trans(lt_next _)(Pos_leb_trans leL2 Hle1)).
      have Hd:
        disjoint_lbl ([:: MkLI ii (Licond e lbl)]++lc2++[:: MkLI ii (Ligoto (next_lbl lbl)); MkLI ii (Lilabel lbl)]) lc1.
      + rewrite !disjoint_cat_l;split;first by move=> ?.
        split;first by apply: valid_disjoint Hv2 Hv1;rewrite Pos.leb_refl orbC.
        move=> lbl0 /=;rewrite orbF /is_label /=;case:eqP=> //= ?;subst lbl0.
        apply /negP => H; have := @valid_has _ lbl _ _ Hv1;rewrite H orbT.
        move=> /(_ isT) /andP[];rewrite Pos.leb_antisym.
        by rewrite (Pos_lt_leb_trans (lt_next _) leL2).
      have /(_ _ Hd) := lsem_cat_hd _ Hs1.
      rewrite !of_estate_add_hd_c /=.
      move=> /(@lsem_cat_tl LO [:: MkLI ii (Lilabel (next_lbl lbl))]) /=.
      rewrite !setc_of_estate addn0 size_cat /= addn2 /C -!catA /= => Hsem.
      eapply tc_trans. apply Hsem. apply tc_step.
      rewrite /lsem1 /step /setc /find_instr /= onth_cat.
      have -> : ((size lc2 + size lc1)%Nrec.+2 < size lc2) = false.
      + by apply negbTE;apply /ltP;rewrite -addnE -plusE;omega.
      have -> /= : (size lc2 + size lc1)%Nrec.+2 - size lc2 = (size lc1).+2.
      + by rewrite -addnE -minusE -plusE;omega.
      rewrite onth_cat ltnn subnn /= size_cat /= size_cat /eval_instr /=.
      by rewrite !addSn !addnS addn0.
    move=> /Hs2{Hs2}[] Hwf Hs2 ->; split; first by constructor.
    apply lsem_step with (of_estate {| emem := m1; evm := vm1 |} C 1).
    + by rewrite /lsem1 /step /= /eval_instr /= ?to_of_estate ok_b /=.
    apply tc_trans with (of_estate s2 C (size lc2).+1).
    + move: Hs2. 
      move=> /(@lsem_cat_tl LO [:: MkLI ii (Ligoto (next_lbl lbl)), MkLI ii (Lilabel lbl) & lc1 ++ [:: MkLI ii (Lilabel (next_lbl lbl))]]) /= H.
      by have /= /(_ [:: MkLI ii (Licond e lbl)]) H0 := lsem_cat_hd _ H; apply H0.
    apply tc_step.
    rewrite /lsem1 /step /= /C /find_instr /= onth_cat ltnn subnn /eval_instr /=.
    rewrite -cat_cons -2!cat_rcons catA find_label_cat_hd.
    + rewrite find_label_hd /= !size_cat /= !size_rcons size_cat /= !addn0.
      rewrite !(addSn, addnS) addn0 -addn4 - addn1 -addnA (addnC (size lc2) (_ + _)) !PoszD GRing.addrKA.
      by rewrite -GRing.addrA -!PoszD -(linear_size Heq1).
    rewrite has_cat !has_rcons /=.
    rewrite {1}/is_label /=.
    case: eqP => Heq /=.
    + by have := lt_next lbl;rewrite Pos.ltb_antisym Heq Pos.leb_refl.
    apply /negP => /orP [] H.
    + have := @valid_has _ (next_lbl lbl) _ _ Hv2.
      by rewrite H Pos.leb_antisym (Pos_lt_leb_trans (lt_next _) Hle1) /= => /(_ isT).
    have := @valid_has _ (next_lbl lbl) _ _ Hv1.
    by rewrite H Pos.leb_antisym lt_next /= => /(_ isT).
  Qed.

  Let Hfor : forall v dir lo hi c, Pc c -> Pi_r (Cfor v (dir, lo, hi) c).
  Proof. by []. Qed.

  Lemma lc_of_estate s lc pc : linear_sem.lc (of_estate s lc pc) = lc.
  Proof. by case: s. Qed.

  Lemma setpc_of_estate s C pc pc' : setpc (of_estate s C pc) pc' = of_estate s C pc'.
  Proof. done. Qed.

  Lemma leak_i_iL_while_c'0 a lti li: 
    leak_i_iL stk li (LT_ilwhile_c'0 a lti) = get_align_leak_il a ++ [:: Lempty0 & ilwhile_c'0 leak_i_iL stk lti li].
  Proof.
  by case: li=> //=.
  Qed.

  Lemma leak_i_il_il_while a lti lti' li : leak_i_iL stk li (LT_ilwhile a lti lti') = 
  [:: Lempty (Posz (get_linear_size_C lti' + (get_align_size a + 3)))] ++ ilwhile leak_i_iL stk lti lti' li.
  Proof. by case: li. Qed.

  Let Hwhile : forall a c e c', Pc c -> Pc c' -> Pi_r (Cwhile a c e c').
  Proof.
    move=> a c e c' Hc Hc' ii lbl lbli li lti /=.
    set ι := MkLI ii.
    case: is_boolP => [[] | {e} e].
    + case: c' Hc' => [ _ | i c' ].
    (* c' is [::]*)
    (* when c' = [::] *)
    (* align; Lilabel L1; c ; Licond e L1 *)
    (* Depending on e we will repeat c till e becomes false *)
    + rewrite linear_c_nil;case Heqc: linear_c => [[[lblc lc] ltc']|] //= x; apply ok_inj in x.
      case/xseq.pair_inj: x => h1 <-; case: h1=> h1' h1''; subst lbli li.
      have {Hc}[Hle1 Hvc Hc]:= Hc _ _ _ _ Heqc.
      have leL1 := le_next lbl.
      have ltL1 := lt_next lbl.
      have Hle2 := Pos_leb_trans leL1 Hle1.
      have Hlt := Pos_lt_leb_trans ltL1 Hle1.
      split => //.
      + by rewrite valid_add_align /= valid_cat /= Pos.leb_refl Hlt (valid_le_min _ Hvc).
      move=> s1 s2 li H; rewrite leak_i_iL_while_c'0 /=.
      suff : leak_w0_WF ltc' li /\ 
         @lsem LO gd
          (setpc (of_estate s1 (ι (Lilabel lbl) :: lc ++ [:: ι (Licond true lbl)]) 0)
          (lpc (of_estate s1 (ι (Lilabel lbl) :: lc ++ [:: ι (Licond true lbl)]) 0)).+1)
          (@ilwhile_c'0 (@leak_i_iL LO) LO stk ltc' li)
          (of_estate s2 (ι (Lilabel lbl) :: lc ++ [:: ι (Licond true lbl)])
          (size (ι (Lilabel lbl) :: lc ++ [:: ι (Licond true lbl)]))).
      + move=> [??]; split; first by constructor.
        by apply: lsem_add_align; apply: lsem_step=> //.
      set L := [:: ι (Lilabel lbl) ].
      set C := L ++ lc ++ [:: ι (Licond e lbl)].
      have HL : valid lbl (next_lbl lbl) L by rewrite/L/= Pos.leb_refl ltL1.
      have Hd : disjoint_lbl L lc by apply: valid_disjoint _ HL Hvc; rewrite Pos.leb_refl.
      elim: _ {-1} _ _ _ / H (erefl (Cwhile a c true [::])) => // { s1 s2}.
      + move=> s1 s2 s3 s4 a' c0 e0 c' lc0 le lc' lw Hsem He Hsem' Hs IH.
        move=> [] h1 h2 h3 h4; subst a c0 e0 c'. 
        specialize (IH (erefl _)).
        specialize (Hc _ _ _ Hsem); case: IH Hc => Hwf IH [] Hwfc Hc; split; first by constructor. 
        move: Hsem' => /S.semE [] hs hl; subst.
        apply tc_trans with {|
          lmem := emem s2;
          lvm := evm s2;
          lc := ι (Lilabel lbl) :: lc ++ [:: ι (Licond true lbl)];
          lpc := 1 + size lc |}.
        + have /(_ LO) Hhd := lsem_cat_hd. 
          have /= {Hhd} Hhd := (Hhd L gd (of_estate s1 lc 0) (of_estate s2 lc (size lc))
                                    (@leak_i_iLs (@leak_i_iL LO) LO stk ltc' lc0) Hd Hc).
          rewrite /lsem /add_hd_c /= addn0 in Hhd.
          have Htl := (@lsem_cat_tl LO). 
          rewrite /lsem in Htl.
          rewrite /add_hd_c in Htl. rewrite /= in Htl.
          rewrite /setpc /=. rewrite /setc in Htl. rewrite /= in Htl.
          have /= {Htl} Htl := (Htl [:: ι (Licond true lbl)] gd {|
          lmem := emem s1;
          lvm := evm s1;
          lc := ι (Lilabel lbl) :: lc;      
          lpc := 1|}  {|
          lmem := emem s2;
          lvm := evm s2;
          lc := ι (Lilabel lbl) :: lc;
          lpc := 1 + size lc |} (@leak_i_iLs (@leak_i_iL LO) LO stk ltc' lc0) Hhd).
          by apply Htl. 
        apply: lsem_step.
        + rewrite /lsem1 /step /find_instr /= onth_cat ltnn subnn /= /eval_instr /= /to_estate /=.
          replace s2 with {| emem := emem s2; evm := evm s2 |} in He; last by case s2.
          rewrite /= find_label_hd /=. rewrite /= in He. case: He=> <-.
          by rewrite PoszD GRing.opprD GRing.addrA GRing.subrr GRing.add0r (linear_size Heqc).
        (* recursive part *)
        by move: IH; rewrite /setpc /of_estate /= -/(ilwhile_c'0 leak_i_iL) size_cat /=.
      move=> s1 s2 a' c0 e0 c' le0 lc0 Hsem He [] h1 h2 h3 h4; subst a c c'. 
      rewrite -h3 in He. rewrite /= in He. case: He=> He1 He2. inversion He1.
    (* last case: c' is not empty *)
    move: (i :: c') => { i c' } c' Hc'.
    rewrite linear_c_nil;case Heqc: linear_c => [[[lblc lc] ltc]|] //=.
    have {Hc}[Hle1 Hvc Hc]:= Hc _ _ _ _ Heqc.
    rewrite linear_c_nil.
    case Heq:linear_c => [[[lblc' lc'] ltc']|] //= [] ??;subst lbli li; move=> <- /=.
    have leL1 := le_next lbl; have leL2 := le_next (next_lbl lbl).
    have lblL2 := Pos_leb_trans leL1 leL2.
    have lblcL2 := Pos_leb_trans lblL2 Hle1.
    have [Hle Hv Hs]:= Hc' _ _ _ _ Heq;split.
    + apply: (Pos_leb_trans lblL2).
      by apply: (Pos_leb_trans Hle1).
    + rewrite /= valid_add_align /= valid_cat /= Pos.leb_refl leL1 (valid_le_min _ Hv) //.
      rewrite (Pos_lt_leb_trans (lt_next _)).
      rewrite (Pos_lt_leb_trans _ Hle) /=.
      rewrite valid_cat /= leL1 /=.
      rewrite (valid_le_max Hle) /=.
      rewrite (Pos_lt_leb_trans (lt_next _)) //.
      rewrite (Pos_leb_trans Hle1) //.
      rewrite (valid_le_min _ Hvc) //.
      rewrite (Pos_lt_leb_trans (lt_next _)) //.
      rewrite (Pos_leb_trans _ Hle) //.
      rewrite (Pos_leb_trans leL2 Hle1) //.
    move=> s1 s2 li H. rewrite leak_i_il_il_while /=.
    set C := (C in of_estate _ C _);rewrite -/C.
    pose C1 := (ι (Lilabel (next_lbl lbl)) :: lc' ++ ι (Lilabel lbl) :: lc ++ [:: ι (Licond true (next_lbl lbl))]).
    suff : leak_w_WF ltc ltc' li /\
       @lsem LO gd (of_estate s1 C1 (size lc').+2) (@ilwhile (@leak_i_iL LO) LO stk ltc ltc' li) (of_estate s2 C1 (size C1)).
    + move=> [? h]; split; first by constructor. 
      apply lsem_step with (of_estate s1 C ((a == Align) + (size lc').+2).+1).
      + rewrite /lsem1 /step /= /eval_instr /=.
        have -> /= : find_label lbl C =  ok ((a == Align) + (size lc').+2); last first.
        + rewrite GRing.subr0 addnA (addnC (get_linear_size_C _)) -addnS -addn3 addnA -(linear_size Heq).
          by case: (a).
        rewrite /C -cat1s find_label_cat_hd //= find_label_add_align.
        rewrite -!cat_cons find_label_cat_hd /=.
        + by rewrite find_label_hd /= addn0 addnA (addnC 1) -addnA.
        rewrite /= {1}/is_label /=.
        case: eqP => H' /=.
        + by have := lt_next lbl;rewrite Pos.ltb_antisym -H' Pos.leb_refl.
        apply /negP=> H1;have := @valid_has _ lbl _ _ Hv.
        rewrite H1 Pos.leb_antisym.
        by rewrite (Pos_lt_leb_trans (Pos_lt_leb_trans (lt_next _) leL2) Hle1) /= => /(_ isT).
      move: h; rewrite /C add_align_nil -cat_cons size_cat /= => h.
      have -> : ((a == Align) + (size lc').+2).+1 =
                size ((ι (Ligoto lbl) :: add_align ii a [::])) + (size lc').+2.
      + by case: (a).
      apply: (lsem_cat_hd (c := ι (Ligoto lbl) :: add_align ii a [::]) _ h). 
      by rewrite /disjoint_lbl; case:(a).
   (* Start induction after the first goto (at the first location where the loop will come back) *)
    elim: _ {-1}_ _ _ / H (erefl (Cwhile a c true c'))=> // {s1 s2}.
    + move=> s1 s2 s3 s4 a0 c0 e0 c'0 lc0 le lc'0 lw Hsem0 He Hsem Hsemi IH [] ????; subst a0 c0 e0 c'0.
      case: (Hs _ _ _ Hsem) => hwf1 {Hs} Hs.
      case: (Hc _ _ _ Hsem0) => Hwf2 {Hc} Hc.
      case: (IH refl_equal) => hwf {IH} IH; split; first by constructor.
      apply tc_trans with (of_estate s2 C1 ( (size lc').+2 + size lc)).
      + have Hd: disjoint_lbl
          [:: {| li_ii := ii; li_i := Lilabel (next_lbl lbl) |}
          & lc' ++ [:: {| li_ii := ii; li_i := Lilabel lbl |}]] lc.
        + rewrite -cat1s !disjoint_cat_l; repeat split=> //.
          + move=> lbl0 /=;rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply /negP=> H; have := @valid_has _ (next_lbl lbl) _ _ Hvc.
            by rewrite H Pos.leb_antisym (lt_next _) orbT=> /(_ isT).
          + apply: (valid_disjoint _ Hv Hvc).
            by rewrite Pos.leb_refl /= orbT.
          + move=> lbl0 /=; rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply/negP=> H; have := @valid_has _ lbl _ _ Hvc.
            by rewrite H Pos.leb_antisym (Pos_lt_leb_trans (lt_next _) leL2) orbT=> /(_ isT).
        have /(_ _ Hd):= lsem_cat_hd _ Hc.
        move=> /(lsem_cat_tl [:: MkLI ii (Licond true (next_lbl lbl))]) /=.
        rewrite !of_estate_add_hd_c !setc_of_estate /= /C1.
        by rewrite !size_cat addn0 /= addn1 !addSn /= -!cat_cons -!catA.
      apply: lsem_step.
      + rewrite /lsem1 /step /= /C1 /find_instr /=.
        rewrite -cat_cons catA onth_cat size_cat /= addnS ltnn subnn /eval_instr /=.
        rewrite /= in He. case: He => <-.
        rewrite /setpc /of_estate /find_label /= /is_label /= eqxx /=.
        rewrite -addn2 !PoszD -(linear_size Heqc) -(linear_size Heq).
        rewrite (GRing.addrC (Posz (size lc'))) !GRing.opprD !GRing.addrA.
        rewrite GRing.addrC (GRing.addrC (1 - Posz 2)%R). 
        have -> : (1 - Posz 2 = -1)%R by done.
        by rewrite GRing.addrA.
      apply: tc_trans.
      + have Hd : disjoint_lbl [:: MkLI ii (Lilabel (next_lbl lbl))] lc'.
        + move=> lbl0 /=;rewrite orbF /is_label /=;case: eqP => //= ?;subst.
          apply /negP=> H;have := @valid_has _ (next_lbl lbl) _ _ Hv.
          rewrite H Pos.leb_antisym.
          by rewrite (Pos_lt_leb_trans (lt_next _) Hle1) /= orbT => /(_ isT).
      have /(_ _ Hd) := lsem_cat_hd _ Hs. 
      move=> /(@lsem_cat_tl LO ((MkLI ii (Lilabel lbl)) :: lc ++ [:: MkLI ii (Licond true (next_lbl lbl))])).
      rewrite !of_estate_add_hd_c !setc_of_estate !lc_of_estate addn0.
      rewrite -!cat_cons -!catA => H.
      apply H.
      apply: lsem_step.
      + by rewrite /lsem1 /step /= /find_instr /= onth_cat ltnn subnn /= /eval_instr /=;eauto.
      exact: IH.
    move=> s1 s2 c0 a0 e0 c0' le lc0 Hs0 He [????]; subst a0 e0 c0 c0'.
    by rewrite /= in He; case: He=> He1 He2; inversion He1.
    (* case 2: when e is false *) (* done *)
    + rewrite linear_c_nil; case Heqc' : linear_c => [[[lblc' lc'] ltc]|] //=.
      move: Hc. rewrite /Pc. 
      move=> Hc. move: (Hc lbl lblc' lc' ltc Heqc'). move=> [] H1 H2 H3.
      move=> [] <- <- <-; split.
      + auto.
      + rewrite cats0. apply H2.
      + rewrite cats0. move=> s1 s2 l /S.sem_iE' [si] [b] [lc] [le] [Hs] //=.
        move=> [] [] <- <- [] <- -> /=. move: (H3 s1 si lc Hs). move=> {H3} [Hwf H3].
        split; first by constructor.
        by apply H3.
    (* last case *)
    case: c' Hc' => [ _ | i c' ].
    (* c' is [::]*)
    (* when c' = [::] *)
    (* align; Lilabel L1; c ; Licond e L1 *)
    (* Depending on e we will repeat c till e becomes false *)
    + rewrite linear_c_nil;case Heqc: linear_c => [[[lblc lc] ltc']|] //= x; apply ok_inj in x.
      case/xseq.pair_inj: x => h1 <-; case: h1=> h1' h1''; subst lbli li.
      have {Hc}[Hle1 Hvc Hc]:= Hc _ _ _ _ Heqc.
      have leL1 := le_next lbl.
      have ltL1 := lt_next lbl.
      have Hle2 := Pos_leb_trans leL1 Hle1.
      have Hlt := Pos_lt_leb_trans ltL1 Hle1.
      split => //.
      + by rewrite valid_add_align /= valid_cat /= Pos.leb_refl Hlt (valid_le_min _ Hvc).
      move=> s1 s2 li H. rewrite leak_i_iL_while_c'0 /=. 
      suff : leak_w0_WF ltc' li /\
        @lsem LO gd
         (setpc (of_estate s1 (ι (Lilabel lbl) :: lc ++ [:: ι (Licond e lbl)]) 0)
         (lpc (of_estate s1 (ι (Lilabel lbl) :: lc ++ [:: ι (Licond e lbl)]) 0)).+1)
         (@ilwhile_c'0 (@leak_i_iL LO) LO stk ltc' li)
         (of_estate s2 (ι (Lilabel lbl) :: lc ++ [:: ι (Licond e lbl)])
           (size (ι (Lilabel lbl) :: lc ++ [:: ι (Licond e lbl)]))).
      + move=> [??]; split; first by constructor.
        by apply: lsem_add_align; apply: lsem_step.
      set L := [:: ι (Lilabel lbl) ].
      set C := L ++ lc ++ [:: ι (Licond e lbl)].
      have HL : valid lbl (next_lbl lbl) L by rewrite/L/= Pos.leb_refl ltL1.
      have Hd : disjoint_lbl L lc by apply: valid_disjoint _ HL Hvc; rewrite Pos.leb_refl.
      elim: _ {-1} _ _ _ / H (erefl (Cwhile a c e [::])) => // { s1 s2}.
      + move=> s1 s2 s3 s4 a' c0 e0 c' lc0 le lc' lw Hsem He Hsem' Hs IH.
        move=> [] h1 h2 h3 h4; subst a c0 e0 c'.
        specialize (IH (erefl _)). case: IH => Hwf IH.
        specialize (Hc _ _ _ Hsem). case: Hc => Hwf' Hc.
        split; first by constructor.
        move: Hsem'. move=> /S.semE. 
        move=> [] hs hl.
        apply: tc_trans.
        + have /(_ _ Hd) := lsem_cat_hd _ Hc. move=> Hhd.
          move: (lsem_cat_tl [:: ι (Licond e lbl)] Hhd). move=> Htl.
          rewrite /lsem in Hhd. rewrite /lsem in Htl.
          rewrite /add_hd_c in Htl. rewrite /= in Htl.
          rewrite /setpc /=. rewrite /setc in Htl. rewrite /= in Htl. 
          by apply Htl. 
        apply: lsem_step.
        + rewrite /lsem1 /step /find_instr /= onth_cat ltnn subnn /= /eval_instr /= /to_estate /=.
          replace s2 with {| emem := emem s2; evm := evm s2 |} in He; last by case s2.
          rewrite He /= find_label_hd /= -(linear_size Heqc).
          by rewrite PoszD GRing.opprD GRing.addrA GRing.subrr GRing.add0r. 
          
        (* recursive part *)
        by rewrite /setpc /of_estate /= hs in IH.
      move=> s1 s2 a' c0 e0 c' le0 lc0 Hsem He [] h1 h2 h3 h4; subst a c e c'. 
      specialize (Hc _ _ _ Hsem); case: Hc => Hwf Hc.
      split; first by constructor.
      apply: tc_trans.
      + have /(_ _ Hd) := lsem_cat_hd _ Hc. move=> Hhd.
        move: (lsem_cat_tl [:: ι (Licond e0 lbl)] Hhd). move=> Htl.
        rewrite /lsem in Hhd. rewrite /lsem in Htl.
        rewrite /add_hd_c in Htl. rewrite /= in Htl.
        rewrite /setpc /=. rewrite /setc in Htl. rewrite /= in Htl.
        by apply Htl.
      apply: tc_step.
      rewrite /lsem1 /step /= /of_estate /find_instr /=.
      rewrite onth_cat ltnn subnn /= /eval_instr /= to_of_estate He /=.
      by rewrite size_cat /= add1n addn1.
    (* last case: c' is not empty *)
    move: (i :: c') => { i c' } c' Hc'.
    rewrite linear_c_nil;case Heqc: linear_c => [[[lblc lc] ltc]|] //=.
    have {Hc}[Hle1 Hvc Hc]:= Hc _ _ _ _ Heqc.
    rewrite linear_c_nil.
    case Heq:linear_c => [[[lblc' lc'] ltc']|] //= [] ??;subst lbli li; move=> <- /=.
    have leL1 := le_next lbl; have leL2 := le_next (next_lbl lbl).
    have lblL2 := Pos_leb_trans leL1 leL2.
    have lblcL2 := Pos_leb_trans lblL2 Hle1.
    have [Hle Hv Hs]:= Hc' _ _ _ _ Heq;split.
    + apply: (Pos_leb_trans lblL2).
      by apply: (Pos_leb_trans Hle1).
    + rewrite /= valid_add_align /= valid_cat /= Pos.leb_refl leL1 (valid_le_min _ Hv) //.
      rewrite (Pos_lt_leb_trans (lt_next _)).
      rewrite (Pos_lt_leb_trans _ Hle) /=.
      rewrite valid_cat /= leL1 /=.
      rewrite (valid_le_max Hle) /=.
      rewrite (Pos_lt_leb_trans (lt_next _)) //.
      rewrite (Pos_leb_trans Hle1) //.
      rewrite (valid_le_min _ Hvc) //.
      rewrite (Pos_lt_leb_trans (lt_next _)) //.
      rewrite (Pos_leb_trans _ Hle) //.
      rewrite (Pos_leb_trans leL2 Hle1) //.
    move=> s1 s2 li H. rewrite leak_i_il_il_while /=.
    set C := (C in of_estate _ C _);rewrite -/C.
    pose C1 := (ι (Lilabel (next_lbl lbl)) :: lc' ++ ι (Lilabel lbl) :: lc ++ [:: ι (Licond e (next_lbl lbl))]).
    suff : leak_w_WF ltc ltc' li /\ 
      @lsem LO gd (of_estate s1 C1 ((size lc').+2)) (@ilwhile (@leak_i_iL LO) LO stk ltc ltc' li)
                (of_estate s2 C1 (size C1)).
    + move=> [? h]; split; first by constructor.
      apply lsem_step with (of_estate s1 C ((a == Align) + (size lc').+2).+1).
      + rewrite /lsem1 /step /= /eval_instr /=.
        have -> : find_label lbl C =  ok ((a == Align) + (size lc').+2); last first.
        + rewrite /=; do 3!f_equal.
          rewrite GRing.subr0 -addn1 -addn2 !PoszD -(linear_size Heq).
          have -> : get_align_size a = (a == Align) by case a. 
          by rewrite -!PoszD; f_equal; ring.
        rewrite /C -cat1s find_label_cat_hd // find_label_add_align.
        rewrite -!cat_cons find_label_cat_hd /=.
        + by rewrite find_label_hd /= addn0 addnA (addnC 1) -addnA.
        rewrite /= {1}/is_label /=.
        case: eqP => H' /=.
        + by have := lt_next lbl;rewrite Pos.ltb_antisym -H' Pos.leb_refl.
        apply /negP=> H1;have := @valid_has _ lbl _ _ Hv.
        rewrite H1 Pos.leb_antisym.
        by rewrite (Pos_lt_leb_trans (Pos_lt_leb_trans (lt_next _) leL2) Hle1) /= => /(_ isT).
      move: h; rewrite /C add_align_nil -cat_cons size_cat => h.
      have -> : ((a == Align) + (size lc').+2).+1 =
                size ((ι (Ligoto lbl) :: add_align ii a [::])) + (size lc').+2.
      + by case: (a).
      by apply: (lsem_cat_hd _ h); rewrite /disjoint_lbl; case:(a).

    elim: _ {-1}_ _ _ / H (erefl (Cwhile a c e c'))=> // {s1 s2}.
    + move=> s1 s2 s3 s4 a0 c0 e0 c'0 lc0 le lc'0 lw Hsem0 He Hsem Hsemi IH [] ????; subst a0 c0 e0 c'0.
      case: (Hs _ _ _ Hsem) => {Hs} Hwf1 Hs.
      case: (Hc _ _ _ Hsem0) => {Hc} Hwf2 Hc.
      case: (IH refl_equal) => {IH} Hwf3 IH.
      split; first by constructor.
      apply tc_trans with (of_estate s2 C1 ( (size lc').+2 + size lc)).
      (*apply (@lsem_trans gd (of_estate s2 C1 ( (size lc').+2 + size lc))).*)
      + have Hd: disjoint_lbl
          [:: {| li_ii := ii; li_i := Lilabel (next_lbl lbl) |}
          & lc' ++ [:: {| li_ii := ii; li_i := Lilabel lbl |}]] lc.
        + rewrite -cat1s !disjoint_cat_l; repeat split=> //.
          + move=> lbl0 /=;rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply /negP=> H; have := @valid_has _ (next_lbl lbl) _ _ Hvc.
            by rewrite H Pos.leb_antisym (lt_next _) orbT=> /(_ isT).
          + apply: (valid_disjoint _ Hv Hvc).
            by rewrite Pos.leb_refl /= orbT.
          + move=> lbl0 /=; rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply/negP=> H; have := @valid_has _ lbl _ _ Hvc.
            by rewrite H Pos.leb_antisym (Pos_lt_leb_trans (lt_next _) leL2) orbT=> /(_ isT).
        have /(_ _ Hd):= lsem_cat_hd _ Hc.
        move=> /(lsem_cat_tl [:: MkLI ii (Licond e (next_lbl lbl))]) /=.
        rewrite !of_estate_add_hd_c !setc_of_estate /= /C1.
        by rewrite !size_cat addn0 /= addn1 !addSn /= -!cat_cons -!catA.
      apply: lsem_step.
      + rewrite /lsem1 /step /= /C1 /find_instr /=.
        rewrite -cat_cons catA onth_cat size_cat /= addnS ltnn subnn /eval_instr /=.
        rewrite to_of_estate He /find_label /= /is_label /= eqxx /=.
        rewrite -add2n -(linear_size Heqc) -(linear_size Heq) (addnC (size lc)) !PoszD.
        rewrite !GRing.opprD !GRing.addrA.
        have -> : (1 - Posz 2 = -1)%R by done.
        by rewrite -GRing.addrA GRing.addrC.
      rewrite setpc_of_estate.
      apply: tc_trans.
      + have Hd : disjoint_lbl [:: MkLI ii (Lilabel (next_lbl lbl))] lc'.
        + move=> lbl0 /=;rewrite orbF /is_label /=;case: eqP => //= ?;subst.
          apply /negP=> H;have := @valid_has _ (next_lbl lbl) _ _ Hv.
          rewrite H Pos.leb_antisym.
          by rewrite (Pos_lt_leb_trans (lt_next _) Hle1) /= orbT => /(_ isT).
      have /(_ _ Hd) := lsem_cat_hd _ Hs.
      move=> /(@lsem_cat_tl LO ((MkLI ii (Lilabel lbl)) :: lc ++ [:: MkLI ii (Licond e (next_lbl lbl))])).
      rewrite !of_estate_add_hd_c !setc_of_estate !lc_of_estate addn0.
      rewrite -!cat_cons -!catA => H.
      apply H.
      apply: lsem_step.
      + by rewrite /lsem1 /step /= /find_instr /= onth_cat ltnn subnn /= /eval_instr /=;eauto.
      exact: IH.
    + move=> s1 s2 c0 a0 e0 c0' le lc0 Hs0 He [????]; subst a0 e0 c0 c0'.
      case: (Hc _ _ _ Hs0) => {Hc} [] Hwf Hc; split; first by constructor.
      apply tc_trans with (of_estate s2 C1 (size lc' + size lc).+2).
      + have Hd: disjoint_lbl
          [:: {| li_ii := ii; li_i := Lilabel (next_lbl lbl) |}
          & lc' ++ [:: {| li_ii := ii; li_i := Lilabel lbl |}]] lc.
          rewrite -cat1s !disjoint_cat_l; repeat split=> //.
          + move=> lbl0 /=;rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply /negP=> H; have := @valid_has _ (next_lbl lbl) _ _ Hvc.
            by rewrite H Pos.leb_antisym (lt_next _) orbT=> /(_ isT).
          + apply: (valid_disjoint _ Hv Hvc).
            by rewrite Pos.leb_refl /= orbT.
          + move=> lbl0 /=; rewrite orbF /is_label /=; case: eqP=> //= ?;subst.
            apply/negP=> H; have := @valid_has _ lbl _ _ Hvc.
            by rewrite H Pos.leb_antisym (Pos_lt_leb_trans (lt_next _) leL2) orbT=> /(_ isT).
        have /(_ _ Hd) := lsem_cat_hd _ Hc.
        move=> /(lsem_cat_tl [:: MkLI ii (Licond e (next_lbl lbl))]) /=.
        rewrite !of_estate_add_hd_c !setc_of_estate /= size_cat /= addn0 addn1.
        by rewrite -!cat_cons -!catA.
      apply: tc_step.
      rewrite /lsem1 /step /find_instr /= -cat_cons catA onth_cat.
      rewrite size_cat /= addnS ltnn subnn /eval_instr /= to_of_estate He /=;eauto.
      by rewrite setpc_of_estate /C /= size_cat /= size_cat /= addn1 !addnS.
   Qed.

  Let Hcall : forall i xs f es, Pi_r (Ccall i xs f es).
  Proof. by []. Qed.

  Lemma linear_cP c lbl lblc lc ltc:
    linear_c linear_i c lbl [::] = ok (lblc, lc, ltc) ->
    [/\ (lbl <=? lblc)%positive,
     valid lbl lblc lc &
     forall s1 s2 l, S.sem p gd s1 c l s2 ->
       leak_is_WF ltc l /\
       lsem gd (of_estate s1 lc 0) (leak_i_iLs (leak_i_iL) stk ltc l) (of_estate s2 lc (size lc))].
  Proof.
    apply (@cmd_rect Pi_r Pi Pc HmkI Hskip Hseq Hassgn Hopn Hif Hfor Hwhile Hcall).
  Qed.

  Lemma linear_fdP : forall fn m1 va m2 vr lf,
    S.sem_call p gd m1 fn va (fn, lf) m2 vr -> 
    leak_is_WF (leak_Fun_L Fs fn) lf /\
    lsem_fd p' gd m1 fn va (fn, leak_i_iLs leak_i_iL stk (leak_Fun_L Fs fn) lf) m2 vr.
  Proof.
    move=> fn m1 vargs m2 vargs' lf /S.sem_callE' [] sf [] Hsf [] m1' [] m2' [] vargs1 [] s2 [] m2'' [] vm2 [] vres.
    move=> [] Halloc [] Hs1 [] Htyi [] Hs2 [] /= Hbody [] Hres [] Htyo Hm2.
    have dcok : map_cfprog_leak linear_fd p = ok (p', Fs).
    + move: linear_ok; rewrite /linear_prog /=. by move=> ->.
    have := (get_map_cfprog_leak dcok Hsf). move=> [] f' [] lt' [] Hf'1 /= Hf'2 Hleak.
    have Hf'3 := Hf'1.
    apply: rbindP Hf'3=> [[[l1 l2] l3] Hc] [] Hf'3.
    rewrite /add_finfo in Hc.
    case Heq: linear_c Hc=> [[[lblc lc'] ltc]|] //= [] Hl Hl1 Hl2 Hl3.
    rewrite linear_c_nil in Heq.
    apply: rbindP Heq=> [[[lblc' lc''] ltc']] Heq [] Hz1 Hz2.
    have [h1 h2 H]:= linear_cP Heq.
    move: Hbody=> /H [] Hwf /(@lsem_cat_tl LO [::]) Hs.
    rewrite -Hf'3 in Hf'2. move=> h.
    have -> : (leak_Fun_L Fs fn) = lt'.
    + by rewrite /get_leak in Hleak; rewrite /leak_Fun_L /= Hleak.
    subst; split => //.
    eapply LSem_fd; eauto.
    move: Hs; rewrite /= !setc_of_estate.
    by rewrite cats0.
  Qed.

End PROOF.


