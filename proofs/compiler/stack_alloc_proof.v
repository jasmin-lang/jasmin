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

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import psem compiler_util constant_prop_proof.
Require Export stack_alloc stack_sem.
Require Import Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
Local Open Scope Z_scope.

(* --------------------------------------------------------------------------- *)

Lemma size_of_pos t s : size_of t = ok s -> (1 <= s).
Proof.
  case: t=> //= [sz p [] <-| sz [] <-]; have hsz := wsize_size_pos sz; nia.
Qed.

Definition stk_ok (w: pointer) (z:Z) :=
  wunsigned w + z <= wbase Uptr /\
  forall ofs s,
    (0 <= ofs /\ ofs + wsize_size s <= z)%Z ->
    is_align (w + wrepr _ ofs) s = is_align (wrepr _ ofs) s.

Definition valid_map (m:map) (stk_size:Z) :=
  forall x px, Mvar.get m.1 x = Some px -> 
     exists sx, size_of (vtype x) = ok sx /\
     [/\ 0 <= px, px + sx <= stk_size,
      aligned_for (vtype x) px &
         forall y py sy, x != y ->  
           Mvar.get m.1 y = Some py -> size_of (vtype y) = ok sy ->
           px + sx <= py \/ py + sy <= px].

Hint Resolve is_align_no_overflow Memory.valid_align.

Section PROOF.
  Variable P: prog.
  Notation gd := (p_globs P).
  Variable SP: sprog.

  Variable m:map.
  Variable stk_size : Z.
  Variable pstk : pointer.

  Hypothesis pstk_add : stk_ok pstk stk_size.

  Hypothesis validm : valid_map m stk_size.

  Definition valid_stk_word (vm1:vmap) (m2:mem) (pstk: pointer) (p: Z) sz vn :=
    valid_pointer m2 (pstk + wrepr _ p) sz /\
    forall v,
      vm1.[{| vtype := sword sz; vname := vn |}] = ok v ->
      exists e : pw_size v = sz, 
       read_mem m2 (pstk + wrepr _ p) sz = 
          ok (eq_rect (pw_size v) (fun sz => word sz) (pw_word v) sz e).

  Definition valid_stk_arr (vm1:vmap) (m2:mem) (pstk: pointer) (p: Z) sz s vn :=
    forall off, (0 <= off < Zpos s)%Z ->
      valid_pointer m2 (pstk + (wrepr _ (wsize_size sz * off + p))) sz /\
      let t := vm1.[{| vtype := sarr sz s; vname := vn |}] in
      forall a, t = ok a ->
        forall v, FArray.get a off = ok v ->
          read_mem m2 (pstk + (wrepr _ (wsize_size sz * off + p))) sz = ok v.

  Definition valid_stk (vm1:vmap) (m2:mem) pstk :=
    forall x,
      match Mvar.get m.1 x with
      | Some p =>
        match vtype x with
        | sword sz => valid_stk_word vm1 m2 pstk p sz (vname x)
        | sarr sz s => valid_stk_arr vm1 m2 pstk p sz s (vname x)
        | _ => True
        end
      | _ => True
      end.

  Definition eq_vm (vm1 vm2:vmap) := 
    forall (x:var), 
       ~~ is_in_stk m x -> ~~ is_vstk m x -> 
       eval_uincl vm1.[x] vm2.[x].

  Lemma eq_vm_write vm1 vm2 x v v':
    eq_vm vm1 vm2 ->
    eval_uincl v v' -> 
    eq_vm vm1.[x <- v] vm2.[x <- v'].
  Proof.
    move=> Heqvm Hu w ??.
    case : (x =P w) => [<- | /eqP ?];first by rewrite !Fv.setP_eq.
    by rewrite !Fv.setP_neq //; apply Heqvm.
  Qed.

  Definition disjoint_stk m :=
    forall w sz,
      valid_pointer m w sz ->
      ~((wunsigned pstk <? wunsigned w + wsize_size sz) && (wunsigned w <? wunsigned pstk + stk_size)).

  Variant valid (s1 s2: estate) : Prop :=
    Valid of
      (disjoint_stk (emem s1)) &
      (forall w sz, valid_pointer (emem s1) w sz -> read_mem (emem s1) w sz = read_mem (emem s2) w sz) &
      (forall w sz, valid_pointer (emem s2) w sz = valid_pointer (emem s1) w sz || (between pstk stk_size w sz && is_align w sz)) &
      (eq_vm (evm s1) (evm s2)) &
      (get_var (evm s2) (vstk m) = ok (Vword pstk)) &
      (top_stack (emem s2) = pstk) &
      (frame_size (emem s2) pstk = Some stk_size) &
      (valid_stk (evm s1) (emem s2) pstk)
  .

  Lemma check_varP vm1 vm2 x1 x2 v:
    check_var m x1 x2 -> eq_vm vm1 vm2 -> 
    get_var vm1 x1 = ok v ->
    exists v', get_var vm2 x2 = ok v' /\ value_uincl v v'.
  Proof.
    move=> /andP [/andP [Hin_stk /eqP Heq12] Hnot_vstk] Heq Hget.
    have := Heq _ Hin_stk Hnot_vstk.
    move: Hget;rewrite /get_var Heq12; apply: on_vuP => [t | ] -> /=.
    + by move=> <-;case vm2.[x2] => //= s Hs;exists (pto_val s).
    move=> [<-] /=;case vm2.[x2] => //= [s _ | ? <-].
    + by exists (pto_val s);split => //;symmetry;apply subtype_eq_vundef_type;
        apply subtype_type_of_val.
    eexists;split;first reflexivity.
    by symmetry;apply subtype_eq_vundef_type;apply subtype_vundef_type.
  Qed.

  Lemma check_varsP vm1 vm2 x1 x2 vs:
    all2 (check_var m) x1 x2 -> eq_vm vm1 vm2 ->
    mapM (fun x : var_i => get_var vm1 x) x1 = ok vs ->
    exists vs', 
      mapM (fun x : var_i => get_var vm2 x) x2 = ok vs' /\
      List.Forall2 value_uincl vs vs'.
  Proof.
    elim: x1 x2 vs=> [|a l IH] [|a' l'] //= vs.
    + move=> _ Heq [<-];by exists [::].
    move=> /andP [Ha Hl] Heq.
    apply: rbindP => va /(check_varP Ha Heq) [v' [-> Hu]].
    apply: rbindP => tl  /(IH _ _ Hl Heq) [tl' [-> Hus]] [<-] /=.
    by exists (v' :: tl');split=>//;constructor.
  Qed.

  Lemma check_var_stkP s1 s2 sz x1 x2 e v:
    check_var_stk m sz x1 x2 e ->
    valid s1 s2 ->
    sem_pexpr gd s1 (Pvar x1) = ok v ->
    exists v', 
       sem_pexpr gd s2 (Pload sz x2 e) = ok v' /\ value_uincl v v'.
  Proof.
    case/andP => /andP [] /eqP Hvstk /eqP Htype.
    case Hget: (Mvar.get _ _) => [ ofs |] // /eqP -> {e}.
    case => _ _ _ _; rewrite - Hvstk => Hpstk _ _ /(_ x1).
    rewrite Hget Htype => -[] /= H H' Hvar.
    rewrite Hpstk /=.
    case: x1 Htype Hget Hvar H'=> [[x1t x1n] vi1] /= Htype Hget Hvar H'; subst.
    rewrite /zero_extend !wrepr_unsigned.
    apply: on_vuP Hvar => /= [w | ].
    + by move => /H';case: w => sz' w hle /= [heq ->] <-;subst sz';exists (Vword w).
    by move=> _ [<-];move /Memory.readV: H => [w -> /=];exists (Vword w).
  Qed.

  Lemma is_addr_ofsP sz ofs e1 e2 :
    is_addr_ofs sz ofs e1 e2 ->
    exists i, 
    e1 = Pconst i /\ 
    e2 = Papp1 (Oword_of_int Uptr) (wsize_size sz * i + ofs).
  Proof.
    rewrite /is_addr_ofs;case:is_constP => // i.
    by case: is_wconst_of_sizeP => // z /eqP <-; eauto.
  Qed.

  Lemma check_arr_stkP s1 s2 sz x1 e1 x2 e2 v:
    check_arr_stk m sz x1 e1 x2 e2 ->
    valid s1 s2 ->
    sem_pexpr gd s1 (Pget x1 e1) = ok v ->
    sem_pexpr gd s2 (Pload sz x2 e2) = ok v.
  Proof.
    case: x1 => [[xt1 xn1] ii1]; case/andP => /eqP Hvstk /=.
    case: xt1 => // sz1 n /andP [] /eqP -> {sz1}.
    case Hget: (Mvar.get m.1 _)=> [ofs|//] /is_addr_ofsP [i [??]];subst e1 e2.
    set x1 := {| vname := xn1 |}.
    case => H1 H2 H3 H4 H5 _ _ H6.
    apply: on_arr_varP=> sz' n' t /= [_ ?] Harr; subst n'.
    apply: rbindP => z Hgeti [<-].
    rewrite Hvstk H5 /=.
    have Hbound := Array.getP_inv Hgeti.
    have /andP [/ZleP H0le /ZltP Hlt]:= Hbound.
    rewrite /zero_extend !wrepr_unsigned.
    have := H6 x1; rewrite Hget /=.
    move=> /(_ i) [//| /=] ?.
    move: Harr;rewrite /get_var.
    apply: on_vuP => //= n0 Ht0 /Varr_inj [_] [?]; subst => /= ?; subst n0.
    move=> /(_ _ Ht0) H.
    by move: Hgeti; rewrite /Array.get Hbound => /H ->.
  Qed.

  Lemma check_eP (e1 e2: pexpr) (s1 s2: estate) v :
    check_e m e1 e2 -> valid s1 s2 -> sem_pexpr gd s1 e1 = ok v ->
    exists v', sem_pexpr gd s2 e2 = ok v' /\ value_uincl v v'.
  Proof.
    move=> He Hv; move: He.
    have Hvm: eq_vm (evm s1) (evm s2).
      by move: Hv=> -[].
    elim: e1 e2 v=> 
     [z1|b1|sz1 n1|v1| g1 |v1 e1 IH|sz1 v1 e1 IH|o1 e1 IH|o1 e1 H1 e1' H1' | e He e1 H1 e1' H1'] e2 v.
    + by case: e2=> //= z2 /eqP -> [] <-;exists z2;auto.
    + by case: e2=> //= b2 /eqP -> [] <-;exists b2;auto.
    + by case: e2 => // _ _ /andP [] /eqP <- /eqP <- [<-]{v}; eexists; split; first reflexivity.
    + case: e2 => //= [v2 | sz2 v2 e2].
      + by move=> /check_varP -/(_ _ _ _ Hvm) H/H. 
      move=> /check_var_stkP -/(_ _ _ _ Hv) H /H {H} [v' [Hload /= Hu]].
      by exists v';split.
    + by case: e2=>//= g2 /eqP -> ->; eauto.
    + case: e2=> //= [ | sz ] v2 e2.
      + move=> /andP [/check_varP Hv12 /IH{IH} He].
        apply: on_arr_varP=> sz n t Ht Harr /=.
        rewrite /on_arr_var. 
        have [v' [-> Hu] /=]:= Hv12 _ _ _ Hvm Harr.
        apply: rbindP=> i; apply: rbindP=> ve /He [ve' [-> Hve]].
        move=> /(value_uincl_int Hve) [??];subst ve ve'=> /=.
        apply: rbindP => w Hw [<-].
        case: v' Hu => //= sz' n' a [<-] [?]; subst => /= /(_ _ _ Hw) -> /=.
        by exists (Vword w); split => //; exists erefl.
      move=> He Hv1;exists v;split=>//.
      by apply: (check_arr_stkP He Hv Hv1).
    + case: e2=> // sz v2 e2 /= /andP [/andP [] /eqP -> Hv12 He12].
      apply: rbindP=> w1; apply: rbindP=> x1 Hx1 Hw1.
      apply: rbindP=> w2; apply: rbindP=> x2 Hx2 Hw2.
      apply: rbindP=> w Hw -[] <-.
      exists (Vword w);split => //.
      have [x1' [->]]:= check_varP Hv12 Hvm Hx1.
      move=> /value_uincl_word -/(_ _ _ Hw1) /= -> /=.
      have [v' [-> /= Hu]]:= IH _ _ He12 Hx2.
      rewrite (value_uincl_word Hu Hw2) /=.
      suff : @read_mem _ Memory.M (emem s2) (w1 + w2) sz = ok w by move => ->.
      rewrite -Hw;case: Hv => _ -> //.
      by apply/Memory.readV; exists w; exact: Hw.
    + case: e2=> // o2 e2 /= /andP []/eqP <- /IH He.
      apply: rbindP=> b /He [v' []] -> /vuincl_sem_sop1 Hu /Hu /= ->.
      by exists v.
    + case: e2=> // o2 e2 e2' /= /andP [/andP [/eqP -> /H1 He] /H1' He'].
      apply: rbindP=> v1 /He [v1' []] -> /vuincl_sem_sop2 Hu1.
      apply: rbindP=> v2 /He' [v2' []] -> /Hu1 Hu2 /Hu2 /= ->. 
      by exists v.
    case: e2 => // e' e2 e2' /= /andP[] /andP[] /He{He}He /H1{H1}H1 /H1'{H1'}H1'.
    apply: rbindP => b;apply: rbindP => w /He [b' [->]] /value_uincl_bool.
    move=> H /H [??];subst w b'=> /=.
    t_xrbindP=> v1 /H1 [] v1' [] -> Hv1' v2 /H1' [] v2' [] -> Hv2' /=.
    rewrite (value_uincl_vundef_type_eq Hv1') (value_uincl_vundef_type_eq Hv2').
    case:eqP => // heq;case: andP => // -[/(value_uincl_is_defined Hv1')] ->
       /(value_uincl_is_defined Hv2') -> /= [<-].
    by eexists;split;first reflexivity;case:(b).
  Qed.

  Lemma check_esP (es es': pexprs) (s1 s2: estate) vs :
    all2 (check_e m) es es' -> valid s1 s2 ->
    sem_pexprs gd s1 es = ok vs ->
    exists vs',  
      sem_pexprs gd s2 es' = ok vs' /\
      List.Forall2 value_uincl vs vs'.
  Proof.
    rewrite /sem_pexprs;elim: es es' vs=> //= [|a l IH] [ | a' l'] //= vs.
    + by move=> _ Hv [<-];eauto.
    move=> /andP [Ha Hl] Hvalid.
    apply: rbindP => v /(check_eP Ha Hvalid) [v' [->] Hu].
    apply: rbindP => vs1 /(IH _ _ Hl Hvalid) [vs' [->] Hus] [<-] /=.
    by exists (v' :: vs');split=>//;constructor.
  Qed.

  Lemma valid_stk_write_notinstk s1 s2 vi v:
    ~~ (is_in_stk m vi) ->
    valid_stk (evm s1) (emem s2) pstk ->
    valid_stk (evm s1).[vi <- v] (emem s2) pstk.
  Proof.
    move=> Hnotinstk Hstk x.
    move: Hstk=> /(_ x).
    case Hget: (Mvar.get m.1 x)=> [get|] //.
    have Hx: x != vi.
      apply/negP=> /eqP Habs.
      by rewrite /is_in_stk -Habs Hget in Hnotinstk.
    case Htype: (vtype x)=> // [sz p|].
    + move=> H off Hoff.
      move: H=> /(_ off Hoff) [H H'].
      split=> //.
      move=> t a0 Ht v0 Haget.
      rewrite /= in H'.
      have Hvma: (evm s1).[{| vtype := sarr sz p; vname := vname x |}] = ok a0.
        rewrite -Ht /t Fv.setP_neq //.
        case: x Hget Hx Htype t a0 Ht Haget H'=> [xt xn] /= ?? Htype ?????.
        by rewrite -Htype eq_sym.
      by rewrite (H' _ Hvma _ Haget).
    move=> [H H'];split=> //= v0; rewrite Fv.setP_neq; first by move=> /H'.
    by rewrite eq_sym;case: (x) Htype Hx => ?? /= ->.
  Qed.

  Lemma valid_set_uincl s1 s2 vi v v': 
    vi != vstk m -> ~~ is_in_stk m vi ->
    valid s1 s2 -> eval_uincl v v' ->
    valid {| emem := emem s1; evm := (evm s1).[vi <- v] |}
          {| emem := emem s2; evm := (evm s2).[vi <- v'] |}.
  Proof.
    move=> neq nin [???????] Hu;split=> //=.
    + by apply: eq_vm_write.
    + by rewrite /get_var Fv.setP_neq ?Hx //.
    by apply: valid_stk_write_notinstk.
  Qed.

  Lemma check_varW (vi vi': var_i) (s1 s2: estate) v v':
    check_var m vi vi' -> valid s1 s2 -> value_uincl v v' ->
    forall s1', write_var vi v s1 = ok s1' ->
    exists s2', write_var vi' v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> /andP [/andP [Hnotinstk /eqP Heq] Hnotstk] Hval Hu s1'. 
    rewrite /write_var -Heq => {Heq vi'}.
    (apply: rbindP=> z /=; apply: set_varP;rewrite /set_var) => 
       [ t | /negbTE ->]. 
    + move=> /(pof_val_uincl Hu) [t' [-> Htt']] <- [<-] /=.
      eexists;split;first reflexivity.
      by apply valid_set_uincl.
    move=> /pof_val_error [t' [Ht' ?]] ? [<-];subst.
    have : vundef_type (vtype vi) = vundef_type (type_of_val v'). 
    + rewrite -(value_uincl_vundef_type_eq Hu) /= -vundef_type_idem.
      by apply subtype_vundef_type_eq.
    move=> /pof_val_type_of [[v'']| ] -> /=;(eexists;split;first reflexivity);
      apply valid_set_uincl => //.
    by apply eval_uincl_undef.
  Qed.

  Lemma check_varsW (vi vi': seq var_i) (s1 s2: estate) v v':
    all2 (check_var m) vi vi' -> valid s1 s2 -> 
    List.Forall2 value_uincl v v' -> 
    forall s1', write_vars vi v s1 = ok s1' ->
    exists s2', write_vars vi' v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    elim: vi vi' v v' s1 s2 => [|a l IH] [|a' l'] //= [|va vl] [|va' vl'] s1 s2 //=.
    + by move=> _ Hv _ s1' []<-; exists s2.
    + by move => _ _ /List_Forall2_inv_l /seq_eq_injL.
    + by move => _ _ /List_Forall2_inv_r /seq_eq_injL.
    move=> /andP [Ha Hl] Hv /List_Forall2_inv_l [va''] [vl''] [] /seq_eq_injL [??]; subst va'' vl'' => - [] hva hvl s1'.
    apply: rbindP=> x Hwa.
    move: (check_varW Ha Hv hva Hwa)=> [s2' [Hs2' Hv2']] Hwl.
    move: (IH _ _ _ _ _ Hl Hv2' hvl _ Hwl)=> [s3' [Hs3' Hv3']].
    by exists s3'; split=> //; rewrite Hs2' /= Hs3'.
  Qed.

  Lemma wunsigned_pstk_add ofs :
    0 <= ofs -> ofs < stk_size ->
    wunsigned (pstk + wrepr Uptr ofs) = wunsigned pstk + ofs.
  Proof.
  move => p1 p2.
  apply: wunsigned_add.
  case: (pstk_add) => h _.
  have := wunsigned_range pstk.
  lia.
  Qed.

  Lemma lt_of_add_le x y sz :
    x + wsize_size sz <= y ->
    x < y.
  Proof. have := wsize_size_pos sz; lia. Qed.

  Lemma valid_get_w sz vn ofs :
    Mvar.get m.1 {| vtype := sword sz; vname := vn |} = Some ofs ->
    between pstk stk_size (pstk + wrepr Uptr ofs) sz && is_align (pstk + wrepr Uptr ofs) sz.
  Proof.
    case: pstk_add => hstk halign Hget.
    move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' Hal Hoverlap]]].
    subst.
    apply/andP; split.
    + have h := wunsigned_pstk_add Hsx (lt_of_add_le Hsx').
      apply/andP; rewrite h; split; apply/ZleP; lia.
    rewrite halign => //; lia.
  Qed.

  Lemma valid_stk_arr_var_stk s1 s2 sz xwn sz' xan ofsw ofsa n w m':
    let xw := {| vname := xwn; vtype := sword sz |} in
    Mvar.get m.1 xw = Some ofsw ->
    let xa := {| vname := xan; vtype := sarr sz' n |} in
    Mvar.get m.1 xa = Some ofsa ->
    write_mem (emem s2) (pstk + wrepr _ ofsw) sz w = ok m' ->
    valid_stk_arr (evm s1) (emem s2) pstk ofsa sz' n xan ->
    valid_stk_arr (evm s1).[xw <- ok (pword_of_word w)] m' pstk ofsa sz' n xan.
  Proof.
    move=> xw Hgetw xa Hgeta Hm' H off Hoff.
    have Hvmem : valid_pointer (emem s2) (pstk + wrepr _ ofsw) sz by apply /Memory.writeV;eauto.
    move: H=> /(_ off Hoff) [Hoff1 Hoff2]; split.
    - by rewrite (Memory.write_valid _ _ Hm').
    have hxwa : xw != xa by rewrite vtype_diff.
    rewrite Fv.setP_neq=> [t a Ht v0 Hv0| //].
    rewrite -(Hoff2 _ Ht _ Hv0).
    apply: (Memory.writeP_neq Hm').
    case: (validm Hgetw) => sx [] [<-] {sx} [hw hw' hxal] /(_ _ _ _ hxwa Hgeta erefl) hdisj.
    case: (validm Hgeta) => sa [] [<-] {sa} [ha ha' haal] _.
    split; eauto.
    have : wunsigned (pstk + wrepr _ ofsw) = wunsigned pstk + ofsw.
    - by apply: (wunsigned_pstk_add hw (lt_of_add_le hw')).
    have hsz' := wsize_size_pos sz'.
    have : wunsigned (pstk + wrepr _ (wsize_size sz' * off + ofsa)) = wunsigned pstk + wsize_size sz' * off + ofsa.
    - by rewrite wunsigned_pstk_add; nia.
    have hsz := wsize_size_pos sz.
    case: hdisj => h; [ left | right ]; nia.
  Qed.

  Lemma valid_stk_word_var_stk s1 s2 sz xn sz' xn' ofsx ofsx' m' w:
    let x := {| vtype := sword sz; vname := xn |} in
    Mvar.get m.1 x = Some ofsx ->
    let x' := {| vtype := sword sz'; vname := xn' |} in
    Mvar.get m.1 x' = Some ofsx' ->
    write_mem (emem s2) (pstk + wrepr _ ofsx) sz w = ok m' ->
    valid_stk_word (evm s1) (emem s2) pstk ofsx' sz' xn' ->
    valid_stk_word (evm s1).[x <- ok (pword_of_word w) ] m' pstk ofsx' sz' xn'.
  Proof.
    move=> vi Hget x Hget' Hm' [H H'].
    have Hvmem : valid_pointer (emem s2) (pstk + wrepr _ ofsx) sz by apply /Memory.writeV;eauto.
    split; first by rewrite (Memory.write_valid _ _ Hm').
    rewrite /= -/x => v; case: (vi =P x).
    + subst vi x; case => ? ?; subst.
      rewrite Fv.setP_eq => -[<-] /=; clarify.
      by exists erefl => /=; exact: (Memory.writeP_eq Hm').
    move/eqP => hvix.
    rewrite Fv.setP_neq // => Hread.
    rewrite (Memory.writeP_neq Hm'); first by exact: H'.
    split; eauto.
    case: (validm Hget) => sx [] [<-] {sx} [hw hw' hxal] /(_ _ _ _ hvix Hget' erefl) hdisj.
    case: (validm Hget') => sa [] [<-] {sa} [ha ha' haal] _.
    have : wunsigned (pstk + wrepr _ ofsx) = wunsigned pstk + ofsx.
    - by apply: (wunsigned_pstk_add hw (lt_of_add_le hw')).
    have haha : wunsigned (pstk + wrepr _ ofsx') = wunsigned pstk + ofsx'.
    - by apply: (wunsigned_pstk_add ha (lt_of_add_le ha')).
    lia.
  Qed.

  Lemma valid_stk_var_stk s1 s2 sz (w: word sz) m' xn ofs ii:
    let vi := {| v_var := {| vtype := sword sz; vname := xn |}; v_info := ii |} in
    Mvar.get m.1 vi = Some ofs ->
    write_mem (emem s2) (pstk + wrepr _ ofs) sz w = ok m' ->
    valid_stk (evm s1) (emem s2) pstk ->
    valid_stk (evm s1).[{| vtype := sword sz; vname := xn |} <- ok (pword_of_word w)] m' pstk.
  Proof.
    move=> vi Hget Hm' H x; move: H=> /(_ x).
    have Hvmem : valid_pointer (emem s2) (pstk + wrepr _ ofs) sz by apply /Memory.writeV;eauto.
    case Hget': (Mvar.get m.1 x)=> [ofs'|//].
    move: x Hget'=> [[| |sz' n| sz'] vn] //= Hget' H.
    + exact: (valid_stk_arr_var_stk Hget Hget' Hm').
    exact: (valid_stk_word_var_stk Hget Hget' Hm').
  Qed.

  Lemma valid_var_stk s1 xn sz w s2 m' ofs ii:
    valid s1 s2 ->
    write_mem (emem s2) (pstk + wrepr _ ofs) sz w = ok m' ->
    let vi := {| v_var := {| vtype := sword sz; vname := xn |}; v_info := ii |} in
    Mvar.get m.1 vi = Some ofs ->
    valid {|
      emem := emem s1;
      evm := (evm s1).[{| vtype := sword sz; vname := xn |} <- ok (pword_of_word w)] |}
      {| emem := m'; evm := evm s2 |}.
  Proof.
    move=> [] H1 H2 H3 H4 H5 Hpstk Hssz H6 Hm' vi Hget.
    have Hmem : valid_pointer (emem s2) (pstk + wrepr _ ofs) sz.
    + by apply/Memory.writeV; eauto.
    split=> //=.
    + move=> w' sz' Hvalid.
      have [sx [hsx [ho1 ho2 hal hdisj]]] := validm Hget.
      have [hov hal'] := pstk_add.
      rewrite (H2 _ _ Hvalid); symmetry; apply: (Memory.writeP_neq Hm').
      split; eauto.
      case: hsx => ?; subst sx.
      have : wunsigned (pstk + wrepr _ ofs) = wunsigned pstk + ofs.
      - by apply: (wunsigned_pstk_add ho1 (lt_of_add_le ho2)).
      have := H1 _ _ Hvalid.
      case/negP/nandP => /ZltP /Z.nlt_ge h; lia.
    + by move=> w' sz'; rewrite -H3 -(Memory.write_valid _ _ Hm').
    + move=> x Hx1 Hx2.
      rewrite Fv.setP_neq; first exact: H4.
      apply/negP=> /eqP ?; subst x.
      by rewrite /is_in_stk Hget in Hx1.
    + by have [<- _ _] := Memory.write_mem_stable Hm'.
    + by have [_ _ <-] := Memory.write_mem_stable Hm'.
    exact: (valid_stk_var_stk Hget Hm').
  Qed.

  Lemma check_var_stkW sz (vi vi': var_i) (s1 s2: estate) v v' e:
    check_var_stk m sz vi vi' e -> valid s1 s2 ->
    value_uincl v v' ->
    type_of_val v = sword sz ->
    forall s1', write_var vi v s1 = ok s1' ->
    exists s2' : estate, write_lval gd (Lmem sz vi' e) v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
  case: vi => -[] xt xn ii /andP [] /andP [] /eqP Hisvstk /= /eqP -> {xt}.
  case Hget: (Mvar.get _ _) => [ ofs | ] // /eqP -> {e} Hv.
  case: (Hv) => H1 H2 H3 H4 H5 Hpstk Hssz H6 Hu hty s1'.
  rewrite Hisvstk H5 /=.
  apply: rbindP=> /= vm'; apply: set_varP => //= w h.
  have [{h} w' [??] ]:= type_of_val_to_pword hty h; subst v w.
  have /= /(_ sz w') := value_uincl_word Hu .
  rewrite truncate_word_u => -> //=.
  move=> ? [?]; subst vm' s1' => /=.
  rewrite /zero_extend !wrepr_unsigned.
  have Hvmem: valid_pointer (emem s2) (pstk + wrepr _ ofs) sz.
  + rewrite H3; apply/orP; right; exact: valid_get_w Hget.
  have [m' Hm'] : exists m', write_mem (emem s2) (pstk + wrepr _ ofs) sz w' = ok m'.
  + by apply/Memory.writeV.
  exists {| emem := m'; evm := evm s2 |}; split.
  + by rewrite Hm' /=.
  exact: valid_var_stk Hv Hm' Hget.
  Qed.

  Lemma valid_map_arr_addr sz n xn off ofsx :
    Mvar.get m.1 {| vtype := sarr sz n; vname := xn |} = Some ofsx ->
    0 <= off < Z.pos n ->
    wunsigned (pstk + wrepr U64 (wsize_size sz * off + ofsx)) =
    wunsigned pstk + wsize_size sz * off + ofsx.
  Proof.
    move=> hget hoff;have [sx /= [[?] [??? _]]] := validm hget;subst sx.
    rewrite wunsigned_add;first by ring.
    case: pstk_add => ? _; have ? := wsize_size_pos sz.
    have ? := wunsigned_range pstk;nia.
  Qed.

  Lemma valid_map_word_addr sz xn ofsx: 
    Mvar.get m.1 {| vtype := sword sz; vname := xn |} = Some ofsx ->
    wunsigned (pstk + wrepr U64 ofsx) = wunsigned pstk + ofsx.
  Proof.
    move=> hget; have [sx /= [[?] [??? _]]] := validm hget;subst sx.
    apply wunsigned_add; case: pstk_add => ? _; have ? := wsize_size_pos sz.
    have ? := wunsigned_range pstk;nia.
  Qed.

  Lemma valid_stk_arr_arr_stk s1 s2 n n' sz xn sz' xn' ofsx ofsx' m' v0 i (a: Array.array n (word sz)) t:
    let x := {| vtype := sarr sz n; vname := xn |} in
    Mvar.get m.1 x = Some ofsx ->
    let x' := {| vtype := sarr sz' n'; vname := xn' |} in
    Mvar.get m.1 x' = Some ofsx' ->
    get_var (evm s1) x = ok (Varr a) ->
    valid_pointer (emem s2) (pstk + wrepr _ (wsize_size sz * i + ofsx)) sz ->
    write_mem (emem s2) (pstk + wrepr _ (wsize_size sz * i + ofsx)) sz v0 = ok m' ->
    Array.set a i v0 = ok t ->
    valid_stk_arr (evm s1) (emem s2) pstk ofsx' sz' n' xn' ->
    valid_stk_arr (evm s1).[x <- ok t] m' pstk ofsx' sz' n' xn'.
  Proof.
    move=> x Hget x' Hget' Ha Hvmem Hm' Ht.
    move=> H off Hoff.
    move: H=> /(_ off Hoff) [H /= H'].
    split=> //.
    - by rewrite (Memory.write_valid _ _ Hm').
    case: (x =P x').
    + subst x x'. case => ???; subst sz' n' xn' => a0.
      rewrite Fv.setP_eq => -[<-] {a0} v1 Hv1.
      rewrite Hget in Hget'; move: Hget'=> []?; subst ofsx'.
      move: (Ht).
      rewrite /Array.set; case: ifP => // /andP [] /ZleP Hi /ZltP Hi' [?]; subst t.
      move: Hv1; rewrite FArray.setP; case: eqP.
      * by move => <- [<-]; rewrite (Memory.writeP_eq Hm').
      move => hio Hv1.
      rewrite (Memory.writeP_neq Hm').
      * apply: (H' _ _ _ Hv1).
        by move: Ha; rewrite /get_var; apply: on_vuP => //= ? -> /Varr_inj1 ->.
      split; eauto.
      by rewrite !(valid_map_arr_addr Hget) //;nia.
    move => Hxx' a'.
    rewrite Fv.setP_neq; last by apply/eqP.
    move => /H'{H'}H' v /H'{H'}.
    rewrite (Memory.writeP_neq Hm') //.
    split; eauto.
    have Hi: 0 <= i < Z.pos n.
    + by move: (Ht);rewrite /Array.set;case:ifP => // /andP [/ZleP ? /ZltP ?].
    rewrite (valid_map_arr_addr Hget) // (valid_map_arr_addr Hget') //. 
    have [sx [/= [?] [??? H1]]]:= validm Hget;subst sx.
    have hxx' : x != x' by apply /eqP.
    have := H1 _ _ _ hxx' Hget' erefl.
    by have := wsize_size_pos sz; have := wsize_size_pos sz'; nia.
  Qed.

  Lemma valid_stk_word_arr_stk n xan sz xwn sz' ofsa ofsw (a: Array.array n (word sz)) m' s1 s2 t v0 i:
    let xa := {| vtype := sarr sz n; vname := xan |} in
    Mvar.get m.1 xa = Some ofsa ->
    let xw := {| vtype := sword sz'; vname := xwn |} in
    Mvar.get m.1 xw = Some ofsw ->
    get_var (evm s1) xa = ok (Varr a) ->
    valid_pointer (emem s2) (pstk + wrepr _ (wsize_size sz * i + ofsa)) sz ->
    write_mem (emem s2) (pstk + wrepr _ (wsize_size sz * i + ofsa)) sz v0 = ok m' ->
    Array.set a i v0 = ok t ->
    valid_stk_word (evm s1) (emem s2) pstk ofsw sz' xwn ->
    valid_stk_word (evm s1).[xa <- ok t] m' pstk ofsw sz' xwn.
  Proof.
    move=> xa Hgeta xw Hgetw Ha Hvmem Hm' Ht [H H'].
    split.
    + by rewrite (Memory.write_valid _ _ Hm').
    move=> /= v1 Hv1.
    rewrite Fv.setP_neq in Hv1; last by rewrite vtype_diff.
    have [e heq] := H' v1 Hv1;exists e;rewrite -heq.
    apply: (Memory.writeP_neq Hm').
    split; eauto.
    have Hi: 0 <= i < Z.pos n.
    + by move: (Ht);rewrite /Array.set;case:ifP => // /andP [/ZleP ? /ZltP ?].
    rewrite (valid_map_arr_addr Hgeta) // (valid_map_word_addr Hgetw) //. 
    have [sx [/= [?] [??? H1]]]:= validm Hgeta;subst sx.
    have hxx' : xa != xw by done.
    have := H1 _ _ _ hxx' Hgetw erefl.
    by have := wsize_size_pos sz; have := wsize_size_pos sz'; nia.
  Qed.

  Lemma valid_stk_arr_stk s1 s2 sz vn n m' v0 i ofs (a: Array.array n (word sz)) t:
    let vi := {| vtype := sarr sz n; vname := vn |} in
    Mvar.get m.1 vi = Some ofs ->
    get_var (evm s1) vi = ok (Varr a) ->
    valid_pointer (emem s2) (pstk + wrepr _ (wsize_size sz * i + ofs)) sz ->
    write_mem (emem s2) (pstk + wrepr _ (wsize_size sz * i + ofs)) sz v0 = ok m' ->
    Array.set a i v0 = ok t ->
    valid_stk (evm s1) (emem s2) pstk ->
    valid_stk (evm s1).[vi <- ok t] m' pstk.
  Proof.
  move=> vi Hget Ha Hvmem Hm' Ht H x; have := H x.
  case Heq: Mvar.get => [ ptr | // ].
  case: x Heq => -[] // => [ sz' n' | sz' ] xn Heq /=.
  + exact: (valid_stk_arr_arr_stk Hget Heq Ha Hvmem Hm' Ht).
  exact: (valid_stk_word_arr_stk Hget Heq Ha Hvmem Hm' Ht).
  Qed.

  Lemma valid_arr_stk sz n vn v0 i ofs s1 s2 m' (a: Array.array n (word sz)) t:
    let vi := {| vtype := sarr sz n; vname := vn |} in
    Mvar.get m.1 vi = Some ofs ->
    get_var (evm s1) vi = ok (Varr a) ->
    write_mem (emem s2) (pstk + wrepr _ (wsize_size sz * i + ofs)) sz v0 = ok m' ->
    Array.set a i v0 = ok t ->
    valid s1 s2 ->
    valid {| emem := emem s1; evm := (evm s1).[vi <- ok t] |}
          {| emem := m'; evm := evm s2 |}.
  Proof.
    move => vi Hget Ha Hm' Ht.
    have Hvmem : valid_pointer (emem s2) (pstk + wrepr _ (wsize_size sz * i + ofs)) sz.
    + by apply/Memory.writeV; eauto.
    case => H1 H2 H3 H4 H5 Hpstk Hssz H6.
    split => //=.
    + move=> w sz' Hvmem'. 
      rewrite (H2 _ _ Hvmem') //.
      symmetry; apply: (Memory.writeP_neq Hm').
      split; eauto.
      have Hi: 0 <= i < Z.pos n.
      + by move: (Ht);rewrite /Array.set;case:ifP => // /andP [/ZleP ? /ZltP ?].
      rewrite (valid_map_arr_addr Hget) //.
      have ?:= wsize_size_pos sz; have ?:= wsize_size_pos sz'.
      have [sx [/= [?] [??? ?]]]:= validm Hget.
      have /negP /nandP [ /ZltP| /ZltP ] := H1 _ _ Hvmem';nia.
    + move=> w' sz'.
      by rewrite (Memory.write_valid _ _ Hm') H3.
    + move=> x Hx1 Hx2.
      rewrite Fv.setP_neq.
      apply: H4=> //.
      apply/negP=> /eqP Habs.
      by rewrite -Habs /is_in_stk Hget in Hx1.
    + by have [<- _ _] := Memory.write_mem_stable Hm'.
    + by have [_ _ <-] := Memory.write_mem_stable Hm'.
    exact: (valid_stk_arr_stk Hget Ha Hvmem Hm' Ht).
  Qed.

  Lemma get_var_arr n sz (a: Array.array n (word sz)) vm vi:
    get_var vm vi = ok (Varr a) ->
    exists vn, vi = {| vtype := sarr sz n; vname := vn |}.
  Proof.
    move: vi=> [vt vn] //=.
    apply: on_vuP=> //= x Hx; rewrite /to_val.
    move: vt x Hx=> [] // sz' n' /= x Hx /Varr_inj [-> [?]]; subst => /= ?.
    by exists vn.
  Qed.

  Lemma check_arr_stkW sz (vi vi': var_i) (s1 s2: estate) v v' e e':
    check_arr_stk m sz vi e vi' e' -> valid s1 s2 ->
    value_uincl v v' ->
    forall s1', write_lval gd (Laset vi e) v s1 = ok s1' ->
    exists s2', write_lval gd (Lmem sz vi' e') v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move: vi=> [vi vii].
    case/andP=> /eqP hvi' /=.
    case: vi => -[] //= sz' n vi /andP[] /eqP -> {sz'}.
    case Hget: Mvar.get => [ ofs | // ] /is_addr_ofsP [i] [? ?]; subst e e' => Hval Hu s1'.
    case: (Hval); rewrite -hvi' => H1 H2 H3 H4 H5 Hpstk Hssz H6.
    apply on_arr_varP => sz' n' t' [] ??; subst sz' n' => Ha /=.
    t_xrbindP => v0 Hv0 t Ht vm.
    apply: set_varP => [ varr /to_arr_ok /Varr_inj1 <- {varr} <- <- | _] /=; last first.
    + by rewrite eq_dec_refl pos_dec_n_n /=.
    rewrite (value_uincl_word Hu Hv0) H5 /= /zero_extend !wrepr_unsigned /=.
    cut (exists m', write_mem (emem s2) (pstk + wrepr Uptr (wsize_size sz * i + ofs)) sz v0 = ok m').
    - case => m' Hm'; rewrite Hm' /=; eexists; split;first by reflexivity.
      exact: (valid_arr_stk Hget Ha Hm' Ht Hval).
    apply/Memory.writeV.
    case: (validm Hget) => sx [[<-]] {sx} [hofs hofs' hal hdisj].
    have hi := Array.setP_inv Ht.
    rewrite H3; apply/orP; right.
    have ? := wsize_size_pos sz; have [sx [/= [<-] [hle0 Hle _ _ ]]]:= validm Hget.
    have ? := wunsigned_range pstk;have [? hpstk] := pstk_add.
    rewrite /between wunsigned_add;last by nia.
    apply/andP;split;first by apply /andP;split;apply /ZleP;nia.
    rewrite hpstk;last by nia.
    by rewrite wrepr_add; apply: is_align_array.
  Qed.

  Lemma valid_stk_mem s1 s2 sz ptr off val m' m'2:
    write_mem (emem s1) (ptr + off) sz val = ok m' ->
    disjoint_zrange pstk stk_size (ptr + off) (wsize_size sz) ->
    write_mem (emem s2) (ptr + off) sz val = ok m'2 ->
    valid_stk (evm s1) (emem s2) pstk ->
    valid_stk (evm s1) m'2 pstk.
  Proof.
    move=> Hm' Hbound Hm'2 Hv x.
    have Hvalid : valid_pointer (emem s1) (ptr + off) sz.
    - by apply/Memory.writeV; eauto.
    move: Hv=> /(_ x).
    case Hget: (Mvar.get m.1 x)=> [offx|//].
    move: x Hget=> [[| | sz' n | sz'] vn] Hget //= H.
    + move=> off' Hoff'.
      move: H=> /(_ off' Hoff') [H H']; split.
      + by rewrite (Memory.write_valid _ _ Hm'2).
      move => t a Ht v0 Hv0.
      rewrite -(H' a Ht v0 Hv0).
      apply: (Memory.writeP_neq Hm'2).
      split; eauto.
      have hsz := wsize_size_pos sz; have hsz' := wsize_size_pos sz'.
      have [_ [[/= <-] [ hoffsx hsx _ _]]] := validm Hget.
      rewrite wunsigned_pstk_add; [ | nia | nia ].
      case: Hbound => _ _ []; nia.
    case: H => [H'' H']; split.
    + by rewrite (Memory.write_valid _ _ Hm'2).
    move=> v0 Hv0; have [e heq]:= H' v0 Hv0;exists e;rewrite -heq.
    apply: (Memory.writeP_neq Hm'2).
    split; eauto.
    have hsz := wsize_size_pos sz; have hsz' := wsize_size_pos sz'.
    have [_ [[/= <-] [ hoffsx hsx _ _]]] := validm Hget.
    rewrite wunsigned_pstk_add; [ | nia | nia ].
    case: Hbound => _ _ []; nia.
  Qed.

  Lemma valid_mem s1 s2 m' m'2 ptr off sz val:
    write_mem (emem s1) (ptr + off) sz val = ok m' ->
    write_mem (emem s2) (ptr + off) sz val = ok m'2 ->
    valid s1 s2 ->
    valid {| emem := m'; evm := evm s1 |} {| emem := m'2; evm := evm s2 |}.
  Proof.
    move=> Hm' Hm'2 [H1 H2 H3 H4 H5 Hpstk Hssz H6].
    split=> //=.
    + move=> sz' w Hw.
      rewrite (Memory.write_valid _ _ Hm') in Hw.
      exact: H1.
    + move=> w sz'.
      rewrite (Memory.write_valid _ _ Hm') => Hw.
      exact: Memory.read_write_any_mem Hw (H2 _ _ Hw) Hm' Hm'2.
    + by move=> w sz'; rewrite (Memory.write_valid w sz' Hm') (Memory.write_valid w sz' Hm'2).
    + by have [<- _ _] := Memory.write_mem_stable Hm'2.
    + by have [_ _ <-] := Memory.write_mem_stable Hm'2.
    apply: (valid_stk_mem Hm') (Hm'2) (H6).
    have Hvalid1: valid_pointer (emem s1) (ptr + off) sz.
    + apply/Memory.writeV; exists m'; exact: Hm'.
    split; eauto.
    + by case: pstk_add => /ZleP.
    case/negP/nandP: (H1 _ _ Hvalid1) => /ZltP; lia.
  Qed.

  Lemma check_memW sz (vi vi': var_i) (s1 s2: estate) v v' e e':
    check_var m vi vi' -> check_e m e e' -> valid s1 s2 -> 
    value_uincl v v' ->
    forall s1', write_lval gd (Lmem sz vi e) v s1 = ok s1'->
    exists s2', write_lval gd (Lmem sz vi' e') v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move => Hvar He Hv Hu s1'.
    case: (Hv) => H1 H2 H3 H4 H5 Hpstk Hssz H6.
    rewrite /write_lval; t_xrbindP => ptr wi hwi hwiptr ofs we he heofs w hvw.
    move => m' Hm' <- {s1'}.
    have [wi' [-> hwi']] := check_varP Hvar H4 hwi.
    rewrite /= (value_uincl_word hwi' hwiptr) /=.
    have [we' [-> hwe']] := check_eP He Hv he.
    rewrite /= (value_uincl_word hwe' heofs) /= (value_uincl_word Hu hvw) /=.
    have : exists m2', write_mem (emem s2) (ptr + ofs) sz w = ok m2'.
    + by apply: Memory.writeV; rewrite H3; apply /orP; left; apply/Memory.writeV; eauto.
    case => m2' Hm2'; rewrite Hm2' /=; eexists; split; first by reflexivity.
    exact: (valid_mem Hm').
  Qed.

  Lemma check_arrW (vi vi': var_i) (s1 s2: estate) v v' e e':
    check_var m vi vi' -> check_e m e e' -> valid s1 s2 -> value_uincl v v' ->
    forall s1', write_lval gd (Laset vi e) v s1 = ok s1'->
    exists s2', write_lval gd (Laset vi' e') v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    case: vi vi' => vi ivi [vi' ivi'].
    move=> Hvar He Hv Hu s1'.
    have Hv' := Hv.
    move: Hv'=> [] H1 H2 H3 H4 H5 Hpstk Hssz H6.
    apply: rbindP=> [[]] // sz n a Ha.
    t_xrbindP => i vali Hvali Hi v0 Hv0 t Ht vm.
    rewrite /set_var;apply: set_varP => //=;last first.
    + by have [xn /= ?] := get_var_arr Ha;subst vi => /= _; rewrite eq_dec_refl pos_dec_n_n.
    move=> varr Hvarr <- <- /=.
    have Hv'0 := value_uincl_word Hu Hv0.
    have [w [-> U]] := check_eP He Hv Hvali.
    have [??]:= value_uincl_int U Hi; subst vali w => /=.
    rewrite /= /on_arr_var.
    have [w [->]]:= check_varP Hvar H4 Ha.
    case: w => //= sz0 n0 a0 [?] [?]; subst n0 sz0 => /= Ha0.
    have Hvar' := Hvar; move: Hvar'=> /andP [/andP [Hnotinstk /eqP /= Heq] notstk].
    subst vi'. rewrite Hv'0 /=.
    have Ha0' : @val_uincl (sarr sz n) (sarr sz n) a a0.
    + by rewrite /val_uincl /=;split => //;exists erefl.
    have [t' [-> Htt'] /=]:= Array_set_uincl Ha0' Ht.
    rewrite /set_var /=.
    have Utt': value_uincl (@Varr sz n t) (Varr t').
    - split => //; exists erefl => /= ??.
      by case: Htt' => ? [e1 /=];rewrite (Eqdep_dec.UIP_dec wsize_eq_dec e1 erefl) /= => h/h.
    have [varr' [-> Uarr] /=]:= pof_val_uincl Utt' Hvarr.
    exists {| emem := emem s2; evm := (evm s2).[vi <- ok varr'] |}; split=> //.
    split=> //=.
    + exact: eq_vm_write.
    + rewrite /get_var Fv.setP_neq //.
    exact: valid_stk_write_notinstk.
  Qed.

  Lemma check_lvalP (r1 r2: lval) v v' ty (s1 s2: estate) :
    check_lval m r1 r2 ty -> valid s1 s2 -> 
    type_of_val v = ty -> value_uincl v v' ->
    forall s1', write_lval gd r1 v s1 = ok s1' ->
    exists s2', write_lval gd r2 v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Hr Hv Htr Hu; move: Hr.
    case: r1=> [vi t |vi|sz vi e|vi e].
    + case: r2=> // vi' t' /= /eqP -> s1' H.
      have [-> _]:= write_noneP H.
      by rewrite (uincl_write_none _ Hu H); exists s2.      
    + case: r2=> // [vi'|sz' vi' e].
      + move=> /check_varW /(_ Hv) H s1' Hw.
        by move: (H _ _ Hu _ Hw)=> [s2' Hs2']; exists s2'.
      rewrite /write_lval /= => /andP [/eqP hty];subst ty.
      move=> /check_var_stkW /(_ Hv) H s1' Hw.
      by move: (H _ _ Hu hty _ Hw)=> [s2' Hs2']; exists s2'.
    + case: r2=> // sz' vi' e'.
      move=> /andP [/andP [] /eqP ? Hvar He] s1' Hw; subst sz'.
      by move: (check_memW Hvar He Hv Hu Hw)=> [s2' Hs2']; exists s2'.
    case: r2=> // [ sz' | ] vi' e' /=.
    + move=> /check_arr_stkW /(_ Hv) H s1' Hw.
    move: (H _ _ Hu _ Hw)=> [s2' Hs2']; exists s2'=> //.
    move=> /andP [Hvar He] s1' Hw.
    move: (check_arrW Hvar He Hv Hu Hw)=> [s2' Hs2']; exists s2'=> //.
  Qed.

  Lemma check_lvalsP (r1 r2: lvals) vs vs' ty (s1 s2: estate) :
    all3 (check_lval m) r1 r2 ty -> valid s1 s2 ->
    seq.map type_of_val vs = ty -> 
    List.Forall2 value_uincl vs vs' ->
    forall s1', write_lvals gd s1 r1 vs = ok s1' ->
    exists s2', write_lvals gd s2 r2 vs' = ok s2' /\ valid s1' s2'.
  Proof.
    elim: r1 r2 ty vs vs' s1 s2=> //= [|a l IH] [|a' l'] // [ | ty tys] // [ | v vs] //.
    + move=> vs' ? s2 ? Hvalid _ /List_Forall2_inv_l -> {vs'} s1' [] <-.
      exists s2; split=> //.
    + move=> ? s1 s2 /andP [Hchecka Hcheckl] Hvalid [] hty htys /List_Forall2_inv_l [v'] [vs'] [->] [hv hvs] s1'.
      apply: rbindP=> x Ha Hl.
      move: (check_lvalP Hchecka Hvalid hty hv Ha)=> [s3 [Hs3 Hvalid']].
      move: (IH _ _ _ _ _ _ Hcheckl Hvalid' htys hvs _ Hl)=> [s3' [Hs3' Hvalid'']].
      by exists s3'; split=> //=; rewrite Hs3.
  Qed.

  Let Pi_r s1 (i1:instr_r) s2 :=
    forall ii1 ii2 i2, check_i m (MkI ii1 i1) (MkI ii2 i2) ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem_i SP gd s1' i2 s2' /\ valid s2 s2'.

  Let Pi s1 (i1:instr) s2 :=
    forall i2, check_i m i1 i2 ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem_I SP gd s1' i2 s2' /\ valid s2 s2'.

  Let Pc s1 (c1:cmd) s2 :=
    forall c2, all2 (check_i m) c1 c2 ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem SP gd s1' c2 s2' /\ valid s2 s2'.

  Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.

  Let Pfun (m1: mem) (fn: funname) (vargs: seq value) (m2: mem) (vres: seq value) := True.

  Local Lemma Hskip : sem_Ind_nil Pc.
  Proof.
    move=> s [] // => _ s' Hv.
    exists s'; split; [exact: S.Eskip|exact: Hv].
  Qed.

  Local Lemma Hcons : sem_Ind_cons P Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ Hi _ Hc [|i' c'] //= /andP [Hi'c Hc'c] s1' Hv.
    have [s2' [Hi' Hv2]] := Hi _ Hi'c _ Hv.
    have [s3' [Hc' Hv3]] := Hc _ Hc'c _ Hv2.
    exists s3'; split=> //.
    apply: S.Eseq; [exact: Hi'|exact: Hc'].
  Qed.

  Local Lemma HmkI : sem_Ind_mkI P Pi_r Pi.
  Proof.
    move=> ii i s1 s2 _ Hi [ii' ir'] Hc s1' Hv.
    move: Hi=> /(_ ii ii' ir' Hc s1' Hv) [s2' [Hs2'1 Hs2'2]].
    by exists s2'; split.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn P Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' hv htr Hw ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= x' a ty' e' /andP [/andP []] Hlval /eqP ? He;subst ty'.
    have [v1 [He' Uvv1]] := (check_eP He Hvalid hv).
    have [v1' [htr' Uvv1']]:= truncate_value_uincl Uvv1 htr.
    have hty := truncate_val_has_type htr.
    move: (check_lvalP Hlval Hvalid hty Uvv1' Hw)=> [s2' [Hw' Hvalid']].
    exists s2'; split=> //.
    apply: S.Eassgn;eauto.
  Qed.

  Local Lemma Hopn : sem_Ind_opn P Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    rewrite /sem_sopn;t_xrbindP => vs va He Hop Hw ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= xs' t' o' es' /andP [/andP [Hlvals /eqP Ho] Hes].
    have [va' [He' Uvv']] := (check_esP Hes Hvalid He);subst o'.
    have [w' [Hop' Uww']]:= vuincl_exec_opn Uvv' Hop.
    have [s2' [Hw' Hvalid']] := check_lvalsP Hlvals Hvalid (sopn_toutP Hop) Uww' Hw.
    exists s2'; split=> //.
    by apply: S.Eopn;rewrite /sem_sopn He' /= Hop'.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true P Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c1' c2' /andP [/andP [He Hcheck] _].
    move: (Hc _ Hcheck _ Hvalid)=> [s2' [Hsem Hvalid']].
    exists s2'; split=> //.
    apply: S.Eif_true=> //.
    have [v' [-> ]]:= check_eP He Hvalid Hse.
    by move=> /value_uincl_bool /= -/(_ _ erefl) [_ ->].
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false P Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c1' c2' /andP [/andP [He _] Hcheck].
    move: (Hc _ Hcheck _ Hvalid)=> [s2' [Hsem Hvalid']].
    exists s2'; split=> //.
    apply: S.Eif_false=> //.
    have [v' [-> ]]:= check_eP He Hvalid Hse.
    by move=> /value_uincl_bool /= -/(_ _ erefl) [_ ->].
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true P Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 c e c' _ Hc Hv ? Hc' ? Hwhile ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= c2 e2 c2' /andP [/andP [Hc2 He2] Hc2'].
    move: (Hc _ Hc2 _ Hvalid)=> [s2' [Hsem' Hvalid']].
    move: (Hc' _ Hc2' _ Hvalid')=> [s2'' [Hsem'' Hvalid'']].
    have [|s3' [Hsem''' Hvalid''']] := (Hwhile ii1 ii2 (Cwhile c2 e2 c2') _ _ Hvalid'').
    + by rewrite /= Hc2 He2 Hc2'.
    exists s3'; split=> //.
    apply: S.Ewhile_true; eauto.
    have [v' [-> ]]:= check_eP He2 Hvalid' Hv.
    by move=> /value_uincl_bool /= -/(_ _ erefl) [_ ->].    
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false P Pc Pi_r.
  Proof.
    move=> s1 s2 c e c' _ Hc Hv ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= c2 e2 c2' /andP [/andP [Hc2 He2] _].
    move: (Hc _ Hc2 _ Hvalid)=> [s2' [Hsem' Hvalid']].
    exists s2'; split=> //.
    apply: S.Ewhile_false; eauto.
    have [v' [-> ]]:= check_eP He2 Hvalid' Hv.
    by move=> /value_uincl_bool /= -/(_ _ erefl) [_ ->].
  Qed.

  Local Lemma Hfor : sem_Ind_for P Pi_r Pfor.
  Proof. by []. Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. by []. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P Pc Pfor.
  Proof. by []. Qed.

  Local Lemma Hcall : sem_Ind_call P Pi_r Pfun.
  Proof. by []. Qed.

  Local Lemma Hproc : sem_Ind_proc P Pc Pfun.
  Proof. by []. Qed.

  Lemma check_cP s1 c s2: sem P s1 c s2 -> Pc s1 c s2.
  Proof.
    apply (@sem_Ind P Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.
End PROOF.

Lemma init_mapP nstk l sz m m1 m2 :
  alloc_stack m1 sz = ok m2 ->
  init_map sz nstk l = ok m -> 
  valid_map m sz /\ m.2 = nstk.
Proof.
  move=> /Memory.alloc_stackP [Hadd Hread Hval Hbound].
  rewrite /init_map.
  set f1 := (f in foldM f _ _ ).
  set g := (g in foldM _ _ _ >>= g). 
  have : forall p p',
    foldM f1 p l = ok p' -> 
    valid_map (p.1,nstk) p.2 -> 0 <= p.2 ->
    (forall y py sy, Mvar.get p.1 y = Some py ->
        size_of (vtype y) = ok sy -> py + sy <= p.2) ->
    (p.2 <= p'.2 /\
        valid_map (p'.1, nstk) p'.2).
  + elim:l => [|[v pn] l Hrec] p p'//=.
    + by move=>[] <- ???;split=>//;omega.
    case:ifPn=> //= /Z.leb_le Hle.
    case: ifP => // Hal.
    case Hs : size_of=> [svp|]//= /Hrec /= {Hrec}Hrec H2 H3 H4. 
    have Hpos := size_of_pos Hs.
    case:Hrec.
    + move=> x px;rewrite Mvar.setP;case:ifPn => /eqP Heq.
      + move=> [] ?;subst;exists svp;split=>//;split => //.
        + omega. + omega.
        move=> y py sy Hne.
        by rewrite Mvar.setP_neq // => /H4 H /H ?;omega.
      move=> /H2 [sx] [Hsx] [] Hle0 Hpx Hal' Hy;exists sx;split=>//;split=>//.
      + omega.
      move=> y py sy Hne;rewrite Mvar.setP;case:eqP=> [?[]? |].
      + subst;rewrite Hs => -[] ?;subst; omega.
      by move=> Hney;apply Hy.
    + omega.
    + move=> y py sy;rewrite Mvar.setP;case:eqP=> [?[]?|].
      + subst;rewrite Hs => -[] ->;omega.
      move=> ? /H4 H /H ?;omega.
    move=> Hle2 H';split=>//;first by omega.
  move=> H;case Heq : foldM => [p'|]//=.
  case: (H _ _ Heq)=> //= Hp' Hv.
  rewrite /g;case:ifP => //= /Z.leb_le Hp Hq Hr Hs [<-].
  split=>// x px Hx.
  case :(Hv x px Hx) => //= sx [] Hsx [] H1 H2 H3.
  by exists sx;split=>//;split=>//;omega.
Qed.

Lemma check_fdP (P: prog) (SP: sprog) l fn fn' fd fd':
  get_fundef (p_funcs P) fn = Some fd ->
  get_fundef SP fn' = Some fd' ->
  check_fd l fd fd' ->
  forall m1 va m1' vr, 
    sem_call P m1 fn va m1' vr ->
    (exists p, alloc_stack m1 (sf_stk_sz fd') = ok p) ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      eq_mem m1' m2' /\
      S.sem_call SP (p_globs P) m1 fn' va m2' vr'.
Proof.
  move=> get Sget.
  rewrite /check_fd.
  case Hinit: init_map => [m|] //= /andP[]/andP[] /andP[] /andP[] /eqP Htyin /eqP Htyout Hp Hr Hi.
  move=> m1 va m1' vr /sem_callE [f] [].
  rewrite get => - [<-] {f} [vargs] [s1] [vm2] [vres] [hvargs hs1 hbody hvres hvr] [m2 Halloc].
  have [/= Hv Hestk] := init_mapP Halloc Hinit.
  have Hstk: stk_ok (top_stack m2) (sf_stk_sz fd').
  + by move: Halloc=> /Memory.alloc_stackP [].
  have Hval'': valid m (sf_stk_sz fd') (top_stack m2) 
          {| emem := m1; evm := vmap0 |} 
           {| emem := m2; evm := vmap0.[{| vtype := sword Uptr; vname := sf_stk_id fd' |} <- ok (pword_of_word (top_stack m2))] |}.
    move: Halloc=> /Memory.alloc_stackP [] Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Ha7.
    split=> //=.
    + move => w sz hv; apply/negP/nandP.
      case: (Ha5 _ _ hv) => h; [ left | right ]; apply/ZltP; lia.
    + move=> x.
      case Heq: (x == {| vtype := sword Uptr; vname := sf_stk_id fd' |}).
      + move: Heq=> /eqP -> /=.
        rewrite /is_vstk /vstk.
        by rewrite Hestk eq_refl.
      + rewrite Fv.setP_neq=> //.
        apply/eqP=> Habs.
        by rewrite Habs eq_refl in Heq.
      + by rewrite /vstk Hestk /= /get_var Fv.setP_eq.
      + by rewrite Ha7 eq_refl.
      move=> x.
      case Hget: (Mvar.get m.1 x)=> [a|//].
      case Htype: (vtype x)=> [| |sz n| sz] //.
      + move=> off Hoff; split.
        + rewrite Ha3; apply/orP; right.
          case: (Hv _ _ Hget) => q []; rewrite Htype /= => - [] ?; subst q => - [] hal hah haa _.
          have hsz := wsize_size_pos sz.
          apply/andP; split.
          * rewrite  /between (wunsigned_pstk_add Hstk); [ | nia | nia ].
            apply/andP; split; apply/ZleP; nia.
          have := @is_align_array Memory.A (@top_stack _ Memory.M m2 + wrepr _ a) sz off.
          rewrite Ha4; last by nia.
          move => /(_ haa).
          set q := (top_stack _ + wrepr _ (_ + _))%R.
          replace (wrepr _ _ + _)%R with q. done.
          subst q; rewrite wrepr_add; ssrring.ssring.
        by rewrite /vmap0 Fv.get0 => t [<-] {t} ?; rewrite FArray.get0.
      case: x Htype Hget => - [] // sz' x [] -> {sz'} Hget.
      split.
      + rewrite Ha3; apply/orP; right.
        exact: (valid_get_w Hstk Hv Hget).
      by move=> v;rewrite /vmap0 Fv.get0.
  have := check_varsW Hp Hval'' _ hs1.
  move=> /(_ vargs) [ |s2 [Hs2 Hv2]];first by apply List_Forall2_refl.
  have [[m2' vm2'] [Hs2' Hv2']] := check_cP SP Hstk Hv hbody Hi Hv2.
  case: Hv2' => /= Hdisj Hmem Hval Heqvm _ Htopstack Hstacksize _.
  have [vr' [/= hvr' hvruincl]] := check_varsP Hr Heqvm hvres.
  have [vr'' [hvr'' hvruincl']] := mapM2_truncate_val hvr hvruincl.
  exists (free_stack m2' (sf_stk_sz fd')), vr''. split; first exact: hvruincl'.
  split.
  + move => w sz.
    pose stk_sz := sf_stk_sz fd'.
    have hts : frame_size m2' (top_stack m2') = Some stk_sz.
    + by rewrite Htopstack Hstacksize.
    have [hrd hvld hcllr hcllstk hfs] := Memory.free_stackP hts.
    move: (Hdisj w sz) (Hmem w sz) (Hval w sz)=> {Hdisj Hmem Hval} Hdisjw Hmemw Hvalw.
    case Heq1: (read_mem m1' w sz) => [w'| err].
    + have Hw : valid_pointer m1' w sz by apply /Memory.readV;exists w'.
      rewrite -Heq1 -hrd; first exact: Hmemw.
      rewrite hvld Hvalw.
      split; first by rewrite Hw.
      rewrite Htopstack.
      have [noo _ _ _ _ _ _] := Memory.alloc_stackP Halloc.
      constructor; eauto.
      + by apply/ZleP.
      case/negP/nandP: (Hdisjw Hw) => /ZltP; rewrite /stk_sz; lia.
    have ? := Memory.read_mem_error Heq1. subst err.
    case Heq2: (read_mem _ _ _) => [w'|];last by rewrite (Memory.read_mem_error Heq2).
    case/read_mem_valid_pointer/hvld: Heq2 => k [_ _ k'].
    move: Hvalw; set b := between _ _ _ _.
    replace b with false.
    + by rewrite k orbF => /esym /Memory.readV [] ?; rewrite Heq1.
    subst b stk_sz; rewrite -Htopstack /between; symmetry.
    have Hsz := wsize_size_pos sz.
    apply/nandP; case: k' => k'; [ right | left ]; apply/ZleP; lia.
  apply: S.EcallRun.
  + exact: Sget.
  + exact: Halloc.
  + exact: erefl.
  + rewrite -Htyin; exact: hvargs.
  + move: Hs2; rewrite /pword_of_word (Eqdep_dec.UIP_dec Bool.bool_dec (cmp_le_refl U64)); exact: id.
  + exact: Hs2'.
  + exact: hvr'.
  + rewrite -Htyout; exact: hvr''.
  reflexivity.
Qed.

Definition alloc_ok SP fn m1 :=
  forall fd, get_fundef SP fn = Some fd ->
  exists p, alloc_stack m1 (sf_stk_sz fd) = ok p.

Lemma check_progP (P: prog) (SP: sprog) l fn:
  check_prog (p_funcs P) SP l ->
  forall m1 va m1' vr, 
    sem_call P m1 fn va m1' vr ->
    alloc_ok SP fn m1 ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      eq_mem m1' m2' /\
      S.sem_call SP (p_globs P) m1 fn va m2' vr'.
Proof.
  move=> Hcheck m1 va m1' vr [] {m1 va m1' vr fn}
    m1 m2 fn f vargs vargs' s1 vm2 vres vres' Hf e0 e1 s e2 e3 Halloc.
  move: (all_progP Hcheck Hf)=> [fd' [l' [Hfd' Hl']]].
  have H : sem_call P m1 fn vargs' m2 vres' by econstructor; eauto.
  by case: (check_fdP Hf Hfd' Hl' H); eauto.
Qed.
