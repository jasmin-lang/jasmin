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
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
Local Open Scope Z_scope.

(* --------------------------------------------------------------------------- *)

Lemma size_of_pos t s : size_of t = ok s -> (1 <= s).
Proof.
  case: t => //= [p [] <-| sz [] <-]; first by lia.
  have hsz := wsize_size_pos sz; nia.
Qed.

Definition stk_ok (w: pointer) (z:Z) :=
  wunsigned w + z <= wbase Uptr /\
  forall ofs s,
(*    (0 <= ofs /\ ofs + wsize_size s <= z)%Z -> *)
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

  Definition valid_stk_arr (vm1:vmap) (m2:mem) (pstk: pointer) (p: Z) s vn :=
    forall off, (0 <= off < Zpos s)%Z ->
      valid_pointer m2 (pstk + (wrepr _ (off + p))) U8 /\
      let t := vm1.[{| vtype := sarr s; vname := vn |}] in
      forall a, t = ok a ->
        forall v, WArray.get U8 a off = ok v ->
          read_mem m2 (pstk + (wrepr _ (off + p))) U8 = ok v.

  Definition valid_stk (vm1:vmap) (m2:mem) pstk :=
    forall x,
      match Mvar.get m.1 x with
      | Some p =>
        match vtype x with
        | sword sz => valid_stk_word vm1 m2 pstk p sz (vname x)
        | sarr s => valid_stk_arr vm1 m2 pstk p s (vname x)
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
      (ohead (frames (emem s2)) = Some (pstk, stk_size)) &
      (valid_stk (evm s1) (emem s2) pstk)
  .

  Lemma check_varP vm1 vm2 x v:
    check_var m x -> eq_vm vm1 vm2 ->
    get_var vm1 x = ok v ->
    exists v', get_var vm2 x = ok v' /\ value_uincl v v'.
  Proof.
    move=> /andP [ Hin_stk Hnot_vstk] Heq Hget.
    have := Heq _ Hin_stk Hnot_vstk.
    move: Hget;rewrite /get_var; apply: on_vuP => [t | ] -> //=.
    by move=> <-;case vm2.[x] => //= s Hs;exists (pto_val s).
  Qed.

  Lemma check_varsP vm1 vm2 xs vs:
    all (check_var m) xs -> eq_vm vm1 vm2 ->
    mapM (fun x : var_i => get_var vm1 x) xs = ok vs ->
    exists vs',
      mapM (fun x : var_i => get_var vm2 x) xs = ok vs' /\
      List.Forall2 value_uincl vs vs'.
  Proof.
    elim: xs vs=> [|a l IH] //= vs.
    + move=> _ Heq [<-];by exists [::].
    move=> /andP [Ha Hl] Heq.
    apply: rbindP => va /(check_varP Ha Heq) [v' [-> Hu]].
    apply: rbindP => tl  /(IH _ Hl Heq) [tl' [-> Hus]] [<-] /=.
    by exists (v' :: tl');split=>//;constructor.
  Qed.

  (* TODO: MOVE *)

  Lemma cast_ptrP s e i : sem_pexpr gd s e = ok (Vint i) ->
    sem_pexpr gd s (cast_ptr e) = ok (Vword (wrepr U64 i)).
  Proof. by move=> h;rewrite /cast_ptr /cast_w /= h. Qed.

  Lemma cast_wordP s e i : sem_pexpr gd s e = ok (Vint i) ->
    exists sz (w:word sz), sem_pexpr gd s (cast_word e) = ok (Vword w) /\
                           truncate_word U64 w = ok (wrepr U64 i).
  Proof.
    move=> he.
    have : exists sz (w:word sz),
                sem_pexpr gd s (cast_ptr e) = ok (Vword w) /\
                        truncate_word U64 w = ok (wrepr U64 i).
    + exists U64, (wrepr U64 i); split; first by apply cast_ptrP.
      by rewrite truncate_word_u.
    case: e he => // -[] // [] //=.
    move=> e he _; move: he; rewrite /sem_sop1 /=; t_xrbindP => v -> w.
    case v => //= [sw w'| []//] /truncate_wordP [hsw ->] <-.
    by exists sw, w'; split => //; rewrite /truncate_word hsw wrepr_unsigned.
  Qed.

  Lemma mk_ofsP sz s2 ofs e i :
    sem_pexpr gd s2 e = ok (Vint i) ->
    sem_pexpr gd s2 (mk_ofs sz e ofs) = ok (Vword (wrepr U64 (i * wsize_size sz + ofs)%Z)).
  Proof.
    rewrite /mk_ofs; case is_constP => /= [? [->] //| {e} e he] /=.
    rewrite /sem_sop2 /=.
    have [sz' [w [-> /= -> /=]]]:= cast_wordP he.
    by rewrite !zero_extend_u wrepr_add wrepr_mul GRing.mulrC.
  Qed.

(* Move this *)
  Lemma subtypeEl ty ty': subtype ty ty' →
    match ty with
    | sbool => ty' = sbool
    | sint => ty' = sint
    | sarr n => ∃ n' : positive, ty' = sarr n' ∧ n <= n'
    | sword sz => ∃ sz' : wsize, ty' = sword sz' ∧ (sz ≤ sz')%CMP
    end.
  Proof.
    (case: ty => /= [/eqP <-|/eqP <-| p | sz ] //;
     case: ty') => // [p' /ZleP ? | sz' ?]; eauto.
  Qed.

  Lemma validr_valid_pointer (m1:mem) p ws : is_ok (validr m1 p ws) = valid_pointer m1 p ws.
  Proof.
    case: (Memory.readV m1 p ws); rewrite Memory.readP /CoreMem.read.
    + by move=> [w]; case: validr.
    by case: validr => //= _ [];eauto.
  Qed.

  Lemma get_arr_read_mem vm mem ofs (n:positive) (t : WArray.array n) xn1 ws i w:
    Mvar.get m.1 {|vtype := sarr n; vname := xn1|} = Some ofs ->
    valid_stk_arr vm mem pstk ofs n xn1 ->
    is_align (wrepr U64 ofs) ws ->
    vm.[{| vtype := sarr n; vname := xn1 |}] = ok t ->
    WArray.get ws t i = ok w ->
    read_mem mem (pstk + wrepr U64 (i * wsize_size ws + ofs)) ws = ok w.
  Proof.
    move=> hm hvalid halign hvget hget.
    rewrite Memory.readP /CoreMem.read.
    have hbound := WArray.get_bound hget.
    have hv : valid_pointer mem (pstk + wrepr U64 (i * wsize_size ws + ofs)) ws.
    + apply Memory.is_align_valid_pointer.
      + by case: pstk_add => ? ->; rewrite Z.mul_comm wrepr_add is_align_array.
      move=> k hk; have [] := hvalid  (i * wsize_size ws + k).
      + by nia.
      by rewrite -Z.add_assoc (Z.add_comm k) Z.add_assoc wrepr_add GRing.addrA.
    have := validr_valid_pointer mem (pstk + wrepr U64 (i * wsize_size ws + ofs))%R ws.
    rewrite hv; case: validr => //= _ _.
    move: (hget);rewrite /WArray.get /CoreMem.read; t_xrbindP => ? _ <-.
    do 2 f_equal; rewrite /CoreMem.uread.
    apply eq_map_ziota => k hk /=.
    have [v]:= WArray.get_get8 hget hk.
    have []/= := hvalid (i * wsize_size ws + k);first nia.
    move=> hva /(_ _ hvget) h /dup [] /h h1 /WArray.get_uget ->.
    move: h1; rewrite Memory.readP /CoreMem.read.
    t_xrbindP=> ??; rewrite CoreMem.uread8_get => <-; f_equal.
    by rewrite Memory.addP !wrepr_add; ssrring.ssring.
  Qed.

  Section CHECK_E_ESP.
    Context s s' (Hv: valid s s').

    Let X e : Prop :=
      ∀ e' v,
        alloc_e m e = ok e' →
        sem_pexpr gd s e = ok v →
        ∃ v', sem_pexpr gd s' e' = ok v' ∧ value_uincl v v'.

    Let Y es : Prop :=
      ∀ es' vs,
        mapM (alloc_e m) es = ok es' →
        sem_pexprs gd s es = ok vs →
        ∃ vs', sem_pexprs gd s' es' = ok vs' ∧ List.Forall2 value_uincl vs vs'.

    Lemma check_e_esP : (∀ e, X e) * (∀ es, Y es).
    Proof.
      have Hvm: eq_vm (evm s) (evm s') by move: Hv => -[].
      apply: pexprs_ind_pair; subst X Y; split => /=.

      - by move=> ?? [<-] [<-];exists [::].

      - move=> e he es hes ??; t_xrbindP => e' /he{he}he es' /hes{hes}hes <-.
        move=> ? /he [v' /= [->]] /= vu ? /hes [vs1' [->]] uvs <- /=.
        by exists (v'::vs1');split => //;constructor.

      + by move=> z1 e2 v [<-] [<-]; exists z1.
      + by move=> b1 e2 v [<-] [<-]; exists b1.
      + by move=> n1 e2 v [<-] [<-]; eexists; split; first reflexivity.

      + move=> v1 e2 v;case heq: Mvar.get => [ofs | ]; last first.
        + case his : is_vstk => // -[<-].
          by apply check_varP => //; rewrite /check_var /is_in_stk heq his.
        case hw : is_word_type => [ws | //].
        have hty := is_word_typeP hw => {hw}.
        case: (Hv) => _ _ _ _ hstk _ /(_ v1); rewrite heq hty => hv [<-] /=.
        case: v1 hty heq hv => /= -[xty x] vi /= ? heq hv; subst xty.
        rewrite hstk /get_var /= !zero_extend_u.
        case: hv => /Memory.readV [v0 hvp] hget; apply: on_vuP => //=.
        by move=> [ws' w wp] /hget /= [e] -> /= <-; subst ws' => /=; exists (Vword w).

      + by move=> g1 e2 v [<-] /= ->; eexists; split; first reflexivity.

      + move=> sz1 [[tv1 nv1] vi1] e1 IH e2 v; t_xrbindP => e1' /IH hrec.
        case heq: Mvar.get => [ofs | ]; last first.
        + case his : is_vstk => // -[<-].
          apply: on_arr_varP=> n t Ht Harr /=; rewrite /on_arr_var.
          have [|v' [-> Hu] /=] := check_varP _ Hvm Harr.
          + by rewrite /check_var /is_in_stk heq his.
          t_xrbindP => i ve /hrec [ve' [-> hve]] /(value_uincl_int hve) [??];subst ve ve'=> /=.
          move=> w hw <-.
          case: v' Hu => //= n' a hincl; have -> /= := WArray.uincl_get hincl hw.
          by exists (Vword w); split => //; exists erefl.
        case:ifP=> //= halign [<-].
        apply: on_arr_varP => n t hsubt hget.
        t_xrbindP => i ve /hrec [ve' [hve' sve']] /(value_uincl_int sve') [??].
        move=> w hti ?; subst v ve ve' => /=.
        set v1 := {| vtype := tv1; vname := nv1 |}.
        case: (Hv) => _ _ _ _ hstk _ /(_ v1); rewrite heq.
        have [n' [/= heqt hnn']]:= subtypeEl hsubt; subst tv1.
        rewrite (mk_ofsP sz1 ofs hve') /= !zero_extend_u.
        rewrite hstk /= zero_extend_u => hva.
        move: hget;rewrite /get_var; apply on_vuP => //= t1 ht1 /Varr_inj.
        move=> [e]; subst n' => /= ?;subst t.
        rewrite (get_arr_read_mem heq hva halign ht1 hti) /=.
        by (eexists;split;first reflexivity) => /=.

      + move=> sz1 v1 e1 IH e2 v.
        case:ifP => // hc; t_xrbindP => e1' /IH hrec <- wv1 vv1 /= hget hto' we1 ve1.
        move=> /hrec [ve1' [->] hu] /= hto wr hr ?;subst v.
        have [vv1' [-> hu'] /=]:= check_varP hc Hvm hget.
        rewrite (value_uincl_word hu hto) (value_uincl_word hu' hto') /=.
        have hv:= read_mem_valid_pointer hr.
        case: Hv => _ /(_ _ _ hv) <- _ _ _ _ _.
        by rewrite hr /=;eexists;(split;first by reflexivity) => /=.

      + move=> o1 e1 IH e2 v.
        t_xrbindP => e1' /IH hrec <- ve1 /hrec [ve1' /= [-> hu] /=] /(vuincl_sem_sop1 hu) ->.
        by eexists;split;first by reflexivity.

      + move=> o1 e1 H1 e1' H1' e2 v.
        t_xrbindP => e1_ /H1 hrec e1'_ /H1' hrec' <- ve1 /hrec.
        move=> [ve1' /= [-> hu] /=] ve2 /hrec' [ve2' /= [-> hu'] /=] .
        move=> /(vuincl_sem_sop2 hu hu') ->.
        by eexists;split;first by reflexivity.

      + move => e1 es1 H1 e2 v.
        t_xrbindP => es1' /H1{H1}H1 <- vs /H1{H1} /= [vs' []].
        rewrite /sem_pexprs => -> /= h1 h2.
        by have [v' ??]:= (vuincl_sem_opN h2 h1);exists v'.

      move=> t e He e1 H1 e1' H1' e2 v.
      t_xrbindP => e_ /He he e1_ /H1 hrec e1'_ /H1' hrec' <-.
      move=> b vb /he [vb' /= [-> ub]] /(value_uincl_bool ub) [??];subst vb vb'.
      move=> vte1 ve1 /hrec [ve1' /= [-> hu] /=] ht1 vte2 ve2 /hrec' [ve2' /= [-> hu'] /=] ht2 <-.
      have [? -> ?] := truncate_value_uincl hu ht1.
      have [? -> ? /=] := truncate_value_uincl hu' ht2.
      eexists;split;first by reflexivity.
      by case: (b).
    Qed.

  End CHECK_E_ESP.

  Definition alloc_eP e e' s s' v he hv :=
    (@check_e_esP s s' hv).1 e e' v he.

  Definition alloc_esP es es' s s' vs hs hv :=
    (@check_e_esP s s' hv).2 es es' vs hs.

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
    case Htype: (vtype x)=> // [p|].
    + move=> H off Hoff.
      move: H=> /(_ off Hoff) [H H'].
      split=> //.
      move=> t a0 Ht v0 Haget.
      rewrite /= in H'.
      have Hvma: (evm s1).[{| vtype := sarr p; vname := vname x |}] = ok a0.
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

  Lemma check_varW (vi : var_i) (s1 s2: estate) v v':
    check_var m vi -> valid s1 s2 -> value_uincl v v' ->
    forall s1', write_var vi v s1 = ok s1' ->
    exists s2', write_var vi v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> /andP [ Hnotinstk Hnotstk] Hval Hu s1'.
    rewrite /write_var; apply: rbindP=> z /=; apply: set_varP;rewrite /set_var.
    + move=> t /(pof_val_uincl Hu) [t' [-> Htt']] <- [<-] /=.
      eexists;split;first reflexivity.
      by apply valid_set_uincl.
    case: vi Hnotinstk Hnotstk => -[tvi nvi] vii /= Hnotinstk Hnotstk.
    move=> /is_sboolP ?; subst tvi => /= /to_bool_undef ?; subst v => <- [<-].
    by have [-> | [b1 ->]] /=:= pof_val_undef Hu erefl;
     (eexists;split;first reflexivity); apply valid_set_uincl.
  Qed.

  Lemma check_varsW (vi : seq var_i) (s1 s2: estate) v v':
    all (check_var m) vi -> valid s1 s2 ->
    List.Forall2 value_uincl v v' ->
    forall s1', write_vars vi v s1 = ok s1' ->
    exists s2', write_vars vi v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    elim: vi v v' s1 s2 => [|a l IH] //= [|va vl] [|va' vl'] s1 s2 //=.
    + by move=> _ Hv _ s1' []<-; exists s2.
    + by move => _ _ /List_Forall2_inv_l /seq_eq_injL.
    + by move => _ _ /List_Forall2_inv_r /seq_eq_injL.
    move=> /andP [Ha Hl] Hv /List_Forall2_inv_l [va''] [vl''] [] /seq_eq_injL [??]; subst va'' vl'' => - [] hva hvl s1'.
    apply: rbindP=> x Hwa.
    move: (check_varW Ha Hv hva Hwa)=> [s2' [Hs2' Hv2']] Hwl.
    move: (IH _ _ _ _ Hl Hv2' hvl _ Hwl)=> [s3' [Hs3' Hv3']].
    by exists s3'; split=> //; rewrite Hs2' /= Hs3'.
  Qed.

  Lemma wunsigned_pstk_add ofs :
    0 <= ofs -> ofs < stk_size ->
    wunsigned (pstk + wrepr Uptr ofs) = wunsigned pstk + ofs.
  Proof.
    move => p1 p2; apply: wunsigned_add.
    case: (pstk_add) => h _; have := wunsigned_range pstk; lia.
  Qed.

  Lemma lt_of_add_le x y sz :
    x + wsize_size sz <= y -> x < y.
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

  Lemma valid_stk_arr_var_stk s1 s2 sz xwn xan ofsw ofsa n w m':
    let xw := {| vname := xwn; vtype := sword sz |} in
    Mvar.get m.1 xw = Some ofsw ->
    let xa := {| vname := xan; vtype := sarr n |} in
    Mvar.get m.1 xa = Some ofsa ->
    write_mem (emem s2) (pstk + wrepr _ ofsw) sz w = ok m' ->
    valid_stk_arr (evm s1) (emem s2) pstk ofsa n xan ->
    valid_stk_arr (evm s1).[xw <- ok (pword_of_word w)] m' pstk ofsa n xan.
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
    rewrite wsize8.
    have : wunsigned (pstk + wrepr _ (off + ofsa)) = wunsigned pstk + off + ofsa.
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
    move: x Hget'=> [[| |n| sz'] vn] //= Hget' H.
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
    move=> [] H1 H2 H3 H4 H5 Hpstk Hframes Hm' vi Hget.
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
    + by have [_ <-] := Memory.write_mem_stable Hm'.
    exact: (valid_stk_var_stk Hget Hm').
  Qed.

  Lemma valid_map_arr_addr n xn off ofsx :
    Mvar.get m.1 {| vtype := sarr n; vname := xn |} = Some ofsx ->
    0 <= off < Z.pos n ->
    wunsigned (pstk + wrepr U64 (off + ofsx)) =
    wunsigned pstk + off + ofsx.
  Proof.
    move=> hget hoff;have [sx /= [[?] [??? _]]] := validm hget;subst sx.
    rewrite wunsigned_add;first by ring.
    case: pstk_add => ? _; have ? := wunsigned_range pstk; nia.
  Qed.

  Lemma valid_map_word_addr sz xn ofsx:
    Mvar.get m.1 {| vtype := sword sz; vname := xn |} = Some ofsx ->
    wunsigned (pstk + wrepr U64 ofsx) = wunsigned pstk + ofsx.
  Proof.
    move=> hget; have [sx /= [[?] [??? _]]] := validm hget;subst sx.
    apply wunsigned_add; case: pstk_add => ? _; have ? := wsize_size_pos sz.
    have ? := wunsigned_range pstk;nia.
  Qed.

  Lemma valid_stk_arr_arr_stk s1 s2 n n' sz xn xn' ofsx ofsx' m' v0 i (a: WArray.array n) t:
    let x := {| vtype := sarr n; vname := xn |} in
    Mvar.get m.1 x = Some ofsx ->
    let x' := {| vtype := sarr n'; vname := xn' |} in
    Mvar.get m.1 x' = Some ofsx' ->
    get_var (evm s1) x = ok (Varr a) ->
    valid_pointer (emem s2) (pstk + wrepr _ (i * wsize_size sz + ofsx)) sz ->
    write_mem (emem s2) (pstk + wrepr _ (i * wsize_size sz + ofsx)) sz v0 = ok m' ->
    WArray.set a i v0 = ok t ->
    valid_stk_arr (evm s1) (emem s2) pstk ofsx' n' xn' ->
    valid_stk_arr (evm s1).[x <- ok t] m' pstk ofsx' n' xn'.
  Proof.
    move=> x Hget x' Hget' Ha Hvmem Hm' Ht.
    move=> H off Hoff.
    move: H=> /(_ off Hoff) [H /= H']; split.
    - by rewrite (Memory.write_valid _ _ Hm').
    case: (x =P x').
    + subst x x'. case => ???; subst n' xn'.
      rewrite Fv.setP_eq => -[<-] v1 Hv1.
      rewrite Hget in Hget'; move: Hget'=> []?; subst ofsx'.
      have -> := Memory.write_read8 (pstk + wrepr U64 (off + ofsx)) Hm'.
      have /= := WArray.set_get8 off Ht; rewrite Hv1.
      rewrite (valid_map_arr_addr Hget Hoff).
      have /(valid_map_arr_addr Hget) -> : 0 <= i * wsize_size sz < Z.pos n.
      + have ? := WArray.set_bound Ht; have ? := wsize_size_pos sz; nia.
      have -> : wunsigned pstk + off + ofsx - (wunsigned pstk + i * wsize_size sz + ofsx) =
                off - i * wsize_size sz by ring.
      case: ifPn => // ? h; apply: (H' a) => //.
      by move: Ha; apply: on_vuP => //= ? -> /Varr_inj1 ->.
    move => Hxx' a'.
    rewrite Fv.setP_neq; last by apply/eqP.
    move => /H'{H'}H' v /H'{H'}.
    rewrite (Memory.writeP_neq Hm') //.
    split; eauto.
    rewrite (valid_map_arr_addr Hget' Hoff).
    have /(valid_map_arr_addr Hget) -> : 0 <= i * wsize_size sz < Z.pos n.
    + have ? := WArray.set_bound Ht; have ? := wsize_size_pos sz; nia.
    rewrite wsize8.
    have [sx [/= [?] [??? H1]]]:= validm Hget;subst sx.
    have hxx' : x != x' by apply /eqP.
    have := H1 _ _ _ hxx' Hget' erefl.
    have ? := wsize_size_pos sz; have ? := WArray.set_bound Ht; nia.
  Qed.

  Lemma valid_stk_word_arr_stk n xan sz xwn sz' ofsa ofsw (a: WArray.array n) m' s1 s2 t v0 i:
    let xa := {| vtype := sarr n; vname := xan |} in
    Mvar.get m.1 xa = Some ofsa ->
    let xw := {| vtype := sword sz'; vname := xwn |} in
    Mvar.get m.1 xw = Some ofsw ->
    get_var (evm s1) xa = ok (Varr a) ->
    valid_pointer (emem s2) (pstk + wrepr _ (i * wsize_size sz + ofsa)) sz ->
    write_mem (emem s2) (pstk + wrepr _ (i * wsize_size sz + ofsa)) sz v0 = ok m' ->
    WArray.set a i v0 = ok t ->
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
    have Hi:= WArray.set_bound Ht; have ? := wsize_size_pos sz.
    rewrite (valid_map_arr_addr Hgeta) ?(valid_map_word_addr Hgetw); last by nia.
    have [sx [/= [?] [??? H1]]]:= validm Hgeta;subst sx.
    have hxx' : xa != xw by done.
    have := H1 _ _ _ hxx' Hgetw erefl; nia.
  Qed.

  Lemma valid_stk_arr_stk s1 s2 sz vn n m' v0 i ofs (a: WArray.array n) t:
    let vi := {| vtype := sarr n; vname := vn |} in
    Mvar.get m.1 vi = Some ofs ->
    get_var (evm s1) vi = ok (Varr a) ->
    valid_pointer (emem s2) (pstk + wrepr _ (i * wsize_size sz + ofs)) sz ->
    write_mem (emem s2) (pstk + wrepr _ (i * wsize_size sz + ofs)) sz v0 = ok m' ->
    WArray.set a i v0 = ok t ->
    valid_stk (evm s1) (emem s2) pstk ->
    valid_stk (evm s1).[vi <- ok t] m' pstk.
  Proof.
    move=> vi Hget Ha Hvmem Hm' Ht H x; have := H x.
    case Heq: Mvar.get => [ ptr | // ].
    case: x Heq => -[] // => [ n' | sz' ] xn Heq /=.
    + exact: (valid_stk_arr_arr_stk Hget Heq Ha Hvmem Hm' Ht).
    exact: (valid_stk_word_arr_stk Hget Heq Ha Hvmem Hm' Ht).
  Qed.

  Lemma valid_arr_stk sz n vn v0 i ofs s1 s2 m' (a: WArray.array n) t:
    let vi := {| vtype := sarr n; vname := vn |} in
    Mvar.get m.1 vi = Some ofs ->
    get_var (evm s1) vi = ok (Varr a) ->
    write_mem (emem s2) (pstk + wrepr _ (i * wsize_size sz + ofs)) sz v0 = ok m' ->
    WArray.set a i v0 = ok t ->
    valid s1 s2 ->
    valid {| emem := emem s1; evm := (evm s1).[vi <- ok t] |}
          {| emem := m'; evm := evm s2 |}.
  Proof.
    move => vi Hget Ha Hm' Ht.
    have Hvmem : valid_pointer (emem s2) (pstk + wrepr _ (i * wsize_size sz + ofs)) sz.
    + by apply/Memory.writeV; eauto.
    case => H1 H2 H3 H4 H5 Hpstk H6.
    split => //=.
    + move=> w sz' Hvmem'.
      rewrite (H2 _ _ Hvmem') //.
      symmetry; apply: (Memory.writeP_neq Hm').
      split; eauto.
      have Hi:= WArray.set_bound Ht; have ? := wsize_size_pos sz.
      rewrite (valid_map_arr_addr Hget) //; last nia.
      have [sx [/= [?] [??? ?]]]:= validm Hget.
      have /negP /nandP [ /ZltP| /ZltP ] := H1 _ _ Hvmem';nia.
    + move=> w' sz'.
      by rewrite (Memory.write_valid _ _ Hm') H3.
    + move=> x Hx1 Hx2.
      rewrite Fv.setP_neq.
      apply: H4=> //.
      apply/negP=> /eqP Habs.
      by rewrite -Habs /is_in_stk Hget in Hx1.
    + by have [_ <-] := Memory.write_mem_stable Hm'.
    exact: (valid_stk_arr_stk Hget Ha Hvmem Hm' Ht).
  Qed.

  Lemma get_var_arr n (a: WArray.array n) vm vi:
    get_var vm vi = ok (Varr a) ->
    exists vn, vi = {| vtype := sarr n; vname := vn |}.
  Proof.
    move: vi=> [vt vn] //=.
    apply: on_vuP=> //= x Hx; rewrite /to_val.
    move: vt x Hx=> [] // n' /= x Hx /Varr_inj [?];subst n' => /=.
    by exists vn.
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
    move: x Hget=> [[| | n | sz'] vn] Hget //= H.
    + move=> off' Hoff'.
      move: H=> /(_ off' Hoff') [H H']; split.
      + by rewrite (Memory.write_valid _ _ Hm'2).
      move => t a Ht v0 Hv0.
      rewrite -(H' a Ht v0 Hv0).
      apply: (Memory.writeP_neq Hm'2).
      split; eauto.
      have hsz := wsize_size_pos sz.
      have [_ [[/= <-] [ hoffsx hsx _ _]]] := validm Hget.
      rewrite wunsigned_pstk_add; [ | nia | nia ].
      case: Hbound => _ _ []; rewrite wsize8; nia.
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
    move=> Hm' Hm'2 [H1 H2 H3 H4 H5 Hpstk H6].
    split=> //=.
    + move=> sz' w Hw.
      rewrite (Memory.write_valid _ _ Hm') in Hw.
      exact: H1.
    + move=> w sz'.
      rewrite (Memory.write_valid _ _ Hm') => Hw.
      exact: Memory.read_write_any_mem Hw (H2 _ _ Hw) Hm' Hm'2.
    + by move=> w sz'; rewrite (Memory.write_valid w sz' Hm') (Memory.write_valid w sz' Hm'2).
    + by have [_ <-] := Memory.write_mem_stable Hm'2.
    apply: (valid_stk_mem Hm') (Hm'2) (H6).
    have Hvalid1: valid_pointer (emem s1) (ptr + off) sz.
    + apply/Memory.writeV; exists m'; exact: Hm'.
    split; eauto.
    + by case: pstk_add => /ZleP.
    case/negP/nandP: (H1 _ _ Hvalid1) => /ZltP; lia.
  Qed.

  Lemma check_memW sz (vi : var_i) (s1 s2: estate) v v' e e':
    check_var m vi -> alloc_e m e = ok e' -> valid s1 s2 ->
    value_uincl v v' ->
    forall s1', write_lval gd (Lmem sz vi e) v s1 = ok s1'->
    exists s2', write_lval gd (Lmem sz vi e') v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move => Hvar He Hv Hu s1'.
    case: (Hv) => H1 H2 H3 H4 H5 Hpstk H6.
    rewrite /write_lval; t_xrbindP => ptr wi hwi hwiptr ofs we he heofs w hvw.
    move => m' Hm' <- {s1'}.
    have [wi' [-> hwi']] := check_varP Hvar H4 hwi.
    rewrite /= (value_uincl_word hwi' hwiptr) /=.
    have [we' [-> hwe' /=]] := alloc_eP He Hv he.
    rewrite /= (value_uincl_word hwe' heofs) /= (value_uincl_word Hu hvw) /=.
    have : exists m2', write_mem (emem s2) (ptr + ofs) sz w = ok m2'.
    + by apply: Memory.writeV; rewrite H3; apply /orP; left; apply/Memory.writeV; eauto.
    case => m2' Hm2'; rewrite Hm2' /=; eexists; split; first by reflexivity.
    exact: (valid_mem Hm').
  Qed.

  Lemma check_arrW (vi: var_i) ws (s1 s2: estate) v v' e e':
    check_var m vi -> alloc_e m e = ok e' -> valid s1 s2 -> value_uincl v v' ->
    forall s1', write_lval gd (Laset ws vi e) v s1 = ok s1'->
    exists s2', write_lval gd (Laset ws vi e') v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    case: vi => vi ivi.
    move=> Hvar He Hv Hu s1'.
    have Hv' := Hv.
    move: Hv'=> [] H1 H2 H3 H4 H5 Hpstk H6.
    apply: rbindP=> [[]] // n a Ha.
    t_xrbindP => i vali Hvali Hi v0 Hv0 t Ht vm.
    rewrite /set_var;apply: set_varP => //=;last first.
    + by move=> /is_sboolP h1 h2;elimtype False; move: h2;rewrite h1.
    move=> varr Hvarr <- <- /=.
    have Hv'0 := value_uincl_word Hu Hv0.
    have [w [-> U]] := alloc_eP He Hv Hvali.
    have [??]:= value_uincl_int U Hi; subst vali w => /=.
    rewrite /= /on_arr_var.
    have [w [->]]:= check_varP Hvar H4 Ha.
    case: w => //= n0 a0 huincl.
    have Hvar' := Hvar; move: Hvar'=> /andP [ Hnotinstk notstk].
    rewrite Hv'0 /=.
    have Ha0' : @val_uincl (sarr n) (sarr n0) a a0 := huincl.
    have [t' -> Htt' /=]:= Array_set_uincl Ha0' Ht.
    rewrite /set_var /=.
    have Utt': value_uincl (@Varr n t) (Varr t') := Htt'.
    have [varr' [-> Uarr] /=]:= pof_val_uincl Utt' Hvarr.
    exists {| emem := emem s2; evm := (evm s2).[vi <- ok varr'] |}; split=> //.
    split=> //=.
    + exact: eq_vm_write.
    + rewrite /get_var Fv.setP_neq //.
    exact: valid_stk_write_notinstk.
  Qed.

  Lemma alloc_lvalP (r1 r2: lval) v v' ty (s1 s2: estate) :
    alloc_lval m r1 ty = ok r2 -> valid s1 s2 ->
    type_of_val v = ty -> value_uincl v v' ->
    forall s1', write_lval gd r1 v s1 = ok s1' ->
    exists s2', write_lval gd r2 v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Hr Hv Htr Hu; move: Hr.
    case: r1=> [vi t |vi|sz vi e|sz vi e] /=.
    + move=> [] ?;subst r2 => s1' H.
      have [-> _ /=]:= write_noneP H.
      by rewrite (uincl_write_none _ Hu H); exists s2.

    + case: vi => -[] xt xn ii /=.
      case Hget: (Mvar.get _ _) => [ ofs | ] //;last first.
      + case : ifPn => // hvs [?]; subst r2 => /= s1'.
        by apply: check_varW => //=;rewrite /check_var /= hvs /is_in_stk Hget.
      case hw: is_word_type => [ sz | //].
      have := is_word_typeP hw => ? {hw};subst xt.
      case: ifP => // /eqP hty [?];subst ty r2 => /=.
      case: (Hv) => H1 H2 H3 H4 H5 Hpstk H6 s1'.
      rewrite H5 /=; apply: rbindP=> /= vm'; apply: set_varP => //= w1 h ?[?]; subst vm' s1'.
      have [{h} w' [??] ]:= type_of_val_to_pword hty h; subst v w1.
      have /= /(_ sz w') := value_uincl_word Hu .
      rewrite truncate_word_u => -> //=.
      rewrite /zero_extend !wrepr_unsigned.
      have Hvmem: valid_pointer (emem s2) (pstk + wrepr _ ofs) sz.
      + rewrite H3; apply/orP; right; exact: valid_get_w Hget.
      have [m' Hm'] : exists m', write_mem (emem s2) (pstk + wrepr _ ofs) sz w' = ok m'.
      + by apply/Memory.writeV.
      exists {| emem := m'; evm := evm s2 |}; split.
      + by rewrite Hm' /=.
      exact: valid_var_stk Hv Hm' Hget.

    + case: ifP => // hc; apply: rbindP => e' ha [<-].
      by apply: (check_memW hc ha Hv Hu).

    t_xrbindP => e' ha; case Hget: Mvar.get => [ ofs | // ]; last first.
    + case: ifPn => // hnis [<-].
      by apply: (check_arrW _ ha Hv Hu); rewrite /check_var hnis /is_in_stk Hget.
    case: ifP => // hal [<-].
    case: vi Hget => [[vty vn] vi] /= Hget.
    case: (Hv) => H1 H2 H3 H4 H5 Hpstk H6 s1'.
    apply on_arr_varP => n' t' /subtypeEl [n1] /= [??];subst vty => hget.
    have ? : n1 = n'; last subst n1.
    + by move: hget; apply on_vuP => //= ? _ /Varr_inj [].
    t_xrbindP => i ve he hi vw hvw t'' haset vm hset ?;subst s1'.
    have [ve' [hve' vu]]:= alloc_eP ha Hv he.
    have [??] := value_uincl_int vu hi;subst ve ve'.
    have -> := mk_ofsP sz ofs hve'.
    rewrite H5 (value_uincl_word Hu hvw) /= !zero_extend_u.
    apply: set_varP hset => //= t1 []??; subst t1 vm.
    cut (exists m',
      write_mem (emem s2) (pstk + wrepr Uptr (i * wsize_size sz + ofs)) sz vw = ok m').
    - case => m' Hm'; rewrite Hm' /=; eexists; split;first by reflexivity.
      rewrite /WArray.inject Z.ltb_irrefl.
      by have := valid_arr_stk Hget hget Hm' haset Hv; case: (t'').
    apply/Memory.writeV.
    case: (validm Hget) => sx [[<-]] {sx} [hofs hofs' hal' hdisj] {hi}.
    have hi:= WArray.set_bound haset.
    rewrite H3; apply/orP; right.
    have ? := wsize_size_pos sz; have [sx [/= [<-] [hle0 Hle _ _ ]]]:= validm Hget.
    have ? := wunsigned_range pstk; have [? hpstk] := pstk_add.
    rewrite /between wunsigned_add; last by nia.
    apply/andP; split; first by apply /andP; split; apply /ZleP;nia.
    have ->: (pstk + wrepr U64 (i * wsize_size sz + ofs))%R =
           (wrepr U64 (wsize_size sz * i) + (pstk + wrepr U64 ofs))%R.
    + by rewrite !wrepr_add Z.mul_comm; ssrring.ssring.
    by apply: is_align_array; rewrite hpstk.
  Qed.

  Lemma alloc_lvalsP (r1 r2: lvals) vs vs' ty (s1 s2: estate) :
    mapM2 bad_lval_number (alloc_lval m) r1 ty = ok r2 -> valid s1 s2 ->
    seq.map type_of_val vs = ty ->
    List.Forall2 value_uincl vs vs' ->
    forall s1', write_lvals gd s1 r1 vs = ok s1' ->
    exists s2', write_lvals gd s2 r2 vs' = ok s2' /\ valid s1' s2'.
  Proof.
    elim: r1 r2 ty vs vs' s1 s2=> //= [|a l IH] r2 [ | ty tys] // [ | v vs] //.
    + move=> vs' ? s2 [<-] Hvalid _ /List_Forall2_inv_l -> {vs'} s1' [] <-.
      by exists s2; split.
    move=> ? s1 s2; t_xrbindP => a' ha l' /IH hrec <-.
    move=> Hvalid [] hty htys /List_Forall2_inv_l [v'] [vs'] [->] [hv hvs] s1' s1'' ha1 hl1.
    have [s2' [hs2' vs2']]:= alloc_lvalP ha Hvalid hty hv ha1.
    have [s2'' [hs2'' vs2'']]:= hrec _ _ _ _ vs2' htys hvs _ hl1.
    by exists s2''; split => //=; rewrite hs2'.
  Qed.

  Let Pi_r s1 (i1:instr_r) s2 :=
    forall ii1 ii2 i2, alloc_i m (MkI ii1 i1) = ok (MkI ii2 i2) ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem_i SP gd s1' i2 s2' /\ valid s2 s2'.

  Let Pi s1 (i1:instr) s2 :=
    forall i2, alloc_i m i1 = ok i2 ->
    forall s1', valid s1 s1' ->
    exists s2', S.sem_I SP gd s1' i2 s2' /\ valid s2 s2'.

  Let Pc s1 (c1:cmd) s2 :=
    forall c2,  mapM (alloc_i m) c1 = ok c2 ->
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
    move=> s1 s2 s3 i c _ Hi _ Hc c1 /=;t_xrbindP => i' hi c' hc <- s1' hv.
    have [s2' [si hv2]]:= Hi _ hi _ hv.
    have [s3' [sc hv3]]:= Hc _ hc _ hv2.
    exists s3'; split => //.
    apply: S.Eseq; [exact: si|exact: sc].
  Qed.

  Local Lemma HmkI : sem_Ind_mkI P Pi_r Pi.
  Proof.
    move=> ii i s1 s2 _ Hi [ii' ir'] ha s1' hv.
    by have [s2' [Hs2'1 Hs2'2]] := Hi _ _ _ ha _ hv; exists s2'; split.
  Qed.

  Local Lemma Hassgn : sem_Ind_assgn P Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' hv htr Hw ii1 ii2 i2 /=.
    t_xrbindP => i' x'; apply: add_iinfoP => ha e'.
    apply: add_iinfoP => he ??? s1' hs1; subst i' i2 ii1.
    have [v1 [He' Uvv1]] := alloc_eP he hs1 hv.
    have [v1' htr' Uvv1']:= truncate_value_uincl Uvv1 htr.
    have hty := truncate_val_has_type htr.
    have [s2' [Hw' Hs2']] := alloc_lvalP ha hs1 hty Uvv1' Hw.
    by exists s2'; split=> //;apply: S.Eassgn;eauto.
  Qed.

  Local Lemma Hopn : sem_Ind_opn P Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    rewrite /sem_sopn;t_xrbindP => vs va He Hop Hw ii1 ii2 i2 /=.
    t_xrbindP => i' x'; apply: add_iinfoP => ha e'.
    apply: add_iinfoP => he ??? s1' hs1; subst i' i2 ii1.
    have [va' [He' Uvv']] := (alloc_esP he hs1 He).
    have [w' [Hop' Uww']]:= vuincl_exec_opn Uvv' Hop.
    have [s2' [Hw' Hvalid']] := alloc_lvalsP ha hs1 (sopn_toutP Hop) Uww' Hw.
    exists s2'; split=> //.
    by apply: S.Eopn;rewrite /sem_sopn He' /= Hop'.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true P Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc ii1 ii2 i2 /=.
    t_xrbindP => i' e'; apply: add_iinfoP => he c1' hc1 c2' hc2 ??? s1' hs1.
    subst i' i2 ii2; have [b [he']]:= alloc_eP he hs1 Hse.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s2' [Hsem Hvalid']] := Hc _ hc1 _ hs1.
    by exists s2'; split=> //; apply: S.Eif_true.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false P Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc ii1 ii2 i2 /=.
    t_xrbindP => i' e'; apply: add_iinfoP => he c1' hc1 c2' hc2 ??? s1' hs1.
    subst i' i2 ii2; have [b [he']]:= alloc_eP he hs1 Hse.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s2' [Hsem Hvalid']] := Hc _ hc2 _ hs1.
    by exists s2'; split=> //; apply: S.Eif_false.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true P Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c1 e c2 _ Hc1 Hv ? Hc2 ? Hwhile ii1 ii2 i2 /=.
    t_xrbindP => i' e'; apply: add_iinfoP => he c1' hc1 c2' hc2 ??? s1' hs1.
    subst i' i2 ii2.
    have [s2' [Hsem' Hvalid']]:= Hc1 _ hc1 _ hs1.
    have [s2'' [Hsem'' Hvalid'']] := Hc2 _ hc2 _ Hvalid'.
    have := Hwhile _.
    have [|s3' [Hsem''' Hvalid''']] := (Hwhile ii1 ii1 (Cwhile a c1' e' c2') _ _ Hvalid'').
    + by rewrite /= he hc1 hc2.
    exists s3'; split=> //.
    apply: S.Ewhile_true; eauto.
    have [v' [-> ]]:= alloc_eP he Hvalid' Hv.
    by move=> /value_uincl_bool /= -/(_ _ erefl) [_ ->].
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false P Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' _ Hc Hv ii1 ii2 i2 /=.
    t_xrbindP => i' e'; apply: add_iinfoP => he c1' hc1 c2' hc2 ??? s1' hs1.
    subst i' i2 ii2.
    have [s2' [Hsem' Hvalid']]:= Hc _ hc1 _ hs1.
    exists s2'; split=> //.
    apply: S.Ewhile_false; eauto.
    have [v' [-> ]]:= alloc_eP he Hvalid' Hv.
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
  rewrite /g;case:ifP => //= /Z.leb_le Hp Hq Hr [<-].
  split=>// x px Hx.
  case :(Hv x px Hx) => //= sx [] Hsx [] H1 H2 H3.
  by exists sx;split=>//;split=>//;omega.
Qed.

Lemma getfun_alloc oracle (P:prog) (SP:sprog) fn fd:
  alloc_prog oracle P = ok SP ->
  get_fundef (p_funcs P) fn = Some fd ->
  exists fd',
     get_fundef SP fn = Some fd' /\
     alloc_fd oracle (fn,fd) = ok (fn,fd').
Proof.
  rewrite /alloc_prog; elim: (p_funcs P) SP => [ | [fn1 fd1] fs hrec] //= SP.
  apply: rbindP => -[fn2 fd2].
  apply: rbindP => sfd hfd [??]; subst fn2 fd2.
  t_xrbindP => fs' /hrec{hrec} hrec <- /=; case: ifPn => [/eqP ? [?]| hne {hfd} //].
  by subst fn1 fd1; exists sfd; rewrite hfd.
Qed.

Lemma oheadE T m (t x: T) :
  ohead m = Some t ->
  head x m = t.
Proof. case: m => //= ? ?; apply: Some_inj. Qed.

Lemma alloc_fdP oracle (P: prog) (SP: sprog) fn fd fd':
  alloc_prog oracle P = ok SP ->
  get_fundef (p_funcs P) fn = Some fd ->
  get_fundef SP fn = Some fd' ->
  forall m1 va m1' vr,
    sem_call P m1 fn va m1' vr ->
    (exists p, alloc_stack m1 (sf_stk_sz fd') = ok p) ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      eq_mem m1' m2' /\
      S.sem_call SP (p_globs P) m1 fn va m2' vr'.
Proof.
  move=> hap get Sget.
  have [sfd1 [] /=]:= getfun_alloc hap get.
  rewrite Sget => -[?]; subst sfd1.
  case: (oracle (fn, fd)) => [[[stk_s stk_i] l] extra].
  case hinit : init_map => [m |] //=; t_xrbindP => sfd c.
  apply: add_finfoP => Hi; case:andP => // -[Hp Hr] [?] ?.
  subst sfd fd' => /=.
  move=> m1 va m1' vr /sem_callE [f] [].
  rewrite get => - [<-] {f} [vargs] [s1] [vm2] [vres] [hvargs hs1 hbody hvres hvr] [m2 Halloc].
  have [/= Hv Hestk] := init_mapP Halloc hinit.
  have Hstk: stk_ok (top_stack m2) stk_s.
  + by move: Halloc=> /Memory.alloc_stackP [].
  have Hval'': valid m stk_s (top_stack m2)
          {| emem := m1; evm := vmap0 |}
           {| emem := m2; evm := vmap0.[{| vtype := sword Uptr; vname := stk_i |} <- ok (pword_of_word (top_stack m2))] |}.
    move: Halloc=> /Memory.alloc_stackP [] Ha1 Ha2 Ha3 Ha4 Ha5 Ha7.
    split=> //=.
    + move => w sz hv; apply/negP/nandP.
      case: (Ha5 _ _ hv) => h; [ left | right ]; apply/ZltP; lia.
    + move=> x.
      case Heq: (x == {| vtype := sword Uptr; vname := stk_i |}).
      + move: Heq=> /eqP -> /=.
        rewrite /is_vstk /vstk.
        by rewrite Hestk eq_refl.
      + rewrite Fv.setP_neq=> //.
        apply/eqP=> Habs.
        by rewrite Habs eq_refl in Heq.
      + by rewrite /vstk Hestk /= /get_var Fv.setP_eq.
      + by rewrite Ha7.
      move=> x.
      case Hget: (Mvar.get m.1 x)=> [a|//].
      case Htype: (vtype x)=> [| |n| sz] //.
      + move=> off Hoff; split.
        + rewrite Ha3; apply/orP; right.
          case: (Hv _ _ Hget) => q []; rewrite Htype /= => - [] ?;
            subst q => - [] hal hah haa _.
          apply/andP; split.
          * rewrite  /between wsize8 (wunsigned_pstk_add Hstk); [ | nia | nia ].
            apply/andP; split; apply/ZleP; nia.
          apply is_align8.
        by rewrite /vmap0 Fv.get0 => t [<-] {t} ?; rewrite WArray.get0.
      case: x Htype Hget => - [] // sz' x [] -> {sz'} Hget.
      split.
      + rewrite Ha3; apply/orP; right.
        exact: (valid_get_w Hstk Hv Hget).
      by move=> v;rewrite /vmap0 Fv.get0.
  have := check_varsW Hp Hval'' _ hs1.
  move=> /(_ vargs) [ |s2 [Hs2 Hv2]];first by apply List_Forall2_refl.
  have [[m2' vm2'] [Hs2' Hv2']] := check_cP SP Hstk Hv hbody Hi Hv2.
  case: Hv2' => /= Hdisj Hmem Hval Heqvm _ Htopstack _.
  have [vr' [/= hvr' hvruincl]] := check_varsP Hr Heqvm hvres.
  have [vr'' hvr'' hvruincl'] := mapM2_truncate_val hvr hvruincl.
  exists (free_stack m2' stk_s), vr''; split; first exact: hvruincl'.
  split.
  + move => w sz.
    have hts : omap snd (ohead (frames m2')) = Some stk_s.
    + by rewrite Htopstack.
    have [ hrd hvld hcllstk ] := Memory.free_stackP hts.
    move: (Hdisj w sz) (Hmem w sz) (Hval w sz)=> {Hdisj Hmem Hval} Hdisjw Hmemw Hvalw.
    case Heq1: (read_mem m1' w sz) => [w'| err].
    + have Hw : valid_pointer m1' w sz by apply /Memory.readV;exists w'.
      rewrite -Heq1 -hrd; first exact: Hmemw.
      rewrite hvld Hvalw.
      split; first by rewrite Hw.
      rewrite /top_stack (oheadE _ Htopstack).
      have [noo _ _] := Memory.alloc_stackP Halloc.
      constructor; eauto.
      + by apply/ZleP.
      case/negP/nandP: (Hdisjw Hw) => /=/ZltP; lia.
    have ? := Memory.read_mem_error Heq1. subst err.
    case Heq2: (read_mem _ _ _) => [w'|];last by rewrite (Memory.read_mem_error Heq2).
    case/read_mem_valid_pointer/hvld: Heq2 => k [_ _ k'].
    move: Hvalw; set b := between _ _ _ _.
    replace b with false.
    + by rewrite k orbF => /esym /Memory.readV [] ?; rewrite Heq1.
    move: k'. rewrite /top_stack (oheadE _ Htopstack) /= => k'.
    symmetry.
    have Hsz := wsize_size_pos sz.
    apply/nandP; case: k' => k'; [ right | left ]; apply/ZleP; lia.
  apply: S.EcallRun.
  + exact: Sget.
  + exact: Halloc.
  + exact: erefl.
  + exact: hvargs.
  + move: Hs2; rewrite /pword_of_word (Eqdep_dec.UIP_dec Bool.bool_dec (cmp_le_refl U64)); exact: id.
  + exact: Hs2'.
  + exact: hvr'.
  + exact: hvr''.
  reflexivity.
Qed.

Definition alloc_ok SP fn m1 :=
  forall fd, get_fundef SP fn = Some fd ->
  exists p, alloc_stack m1 (sf_stk_sz fd) = ok p.

Lemma alloc_progP oracle (P: prog) (SP: sprog) fn:
  alloc_prog oracle P = ok SP ->
  forall m1 va m1' vr,
    sem_call P m1 fn va m1' vr ->
    alloc_ok SP fn m1 ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      eq_mem m1' m2' /\
      S.sem_call SP (p_globs P) m1 fn va m2' vr'.
Proof.
  move=> Hcheck m1 va m1' vr hsem ha.
  have [fd hget]: exists fd, get_fundef (p_funcs P) fn = Some fd.
  + by case: hsem => ??? fd *;exists fd.
  have [sfd [hgetS _]]:= getfun_alloc Hcheck hget.
  by apply : (alloc_fdP Hcheck hget hgetS hsem (ha _ hgetS)).
Qed.
