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

(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import sem compiler_util constant_prop_proof.
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
Proof. case: t=> //= [p [] <-|[] <-] //=; zify; omega. Qed.

Definition stk_ok (w:word) (z:Z) := w + z < I64.modulus.

Definition valid_map (m:map) (stk_size:Z) := 
  forall x px, Mvar.get m.1 x = Some px -> 
     exists sx, size_of (vtype x) = ok sx /\
     [/\ 0 <= px, px + sx <= stk_size &
         forall y py sy, x != y ->  
           Mvar.get m.1 y = Some py -> size_of (vtype y) = ok sy ->
           px + sx <= py \/ py + sy <= px].

Section PROOF.
  Variable P: prog.
  Context (gd: glob_defs).
  Variable SP: sprog.

  Variable m:map.
  Variable stk_size : Z.
  Variable pstk : word.

  Hypothesis pstk_add : stk_ok pstk stk_size.

  Hypothesis validm : valid_map m stk_size.

  Import Memory.

  Definition valid_stk_word (vm1:vmap) (m2:mem) pstk p vn :=
    valid_addr m2 (I64.repr (pstk + p)) /\
    forall v,
      vm1.[{|vtype:=sword;vname := vn|}] = ok v ->
      read_mem m2 (I64.repr (pstk + p)) = ok v.

  Definition valid_stk_arr (vm1:vmap) (m2:mem) pstk p s vn :=
    forall off, (0 <= off < Zpos s)%Z ->
      valid_addr m2 (I64.repr (pstk + (8 * off + p))) /\
      let t := vm1.[{|vtype := sarr s;vname := vn|}] in
      forall a, t = ok a ->
        forall v, FArray.get a off = ok v ->
          read_mem m2 (I64.repr (pstk + (8 * off + p))) = ok v.

  Definition valid_stk (vm1:vmap) (m2:mem) pstk :=
    forall x,
      match Mvar.get m.1 x with
      | Some p =>
        match vtype x with
        | sword => valid_stk_word vm1 m2 pstk p (vname x)
        | sarr s => valid_stk_arr vm1 m2 pstk p s (vname x)
        | _ => True
        end
      | _ => True
      end.

  Definition eq_vm (vm1 vm2:vmap) := 
    (forall (x:var), 
       ~~ is_in_stk m x -> ~~ is_vstk m x -> 
       eval_uincl vm1.[x] vm2.[x]).

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
    forall w, valid_addr m w -> ~(pstk <= w < pstk + stk_size).

  Definition valid (s1 s2:estate) :=
    [/\ disjoint_stk (emem s1), 
        (forall w, valid_addr (emem s1) w -> read_mem (emem s1) w = read_mem (emem s2) w),
        (forall w, valid_addr (emem s2) w = valid_addr (emem s1) w ||  
                                       ((pstk <=? w) && (w <? pstk + stk_size))),
        eq_vm (evm s1) (evm s2) & 
        get_var (evm s2) (vstk m) = ok (Vword pstk) /\
        valid_stk (evm s1) (emem s2) pstk ].

  Lemma get_valid_wrepr x p: 
     Mvar.get m.1 {| vtype := sword; vname := x |} = Some p -> 
     pstk + p = I64.repr (pstk + p).
  Proof.
    move=> Hget; have [sx /= [][]<-[]?? _]:= validm Hget.
    rewrite I64.unsigned_repr //.
    move: pstk_add (I64.unsigned_range pstk);rewrite /stk_ok/I64.max_unsigned.
    move=> ??;omega.
  Qed.

  Lemma get_valid_arepr x n p p1 : 
    Mvar.get m.1 {| vtype := sarr n; vname := x |} = Some p ->
    0 <= p1 < Z.pos n ->
    pstk + (8 * p1 + p) = I64.repr (pstk + (8 * p1 + p)).
  Proof.
    move=> Hget Hp1; have [sx [][]<-[]?? _]:= validm Hget.
    rewrite I64.unsigned_repr //.
    move: pstk_add (I64.unsigned_range pstk);rewrite /stk_ok/I64.max_unsigned.
    move=> ??. lia. 
  Qed.

  Lemma get_valid_repr x sz get:
    size_of (vtype x) = ok sz ->
    Mvar.get m.1 x = Some get ->
    pstk + get = I64.repr (pstk + get).
  Proof.
    move=> Hsz Hget.
    case: x Hget Hsz=> [[]] //.
    + move=> n vn Hget _.
      have ->: get = 8 * 0 + get by [].
      by rewrite {1}(get_valid_arepr Hget).
    + move=> vn Hget _.
      by rewrite {1}(get_valid_wrepr Hget).
  Qed.

  Lemma get_valid_word x p m1 m2: 
     valid m1 m2 -> 
     Mvar.get m.1 {| vtype := sword; vname := x |} = Some p -> 
     valid_addr (emem m2) (I64.repr (pstk + p)).
  Proof.
    move=> [] H0 H1 _ H2 [H3 H4] Hget.
    by have := H4 {| vtype := sword; vname := x |};rewrite Hget /= => -[-> _].
  Qed.

  Lemma get_valid_arr x n p p1 m1 m2: 
     valid m1 m2 -> 
     Mvar.get m.1 {| vtype := sarr n; vname := x |} = Some p -> 
     0 <= p1 < Zpos n ->
     valid_addr (emem m2) (I64.repr (pstk + (8 * p1 + p))).
  Proof.
    move=> [] H0 H1 _ H2 [H3 H4] Hget Hp1.
    by have := H4 {| vtype := sarr n; vname := x |};rewrite Hget /= => /(_ _ Hp1) [].
  Qed.

  Lemma read_write_mem m1 v1 v2 m2 w:
    write_mem m1 v1 v2 = ok m2 ->
    read_mem m2 w = write_mem m1 v1 v2 >>= (fun m2 => read_mem m2 w).
  Proof. by move=> ->. Qed.

  Lemma write_valid m1 m2 v1 v2 w:
    write_mem m1 v1 v2 = ok m2 ->
    valid_addr m1 w = valid_addr m2 w.
  Proof.
    move=> H1.
    have Hr := read_write_mem _ H1.
    have Hv1 : valid_addr m1 v1 by apply /(writeV m1 v1 v2);exists m2.
    case Hw: (valid_addr m1 w);move /readV: (Hw).
    + move=> [w' Hw'];symmetry.
      case (v1 =P w) => [ | /eqP] Heq.
      + by subst;apply /readV;exists v2; rewrite Hr Memory.writeP Hv1 eq_refl.
      by apply /readV;exists w'; rewrite Hr Memory.writeP (negbTE Heq) Hv1.
    move=> Hm1;symmetry;apply /readV => -[w'].
    rewrite Hr Memory.writeP Hv1;case:ifP => /eqP Heq.
    + by subst;move: Hv1;rewrite Hw.
    by move=> ?;apply Hm1;exists w'.
  Qed.

  Lemma read_mem_write_same addr addr' val m1 m2 m1' m2':
    write_mem m1 addr val = ok m1' ->
    write_mem m2 addr val = ok m2' ->
    (forall w, valid_addr m1 w -> read_mem m1 w = read_mem m2 w) ->
    valid_addr m1 addr' ->
    read_mem m1' addr' = read_mem m2' addr'.
  Proof.
    move=> Hw1 Hw2 Hother Hv'.
    have Hv1: valid_addr m1 addr.
      apply/writeV; exists m1'; exact: Hw1.
    have Hv2: valid_addr m2 addr.
      apply/writeV; exists m2'; exact: Hw2.
    rewrite (read_write_mem _ Hw1) (read_write_mem _ Hw2) !writeP Hv1 Hv2 Hother //.
  Qed.

  Lemma add_repr_r x y : I64.add x (I64.repr y) = I64.repr (x + y).
  Proof.
    by apply: reqP; rewrite !urepr !I64.Z_mod_modulus_eq Zplus_mod_idemp_r eq_refl.
  Qed.

  Lemma value_uincl_to_val t (v1 v2 : sem_t t) : 
    val_uincl v1 v2 ->
    value_uincl (to_val v1) (to_val v2).
  Proof. by case: t v1 v2. Qed.

  Lemma check_varP vm1 vm2 x1 x2 v:
    check_var m x1 x2 -> eq_vm vm1 vm2 -> 
    get_var vm1 x1 = ok v ->
    exists v', get_var vm2 x2 = ok v' /\ value_uincl v v'.
  Proof.
    move=> /andP [/andP [Hin_stk /eqP Heq12] Hnot_vstk] Heq Hget.
    have := Heq _ Hin_stk Hnot_vstk.
    move: Hget;rewrite /get_var Heq12; apply: on_vuP => [t | ] -> /=.
    + move=> <-;case vm2.[x2] => //= s Hs;exists (to_val s);split => //.
      by apply value_uincl_to_val.
    move=> [<-] /=;case vm2.[x2] => //= [s _ | ? <-].
    + by exists (to_val s);split => //;rewrite type_of_to_val.
    by exists (Vundef (vtype x2)).
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

  Lemma check_var_stkP s1 s2 x1 x2 e v:
    check_var_stk m x1 x2 e ->
    valid s1 s2 ->
    sem_pexpr gd s1 (Pvar x1) = ok v ->
    exists v', 
       sem_pexpr gd s2 (Pload x2 e) = ok v' /\ value_uincl v v'.
  Proof.
    move=> /andP [/andP [/eqP Hvstk /eqP Htype] Hget] Hvalid /=.
    case Hget: (Mvar.get m.1 x1) Hget=> [ofs|//] /eqP ->.
    rewrite /=.
    move: Hvalid=> -[] _ _ _ _ [Hpstk /(_ x1) H].
    rewrite Hget Htype in H.
    move: H=> [H H'] Hvar.
    rewrite Hvstk Hpstk /=.
    case: x1 Htype Hget Hvar H'=> [[x1t x1n] vi1] /= Htype Hget Hvar H'.
    rewrite Htype in Hget.
    rewrite add_repr_r.
    rewrite /= in H'.
    rewrite /get_var in Hvar.
    move: Hvar;rewrite Htype.
    apply: on_vuP => /= [w | ]. 
    + by move=> /H' -> <-;exists (Vword w).
    by move=> _ [<-];move /readV: H => [w -> /=];exists (Vword w).
  Qed.

  Lemma is_addr_ofsP ofs e1 e2 : 
    is_addr_ofs ofs e1 e2 ->
    exists i, 
    e1 = Pconst i /\ 
    e2 = Pcast (8 * i + ofs).
  Proof.
    rewrite /is_addr_ofs;case:is_constP => // i;case:is_wconstP => // z.
    by move=> /eqP <-;exists i;rewrite Z.add_comm.
  Qed.

  Opaque Z.mul.

  (* FIXME: MOVE THIS *)
  Lemma ZleP x y : reflect (x <= y) (x <=? y).
  Proof. by apply: (equivP idP);rewrite Zle_is_le_bool. Qed.

  Lemma ZltP x y : reflect (x < y) (x <? y).
  Proof. by apply: (equivP idP);rewrite Zlt_is_lt_bool. Qed.

  Lemma check_arr_stkP s1 s2 x1 e1 x2 e2 v:
    check_arr_stk m x1 e1 x2 e2 ->
    valid s1 s2 ->
    sem_pexpr gd s1 (Pget x1 e1) = ok v ->
    sem_pexpr gd s2 (Pload x2 e2) = ok v.
  Proof.
    case: x1 => [[xt1 xn1] ii1]. set x1 := {| v_var := _ |}.
    move=> /andP [/andP [/eqP Hvstk Harrt]].
    case Hget: (Mvar.get m.1 x1)=> [ofs|//] /is_addr_ofsP [i [??]];subst e1 e2.
    move=> [H1 H2 H3 H4 [H5 H6]].
    apply: on_arr_varP=> n t /= Ht Harr /=;subst xt1.
    apply: rbindP => z Hgeti [<-].
    rewrite Hvstk H5 /=.
    have Hbound := Array.getP_inv Hgeti.
    have /andP [/ZleP H0le /ZltP Hlt]:= Hbound. 
    have := H6 x1;rewrite Hget /=.
    move=> /(_ i) [//| /=] ?.
    move: Harr;rewrite /get_var.
    apply: on_vuP => //= t0 Ht0 /Varr_inj [_?];subst t0.
    move=> /(_ _ Ht0) H.
    by move: Hgeti;rewrite /Array.get Hbound add_repr_r => /H ->.
  Qed.

  Lemma check_eP (e1 e2: pexpr) (s1 s2: estate) v :
    check_e m e1 e2 -> valid s1 s2 -> sem_pexpr gd s1 e1 = ok v ->
    exists v', sem_pexpr gd s2 e2 = ok v' /\ value_uincl v v'.
  Proof.
    move=> He Hv; move: He.
    have Hvm: eq_vm (evm s1) (evm s2).
      by move: Hv=> -[].
    elim: e1 e2 v=> 
     [z1|b1|e1 IH|v1| g1 |v1 e1 IH|v1 e1 IH|o1 e1 IH|o1 e1 H1 e1' H1' | e He e1 H1 e1' H1'] e2 v.
    + by case: e2=> //= z2 /eqP -> [] <-;exists z2;auto.
    + by case: e2=> //= b2 /eqP -> [] <-;exists b2;auto.
    + case:e2 => //= e2 /IH{IH}IH.
      apply: rbindP => z;apply: rbindP => v1 /IH [v1' [->]] /= Hu.
      move=> /(value_uincl_int Hu) [??] [?];subst v1 v1' v => /=.
      by exists (Vword (I64.repr z)).
    + case: e2 => //= [v2 | v2 e2].
      + by move=> /check_varP -/(_ _ _ _ Hvm) H/H. 
      move=> /check_var_stkP -/(_ _ _ _ Hv) H /H {H} [v' [Hload /= Hu]].
      by exists v';split.
    + by case: e2=>//= g2 /eqP -> ->; eauto.
    + case: e2=> //= v2 e2.
      + move=> /andP [/check_varP Hv12 /IH{IH} He].
        apply: on_arr_varP=> n t Ht Harr /=.
        rewrite /on_arr_var. 
        have [v' [-> Hu] /=]:= Hv12 _ _ _ Hvm Harr.
        apply: rbindP=> i; apply: rbindP=> ve /He [ve' [-> Hve]].
        move=> /(value_uincl_int Hve) [??];subst ve ve'=> /=.
        apply: rbindP => w Hw [<-].
        by case: v' Hu => //= n' a [<-] /(_ _ _ Hw) -> /=; exists w.
      move=> He Hv1;exists v;split=>//.
      by apply: (check_arr_stkP He Hv Hv1).
    + case: e2=> // v2 e2 /= /andP [Hv12 He12].
      apply: rbindP=> w1; apply: rbindP=> x1 Hx1 Hw1.
      apply: rbindP=> w2; apply: rbindP=> x2 Hx2 Hw2.
      apply: rbindP=> w Hw -[] <-.
      exists (Vword w);split => //.  
      have [x1' [->]]:= check_varP Hv12 Hvm Hx1.
      move=> /value_uincl_word -/(_ _ Hw1) [??];subst x1 x1' => /=.
      have [v' [-> /= Hu]]:= IH _ _ He12 Hx2.
      have [??]:= value_uincl_word Hu Hw2; subst x2 v' => /=.
      have -> // : read_mem (emem s2) (I64.add w1 w2) = ok w.
      rewrite -Hw;case: Hv => _ -> //.
      by apply/readV; exists w; exact: Hw.
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
    t_xrbindP=> v1 /H1 [] v1' [] -> Hv1' v2 /H1' [] v2' [] -> Hv2'.
    t_xrbindP=> y2 Hy2 y3 Hy3 <- /=.
    rewrite -(type_of_val_uincl Hv1').
    have [? [-> _]] /= := of_val_uincl Hv1' Hy2.
    have [? [-> _]] /= := of_val_uincl Hv2' Hy3.
    eexists; split=> //.
    by case: (b).
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
    + move=> [H H'];split=> //= v0; rewrite Fv.setP_neq;last first.
      + by rewrite eq_sym;case: (x) Htype Hx => ?? /= ->.
      by move=> /H'.
  Qed.

  Lemma valid_set_uincl s1 s2 vi v v': 
    vi != vstk m -> ~~ is_in_stk m vi ->
    valid s1 s2 -> eval_uincl v v' ->
    valid {| emem := emem s1; evm := (evm s1).[vi <- v] |}
          {| emem := emem s2; evm := (evm s2).[vi <- v'] |}.
  Proof.
    move=> neq nin [H1 H2 H3 H4 [H5 H6]] Hu;split=> //=.
    + by apply: eq_vm_write.
    split;first by rewrite /get_var Fv.setP_neq ?Hx //.
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
    + move=> /(of_val_uincl Hu) [t' [-> Htt']] <- [<-].
      exists {| emem := emem s2; evm := (evm s2).[vi <- ok t'] |};split=>//.
      by apply valid_set_uincl.
    move=> /of_val_error ?;subst v.
    move: Hu;rewrite /= => /eqP Hu <- [<-].
    have := of_val_type_of v';rewrite -Hu => -[[v'']|] -> /=.
    + exists {| emem := emem s2; evm := (evm s2).[vi <- ok v''] |};split => //.
      by apply valid_set_uincl => //; apply eval_uincl_undef.
    exists {| emem := emem s2; evm := (evm s2).[vi <- undef_addr (vtype vi)] |};split=>//.
    by apply valid_set_uincl.
  Qed.

  Lemma check_varsW (vi vi': seq var_i) (s1 s2: estate) v v':
    all2 (check_var m) vi vi' -> valid s1 s2 -> 
    List.Forall2 value_uincl v v' -> 
    forall s1', write_vars vi v s1 = ok s1' ->
    exists s2', write_vars vi' v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    elim: vi vi' v v' s1 s2 => [|a l IH] [|a' l'] //= [|va vl] [|va' vl'] s1 s2 //=.
    + by move=> _ Hv _ s1' []<-; exists s2.
    + by move=> _ _ H;sinversion H.
    + by move=> _ _ H;sinversion H.
    move=> /andP [Ha Hl] Hv H s1';sinversion H.
    apply: rbindP=> x Hwa.
    move: (check_varW Ha Hv H3 Hwa)=> [s2' [Hs2' Hv2']] Hwl.
    move: (IH _ _ _ _ _ Hl Hv2' H5 _ Hwl)=> [s3' [Hs3' Hv3']].
    by exists s3'; split=> //; rewrite Hs2' /= Hs3'.
  Qed.

  Lemma vtype_diff x x': vtype x != vtype x' -> x != x'.
  Proof. by apply: contra => /eqP ->. Qed.

  Lemma vname_diff x x': vname x != vname x' -> x != x'.
  Proof. by apply: contra => /eqP ->. Qed.

  Lemma var_stk_diff x x' get get' sz:
    Mvar.get m.1 x = Some get ->
    Mvar.get m.1 x' = Some get' ->
    x != x' ->
    size_of (vtype x') = ok sz ->
    get != get'.
  Proof.
    move=> Hget Hget' Hneq Hsz.
    apply/negP=> /eqP Habs.
    rewrite -{}Habs in Hget'.
    move: (validm Hget)=> [sx [Hsx1 [Hsx2 Hsx3 /(_ _ _ _ Hneq Hget' Hsz) [|]]]].
    have := (size_of_pos Hsx1); lia.
    have := (size_of_pos Hsz); lia.
  Qed.

  Lemma var_stk_diff_off x x' get get' off sz:
    Mvar.get m.1 x = Some get ->
    Mvar.get m.1 x' = Some get' ->
    x != x' ->
    size_of (vtype x') = ok sz ->
    0 <= off < sz ->
    get != off + get'.
  Proof.
    move=> Hget Hget' Hneq Hsz Hoff.
    apply/negP=> /eqP Habs.
    rewrite {}Habs in Hget.
    move: (validm Hget)=> [sx [Hsx1 [Hsx2 Hsx3 /(_ _ _ _ Hneq Hget' Hsz) [|]]]].
    have := (size_of_pos Hsx1); lia.
    have := (size_of_pos Hsz); lia.
  Qed.

  Lemma var_stk_diff_off_l x x' get get' off sz:
    Mvar.get m.1 x = Some get ->
    Mvar.get m.1 x' = Some get' ->
    x != x' ->
    size_of (vtype x) = ok sz ->
    0 <= off < sz ->
    get + off != get'.
  Proof.
    move=> Hget Hget' Hneq Hsz Hoff.
    apply/negP=> /eqP Habs.
    rewrite -{}Habs in Hget'.
    rewrite eq_sym in Hneq.
    move: (validm Hget')=> [sx [Hsx1 [Hsx2 Hsx3 /(_ _ _ _ Hneq Hget Hsz) [|]]]].
    have := (size_of_pos Hsx1); lia.
    have := (size_of_pos Hsz); lia.
  Qed.

  Lemma var_stk_diff_off_both x x' get get' off off' sz sz':
    Mvar.get m.1 x = Some get ->
    Mvar.get m.1 x' = Some get' ->
    x != x' ->
    size_of (vtype x) = ok sz ->
    size_of (vtype x') = ok sz' ->
    0 <= off < sz ->
    0 <= off' < sz' ->
    get + off != get' + off'.
  Proof.
    move=> Hget Hget' Hneq Hsz Hsz' Hoff Hoff'.
    apply/negP=> /eqP Habs.
    rewrite eq_sym in Hneq.
    (* TODO: check if optimal *)
    move: (validm Hget')=> [sx [Hsx1 [Hsx2 Hsx3 /(_ _ _ _ Hneq Hget Hsz) [|]]]].
    have := (size_of_pos Hsx1).
    rewrite eq_sym in Hneq.
    move: (validm Hget)=> [sx' [Hsx'1 [Hsx'2 Hsx'3 /(_ _ _ _ Hneq Hget' Hsz') [|]]]].
    have := (size_of_pos Hsx'1); lia.
    lia.
    have := (size_of_pos Hsz); lia.
  Qed.

  Lemma valid_get_w vn get:
    Mvar.get m.1 {| vtype := sword; vname := vn |} = Some get ->
    (pstk <=? I64.add pstk (I64.repr get)) && (I64.add pstk (I64.repr get) <? pstk + stk_size).
  Proof.
    move=> Hget.
    move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' _]]].
    apply/andP; split.
    apply: Zle_imp_le_bool.
    rewrite add_repr_r.
    rewrite -(get_valid_wrepr Hget); lia.
    rewrite add_repr_r.
    apply Zlt_is_lt_bool.
    rewrite -(get_valid_wrepr Hget); lia.
  Qed.

  Lemma valid_get_a vn get n:
    Mvar.get m.1 {| vtype := sarr n; vname := vn |} = Some get ->
    (pstk <=? I64.add pstk (I64.repr get)) && (I64.add pstk (I64.repr get) <? pstk + stk_size).
  Proof.
    move=> Hget.
    move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' _]]].
    have ->: get = 8 * 0 + get by [].
    apply/andP; split.
    apply: Zle_imp_le_bool.
    rewrite add_repr_r.
    rewrite -(get_valid_arepr Hget); lia.
    rewrite add_repr_r.
    apply Zlt_is_lt_bool.
    rewrite -(get_valid_arepr Hget); lia.
  Qed.

  Lemma valid_get_a_off vn get n off:
    Mvar.get m.1 {| vtype := sarr n; vname := vn |} = Some get ->
    0 <= off < Z.pos n ->
    (pstk <=? I64.add pstk (I64.repr (8 * off + get))) && (I64.add pstk (I64.repr (8 * off + get)) <? pstk + stk_size).
  Proof.
    move=> Hget Hoff.
    move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' _]]].
    apply/andP; split.
    apply: Zle_imp_le_bool.
    rewrite add_repr_r.
    rewrite -(get_valid_arepr Hget); lia.
    rewrite add_repr_r.
    apply Zlt_is_lt_bool.
    rewrite -(get_valid_arepr Hget); lia.
  Qed.

  Lemma valid_stk_arr_var_stk s1 s2 xwn xan getw geta n w m':
    let xw := {| vname := xwn; vtype := sword |} in
    Mvar.get m.1 xw = Some getw ->
    let xa := {| vname := xan; vtype := sarr n |} in
    Mvar.get m.1 xa = Some geta ->
    write_mem (emem s2) (I64.add pstk (I64.repr getw)) w = ok m' ->
    valid_addr (emem s2) (I64.add pstk (I64.repr getw)) ->
    valid_stk_arr (evm s1) (emem s2) pstk geta n xan ->
    valid_stk_arr (evm s1).[xw <- ok w] m' pstk geta n xan.
  Proof.
    move=> xw Hgetw xa Hgeta Hm' Hvmem H off Hoff.
    move: H=> /(_ off Hoff) [Hoff1 Hoff2]; split.
    by rewrite -(write_valid _ Hm').
    rewrite Fv.setP_neq=> [t a Ht v0 Hv0|].
    rewrite (read_write_mem _ Hm') writeP Hvmem.
    rewrite (Hoff2 _ Ht _ Hv0).
    case: ifP=> // Heq; exfalso.
    rewrite add_repr_r in Heq.
    have Heq': getw = (8 * off + geta).
      apply (Z.add_cancel_l _ _ pstk).
      rewrite (get_valid_wrepr Hgetw) (get_valid_arepr Hgeta)=> //.
      by apply/eqP.
    have Habs: getw != 8 * off + geta.
      apply: (var_stk_diff_off Hgetw Hgeta)=> //; lia.
    by rewrite Heq' eq_refl in Habs.
    by rewrite vtype_diff.
  Qed.

  Lemma valid_stk_word_var_stk s1 s2 xn xn' getx getx' m' w:
    let x := {| vtype := sword; vname := xn |} in
    Mvar.get m.1 x = Some getx ->
    let x' := {| vtype := sword; vname := xn' |} in
    Mvar.get m.1 x' = Some getx' ->
    write_mem (emem s2) (I64.add pstk (I64.repr getx)) w = ok m' ->
    valid_addr (emem s2) (I64.add pstk (I64.repr getx)) ->
    valid_stk_word (evm s1) (emem s2) pstk getx' xn' ->
    valid_stk_word (evm s1).[x <- ok w] m' pstk getx' xn'.
  Proof.
    move=> vi Hget x Hget' Hm' Hvmem [H H']; split=> //.
    by rewrite -(write_valid _ Hm').
    case Heq: (xn == xn').
    + move: Heq=> /eqP Heq; subst xn' vi x.
      rewrite Fv.setP_eq /= => v0 [] <-.
      rewrite Hget in Hget'; move: Hget'=> []<-.
      by rewrite (read_write_mem _ Hm') writeP Hvmem add_repr_r eq_refl.
    + rewrite Fv.setP_neq; last by rewrite vname_diff //= Heq.
      rewrite /= => v0 Hv0.
      rewrite (read_write_mem _ Hm') writeP Hvmem add_repr_r.
      suff ->: I64.repr (pstk + getx) == I64.repr (pstk + getx') = false.
        by rewrite (H' _ Hv0).
      apply/eqP=> Habs.
      have /eqP Heq'': getx = getx'.
        suff: pstk + getx = pstk + getx' by lia.
          by rewrite (get_valid_wrepr Hget) (get_valid_wrepr Hget') Habs.
      have Habs': getx != getx'.
        apply: (var_stk_diff Hget Hget')=> //.
        by rewrite vname_diff //= Heq.
      by rewrite Heq'' in Habs'.
  Qed.

  Lemma valid_stk_var_stk s1 s2 (w: word) m' xn get ii:
    let vi := {| v_var := {| vtype := sword; vname := xn |}; v_info := ii |} in
    Mvar.get m.1 vi = Some get ->
    write_mem (emem s2) (I64.add pstk (I64.repr get)) w = ok m' ->
    valid_addr (emem s2) (I64.add pstk (I64.repr get)) ->
    valid_stk (evm s1) (emem s2) pstk ->
    valid_stk (evm s1).[{| vtype := sword; vname := xn |} <- ok w] m' pstk.
  Proof.
    move=> vi Hget Hm' Hvmem H x; move: H=> /(_ x).
    case Hget': (Mvar.get m.1 x)=> [getx|//].
    move: x Hget'=> [[| |n| ] vn] //= Hget' H.
    + exact: (valid_stk_arr_var_stk Hget Hget' Hm').
    + exact: (valid_stk_word_var_stk Hget Hget' Hm').
  Qed.

  Lemma valid_var_stk s1 xn w s2 m' get ii:
    valid s1 s2 ->
    write_mem (emem s2) (I64.add pstk (I64.repr get)) w = ok m' ->
    let vi := {| v_var := {| vtype := sword; vname := xn |}; v_info := ii |} in
    Mvar.get m.1 vi = Some get ->
    valid_addr (emem s2) (I64.add pstk (I64.repr get)) ->
    valid {|
      emem := emem s1;
      evm := (evm s1).[{| vtype := sword; vname := xn |} <- ok w] |}
      {| emem := m'; evm := evm s2 |}.
  Proof.
    move=> [] H1 H2 H3 H4 [H5 H6] Hm' vi Hget Hvmem.
    split=> //=.
    + move=> w' Hvalid.
      rewrite (read_write_mem w' Hm') writeP Hvmem (H2 _ Hvalid).
      suff ->: I64.add pstk (I64.repr get) == w' = false=> //.
      rewrite add_repr_r.
      apply/negP=> /eqP Habs.
      have := (get_valid_wrepr Hget).
      rewrite Habs.
      have := (H1 _ Hvalid).
      move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' _]]].
      lia.
    + move=> w'.
      by rewrite -(write_valid _ Hm') H3.
    + move=> x Hx1 Hx2.
      rewrite Fv.setP_neq; first exact: H4.
      apply/negP=> /eqP ?; subst x.
      by rewrite /is_in_stk Hget in Hx1.
    + split=> //.
      exact: (valid_stk_var_stk Hget Hm').
  Qed.

  Lemma check_var_stkW (vi vi': var_i) (s1 s2: estate) v v' e:
     check_var_stk m vi vi' e -> valid s1 s2 -> 
     value_uincl v v' -> 
     forall s1', write_var vi v s1 = ok s1' ->
    exists s2' : estate, write_lval gd (Lmem vi' e) v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    case: vi => [[xt xn] ii];set vi := {| v_var := _ |}.
    move=> /andP [/andP [/eqP Hisvstk /eqP /= Htype] He] Hv Hu;subst xt.
    case Hget: (Mvar.get m.1 vi) He=> [get|//] /eqP -> s1'.
    rewrite Hisvstk;have := Hv=> -[] H1 H2 H3 H4 [H5 H6].
    rewrite H5; apply: rbindP=> /= vm'; apply: set_varP => //= w.
    move=> /(value_uincl_word Hu) [??];subst v v'.
    move=> /= <- [<-].
    have Hvmem: valid_addr (emem s2) (I64.add pstk (I64.repr get)).
      rewrite H3.
      apply/orP; right; apply: (valid_get_w Hget).
    have Hmem: exists m', write_mem (emem s2) (I64.add pstk (I64.repr get)) w = ok m'.
      by apply/writeV.
    move: Hmem=> [m' Hm'].
    exists {| emem := m'; evm := evm s2 |}; split.
    by rewrite Hm' /=.
    exact: (valid_var_stk Hv Hm' Hget Hvmem).
  Qed. 

  Lemma pos_dec_n_n n: CEDecStype.pos_dec n n = left (erefl n).
  Proof.
    by elim: n=> // p0 /= ->.
  Qed.

  Lemma to_arr_eq n t t': to_arr n (Varr t) = ok t' -> t = t'.
  Proof.
    by rewrite /= pos_dec_n_n /= => -[]<-.
  Qed.

  Lemma valid_stk_arr_arr_stk s1 s2 n n' xn xn' getx getx' m' varr v0 i (a: Array.array n word) t:
    let x := {| vtype := sarr n; vname := xn |} in
    Mvar.get m.1 x = Some getx ->
    let x' := {| vtype := sarr n'; vname := xn' |} in
    Mvar.get m.1 x' = Some getx' ->
    get_var (evm s1) x = ok (Varr a) ->
    valid_addr (emem s2) (I64.add pstk (I64.repr (getx + 8 * i))) ->
    write_mem (emem s2) (I64.add pstk (I64.repr (getx + 8 * i))) v0 = ok m' ->
    Array.set a i v0 = ok t ->
    to_arr n (Varr t) = ok varr ->
    valid_stk_arr (evm s1) (emem s2) pstk getx' n' xn' ->
    valid_stk_arr (evm s1).[x <- ok varr] m' pstk getx' n' xn'.
  Proof.
    move=> x Hget x' Hget' Ha Hvmem Hm' Ht Hvarr.
    move=> H off Hoff.
    move: H=> /(_ off Hoff) [H /= H'].
    split=> //.
    by rewrite -(write_valid _ Hm').
    case Heq: (x == x').
    + move: Heq=> /eqP []??; subst n' xn'.
      move=> a0 Ha0 v1 Hv1.
      rewrite Hget in Hget'; move: Hget'=> []?; subst getx'.
      rewrite -Hv1.
      have Htback := Ht.
      rewrite /Array.set in Ht.
      case: ((0 <=? i) && (i <? Z.pos n)) Ht=> // Ht.
      move: Ht=> -[] // Ht.
      have Ha0': a0 = FArray.set a i (ok v0).
        rewrite Ht.
        have ? := to_arr_eq Hvarr; subst varr.
        rewrite Fv.setP_eq in Ha0.
        by move: Ha0=> []<-.
      subst a0.
      rewrite (read_write_mem _ Hm') writeP Hvmem add_repr_r [getx + 8 * i]Z.add_comm.
      case Heqoff: (off == i)=> //.
      + move: Heqoff=> /eqP ->.
        rewrite eq_refl FArray.setP_eq //.
      + move: Heqoff=> /eqP Heqoff.
        have ->: I64.repr (pstk + (8 * i + getx)) == I64.repr (pstk + (8 * off + getx)) = false.
          apply/eqP=> Habs; apply: Heqoff.
          have Hok: pstk + (8 * off + getx) = pstk + (8 * i + getx).
            rewrite [_ + (_ * off + _)](get_valid_arepr Hget) //.
            rewrite [_ + (_ * i + _)](get_valid_arepr Hget).
            by rewrite Habs.
            exact: (Array.setP_inv Htback).
          lia.
        rewrite FArray.setP_neq.
        rewrite FArray.setP_neq in Hv1.
        rewrite (H' a _ _ Hv1) -?Hv1 //.
        (**)
        move: Ha.
        by apply: on_vuP=> //= z -> /Varr_inj [] _ ->.
        (**)
        apply/eqP=> Habs; apply: Heqoff; by rewrite Habs.
        apply/eqP=> Habs; apply: Heqoff; by rewrite Habs.
    + rewrite Fv.setP_neq.
      move=> a0 Ha0 v1 Hv1.
      rewrite (read_write_mem _ Hm') writeP Hvmem add_repr_r.
      case: ifP=> // /eqP Heq'.
      + exfalso.
        have Heq'': getx + 8 * i = 8 * off + getx'.
          suff: pstk + (8 * i + getx) = pstk + (8 * off + getx') by lia.
            rewrite (get_valid_arepr Hget).
            rewrite (get_valid_arepr Hget') //.
            rewrite -Heq'; congr (I64.repr _); lia.
            exact: (Array.setP_inv Ht).
        have Habs: getx + 8 * i != getx' + 8 * off.
          apply: (var_stk_diff_off_both Hget Hget')=> //.
          by rewrite Heq.
          have := Array.setP_inv Ht; lia.
          lia.
        by move: Habs=> /eqP; apply; lia.
      + by rewrite (H' _ Ha0 _ Hv1).
        by rewrite -/x' Heq.
  Qed.

  Lemma valid_stk_word_arr_stk n xan xwn geta getw (a: Array.array n word) m' s1 s2 varr t v0 i:
    let xa := {| vtype := sarr n; vname := xan |} in
    Mvar.get m.1 xa = Some geta ->
    let xw := {| vtype := sword; vname := xwn |} in
    Mvar.get m.1 xw = Some getw ->
    get_var (evm s1) xa = ok (Varr a) ->
    valid_addr (emem s2) (I64.add pstk (I64.repr (geta + 8 * i))) ->
    write_mem (emem s2) (I64.add pstk (I64.repr (geta + 8 * i))) v0 = ok m' ->
    Array.set a i v0 = ok t ->
    to_arr n (Varr t) = ok varr ->
    valid_stk_word (evm s1) (emem s2) pstk getw xwn ->
    valid_stk_word (evm s1).[xa <- ok varr] m' pstk getw xwn.
  Proof.
    move=> xa Hgeta xw Hgetw Ha Hvmem Hm' Ht Hvarr [H H'].
    split.
    + by rewrite -(write_valid _ Hm').
    move=> /= v1 Hv1.
    rewrite (read_write_mem _ Hm') writeP Hvmem.
    rewrite Fv.setP_neq in Hv1; last by rewrite vtype_diff.
    rewrite (H' v1 Hv1).
    case: ifP=> // /eqP Heq; exfalso.
    rewrite add_repr_r in Heq.
    have/eqP: geta + 8 * i != getw.
      apply: (var_stk_diff_off_l Hgeta Hgetw)=> //.
      have := (Array.setP_inv Ht);lia.
    apply.
    have Hok: pstk + (8 * i + geta) = pstk + getw.
      rewrite (get_valid_arepr Hgeta).
      rewrite (get_valid_wrepr Hgetw).
      rewrite -Heq; congr (I64.repr _); lia.
      exact: (Array.setP_inv Ht).
    lia.
  Qed.

  Lemma valid_stk_arr_stk s1 s2 vn n m' varr v0 i get (a: Array.array n word) t:
    let vi := {| vtype := sarr n; vname := vn |} in
    Mvar.get m.1 vi = Some get ->
    get_var (evm s1) vi = ok (Varr a) ->
    valid_addr (emem s2) (I64.add pstk (I64.repr (get + 8 * i))) ->
    write_mem (emem s2) (I64.add pstk (I64.repr (get + 8 * i))) v0 = ok m' ->
    Array.set a i v0 = ok t ->
    to_arr n (Varr t) = ok varr ->
    valid_stk (evm s1) (emem s2) pstk ->
    valid_stk (evm s1).[vi <- ok varr] m' pstk.
  Proof.
    move=> vi Hget Ha Hvmem Hm' Ht Hvarr H6 x.
    move: H6=> /(_ x).
    case Hget': (Mvar.get m.1 x)=> [getx|//].
    move: x Hget'=> [[| |n'|] xn] //= Hget' H.
    + exact: (valid_stk_arr_arr_stk Hget _ Ha Hvmem Hm' Ht).
    + exact: (valid_stk_word_arr_stk Hget _ Ha Hvmem Hm' Ht).
  Qed.

  Lemma valid_arr_stk n vn v0 varr i get s1 s2 m' (a: Array.array n word) t:
    let vi := {| vtype := sarr n; vname := vn |} in
    Mvar.get m.1 vi = Some get ->
    get_var (evm s1) vi = ok (Varr a) ->
    valid_addr (emem s2) (I64.add pstk (I64.repr (get + 8 * i))) ->
    write_mem (emem s2) (I64.add pstk (I64.repr (get + 8 * i))) v0 = ok m' ->
    Array.set a i v0 = ok t ->
    to_arr n (Varr t) = ok varr ->
    valid s1 s2 ->
    valid {| emem := emem s1; evm := (evm s1).[vi <- ok varr] |}
          {| emem := m'; evm := evm s2 |}.
  Proof.
    move=> vi Hget Ha Hvmem Hm' Ht Hvarr [] H1 H2 H3 H4 [H5 H6].
    split=> //=.
    + move=> w Hvmem'.
      rewrite /disjoint_stk in H1.
      rewrite (read_write_mem w Hm') writeP Hvmem.
      rewrite (H2 _ Hvmem').
      suff ->: I64.add pstk (I64.repr (get + 8 * i)) == w = false=> //.
      rewrite add_repr_r.
      apply/negP=> /eqP Habs.
      have Hi' := (Array.setP_inv Ht).
      have := (get_valid_arepr Hget Hi').
      rewrite [get + 8 * i]Z.add_comm in Habs.
      rewrite Habs.
      have := (H1 _ Hvmem').
      move: (validm Hget)=> [sx [/= [] Hsz [Hsx Hsx' _]]].
      lia.
    + move=> w.
      by rewrite -(write_valid _ Hm') H3.
    + move=> x Hx1 Hx2.
      rewrite Fv.setP_neq.
      apply: H4=> //.
      apply/negP=> /eqP Habs.
      by rewrite -Habs /is_in_stk Hget in Hx1.
    + split=> //.
      exact: (valid_stk_arr_stk Hget Ha Hvmem Hm' Ht).
  Qed.

  Lemma get_var_arr n (a: Array.array n word) vm vi:
    get_var vm vi = ok (Varr a) ->
    exists vn, vi = {| vtype := sarr n; vname := vn |}.
  Proof.
    move: vi=> [vt vn] //=.
    apply: on_vuP=> //= x Hx; rewrite /to_val.
    move: vt x Hx=> [] // n' /= x Hx /Varr_inj [-> ?].
    by exists vn.
  Qed.

  Lemma check_arr_stkW (vi vi': var_i) (s1 s2: estate) v v' e e':
    check_arr_stk m vi e vi' e' -> valid s1 s2 ->
    value_uincl v v' -> 
    forall s1', write_lval gd (Laset vi e) v s1 = ok s1' ->
    exists s2', write_lval gd (Lmem vi' e') v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move: vi=> [vi vii].
    move=> Harr Hval Hv s1'.
    have [H1 H2 H3 H4 [H5 H6]] := Hval.
    apply: rbindP=> -[] // n a Ha.
    have [vn /= Hvi] := get_var_arr Ha; subst vi; set vi := {| vtype := sarr n; vname := vn|}.
    apply: rbindP=> i.
    apply: rbindP=> vali Hvali Hi.
    apply: rbindP=> v0 Hv0.
    apply: rbindP=> t Ht.
    apply: rbindP=> vm.
    apply: set_varP => [varr Hvarr <- [] <-| _ /of_val_error] //=.
    move: Harr=> /andP [/andP [/eqP -> {vi'} Harr]].
    rewrite H5 /=. 
    have [??]:= value_uincl_word Hv Hv0; subst v v' => /=.
    case Hget: (Mvar.get m.1 vi) => [get| //] He'.
    have Hall: exists s2' : estate,
      Let m0 := write_mem (emem s2) (I64.add pstk (I64.repr (get + 8 * i))) v0
      in ok {| emem := m0; evm := evm s2 |} = ok s2' /\
      valid {| emem := emem s1; evm := (evm s1).[vi <- ok varr] |} s2'.
    + have Hvmem: valid_addr (emem s2) (I64.add pstk (I64.repr (get + 8 * i))).
      + rewrite add_repr_r [get + 8 * i]Z.add_comm.
        apply (get_valid_arr Hval Hget).
        exact: (Array.setP_inv Ht).
      have Hmem: exists m', 
         write_mem (emem s2) (I64.add pstk (I64.repr (get + 8 * i))) v0 = ok m'.
        by apply/writeV.
      move: Hmem=> [m' Hm'].
      rewrite Hm' /=.
      exists {| emem := m'; evm := evm s2 |}; split=> //=.
      exact: (valid_arr_stk Hget Ha Hvmem Hm' Ht).
    have [i0 [Heqe Heqe']] := is_addr_ofsP He';subst e e' => /=.
    rewrite Z.add_comm.
    by move: Hvali Hi => [<-] [->]. 
  Qed.

  Lemma valid_stk_mem s1 s2 ptr off val m' m'2:
    write_mem (emem s1) (I64.add ptr off) val = ok m' ->
    valid_addr (emem s2) (I64.add ptr off) ->
    ~ pstk <= I64.add ptr off < pstk + stk_size ->
    write_mem (emem s2) (I64.add ptr off) val = ok m'2 ->
    valid_stk (evm s1) (emem s2) pstk ->
    valid_stk (evm s1) m'2 pstk.
  Proof.
    move=> Hm' Hvmem Hbound Hm'2 Hv x.
    move: Hv=> /(_ x).
    case Hget: (Mvar.get m.1 x)=> [getx|//].
    move: x Hget=> [[| |n|] vn] Hget //= H.
    + move=> off0 Hoff0.
      move: H=> /(_ off0 Hoff0) [H H']; split.
      + by rewrite -(write_valid _ Hm'2).
      move=> t a Ht v0 Hv0.
      rewrite -(H' a Ht v0 Hv0).
      rewrite (read_write_mem _ Hm'2) writeP Hvmem.
      suff ->: I64.add ptr off == I64.repr (pstk + (8 * off0 + getx)) = false=> //.
      apply/eqP=> Habs.
      rewrite Habs in Hbound; apply: Hbound.
      move: (validm Hget)=> [sx [/= []Hsz [Hsx Hsx' _]]].
      rewrite -(get_valid_arepr Hget Hoff0); lia.
    + move: H=> [H H']; split.
      + by rewrite -(write_valid _ Hm'2).
      move=> v0 Hv0.
      rewrite -(H' v0 Hv0).
      rewrite (read_write_mem _ Hm'2) writeP Hvmem.
      suff ->: I64.add ptr off == I64.repr (pstk + getx) = false=> //.
      apply/eqP=> Habs.
      rewrite Habs in Hbound; apply: Hbound.
      move: (validm Hget)=> [sx [/= []Hsz [Hsx Hsx' _]]].
      rewrite -(get_valid_wrepr Hget); lia.
  Qed.

  Lemma valid_mem s1 s2 m' m'2 ptr off val:
    write_mem (emem s1) (I64.add ptr off) val = ok m' ->
    valid_addr (emem s2) (I64.add ptr off) ->
    write_mem (emem s2) (I64.add ptr off) val = ok m'2 ->
    valid s1 s2 ->
    valid {| emem := m'; evm := evm s1 |} {| emem := m'2; evm := evm s2 |}.
  Proof.
    move=> Hm' Hvmem Hm'2 [H1 H2 H3 H4 [H5 H6]].
    split=> //=.
    + move=> w Hw.
      rewrite -(write_valid _ Hm') in Hw.
      exact: H1.
    + move=> w Hw.
      apply: (read_mem_write_same Hm' Hm'2 H2).
      by rewrite (write_valid _ Hm').
    + move=> w.
      rewrite -(write_valid _ Hm') -(write_valid _ Hm'2).
      exact: H3.
    + split=> //.
      have Hvalid1: valid_addr (emem s1) (I64.add ptr off).
        apply/writeV; exists m'; exact: Hm'.
      exact: (valid_stk_mem Hm' Hvmem (H1 _ Hvalid1)).
  Qed.

  Lemma check_memW (vi vi': var_i) (s1 s2: estate) v v' e e':
    check_var m vi vi' -> check_e m e e' -> valid s1 s2 -> 
    value_uincl v v' ->
    forall s1', write_lval gd (Lmem vi e) v s1 = ok s1'->
    exists s2', write_lval gd (Lmem vi' e') v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Hvar He Hv Hu s1'.
    have Hv' := Hv.
    move: Hv'=> [] H1 H2 H3 H4 [H5 H6].
    apply: rbindP=> ptr.
    apply: rbindP=> vptr Hvptr Hptr.
    apply: rbindP=> off.
    apply: rbindP=> voff Hvoff Hoff.
    apply: rbindP=> val Hval.
    apply: rbindP=> m' Hm' []<-.
    rewrite /=.
    have ->: get_var (evm s2) vi' = ok vptr.
      have [? [->]]:= check_varP Hvar H4 Hvptr.
      by move=> /value_uincl_word -/(_ _ Hptr) [-> ->].
    rewrite /= Hptr /=.
    have [v1' [->] U]:= check_eP He Hv Hvoff.
    have [??]:= value_uincl_word U Hoff; subst voff v1' => /=.
    have Hvmem: valid_addr (emem s2) (I64.add ptr off).
      rewrite H3.
      apply/orP; left; apply/writeV; exists m'; exact: Hm'.
    have [m'2 Hm'2] : exists m', write_mem (emem s2) (I64.add ptr off) val = ok m'.
      by apply/writeV.
    have [??]:= value_uincl_word Hu Hval;subst v v'.
    rewrite Hval /= Hm'2 /=.
    exists {| emem := m'2; evm := evm s2 |}; split=> //.
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
    move: Hv'=> [] H1 H2 H3 H4 [H5 H6].
    apply: rbindP=> [[]] // n a Ha.
    apply: rbindP=> i.
    apply: rbindP=> vali Hvali Hi.
    apply: rbindP=> v0 Hv0.
    apply: rbindP=> t Ht.
    apply: rbindP=> vm.
    rewrite /set_var;apply: set_varP => //=.
    + move=> varr Hvarr <- [] <- /=.
      have [??] := value_uincl_word Hu Hv0;subst v v'.
      have [v' [->] U]:= check_eP He Hv Hvali.
      have [??]:= value_uincl_int U Hi; subst vali v' => /=.
      rewrite /= /on_arr_var.
      have [v' [->]]:= check_varP Hvar H4 Ha.
      case: v' => //= n0 a0 [?] Ha0;subst n0.
      have Hvar' := Hvar; move: Hvar'=> /andP [/andP [Hnotinstk /eqP /= Heq] notstk].
      subst vi'.
      have [t' [-> Htt'] /=]:= Array_set_uincl Ha0 Ht.
      rewrite /set_var /=.
      have Utt': value_uincl (@Varr n t) (@Varr n t') by done.
      have [varr' [-> Uarr] /=]:= of_val_uincl Utt' Hvarr.
      exists {| emem := emem s2; evm := (evm s2).[vi <- ok varr'] |}; split=> //.
      split=> //=.
      + exact: eq_vm_write.
      + split=> //.
      rewrite /get_var Fv.setP_neq //.
      exact: valid_stk_write_notinstk.
    move=> _ H;elimtype False.
    by case: (vtype vi) H => //= ?;case: CEDecStype.pos_dec.
  Qed.

  Lemma check_lvalP (r1 r2: lval) v v' (s1 s2: estate) :
    check_lval m r1 r2 -> valid s1 s2 -> 
    value_uincl v v' ->
    forall s1', write_lval gd r1 v s1 = ok s1' ->
    exists s2', write_lval gd r2 v' s2 = ok s2' /\ valid s1' s2'.
  Proof.
    move=> Hr Hv Hu; move: Hr.
    case: r1=> [vi t |vi|vi e|vi e].
    + case: r2=> // vi' t' /= /eqP -> s1' H.
      have [-> _]:= write_noneP H.
      by rewrite (uincl_write_none _ Hu H); exists s2.      
    + case: r2=> // [vi'|vi' e].
      + move=> /check_varW /(_ Hv) H s1' Hw.
        by move: (H _ _ Hu _ Hw)=> [s2' Hs2']; exists s2'.
      rewrite /write_lval /=.
      move=> /check_var_stkW /(_ Hv) H s1' Hw.
      by move: (H _ _ Hu _ Hw)=> [s2' Hs2']; exists s2'.
    + case: r2=> // vi' e'.
      move=> /andP [Hvar He] s1' Hw.
      by move: (check_memW Hvar He Hv Hu Hw)=> [s2' Hs2']; exists s2'.
    case: r2=> // vi' e'.
    move=> /check_arr_stkW /(_ Hv) H s1' Hw.
    move: (H _ _ Hu _ Hw)=> [s2' Hs2']; exists s2'=> //.
    move=> /andP [Hvar He] s1' Hw.
    move: (check_arrW Hvar He Hv Hu Hw)=> [s2' Hs2']; exists s2'=> //.
  Qed.

  Lemma check_lvalsP (r1 r2: lvals) vs vs' (s1 s2: estate) :
    all2 (check_lval m) r1 r2 -> valid s1 s2 ->
    List.Forall2 value_uincl vs vs' ->
    forall s1', write_lvals gd s1 r1 vs = ok s1' ->
    exists s2', write_lvals gd s2 r2 vs' = ok s2' /\ valid s1' s2'.
  Proof.
    elim: r1 r2 vs vs' s1 s2=> //= [|a l IH] [|a' l'] // [] //.
    + move=> vs' ? s2 ? Hvalid H;sinversion H => s1' [] <-.
      exists s2; split=> //.
    + move=> vsa vsl ? s1 s2 /andP [Hchecka Hcheckl] Hvalid H s1'.
      sinversion H.
      apply: rbindP=> x Ha Hl.
      move: (check_lvalP Hchecka Hvalid H2 Ha)=> [s3 [Hs3 Hvalid']].
      move: (IH _ _ _ _ _ Hcheckl Hvalid' H4 _ Hl)=> [s3' [Hs3' Hvalid'']].
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

  Local Lemma Hskip s: Pc s [::] s.
  Proof.
    move=> [] // => _ s' Hv.
    exists s'; split; [exact: S.Eskip|exact: Hv].
  Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I P gd s1 i s2 ->
    Pi s1 i s2 -> sem P gd s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> _ Hi _ Hc [|i' c'] //= /andP [Hi'c Hc'c] s1' Hv.
    have [s2' [Hi' Hv2]] := Hi _ Hi'c _ Hv.
    have [s3' [Hc' Hv3]] := Hc _ Hc'c _ Hv2.
    exists s3'; split=> //.
    apply: S.Eseq; [exact: Hi'|exact: Hc'].
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i P gd s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. 
    move=> _ Hi [ii' ir'] Hc s1' Hv.
    move: Hi=> /(_ ii ii' ir' Hc s1' Hv) [s2' [Hs2'1 Hs2'2]].
    by exists s2'; split.
  Qed.

  Local Lemma Hassgn s1 s2 x tag e :
    Let v := sem_pexpr gd s1 e in write_lval gd x v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn x tag e) s2.
  Proof.
    apply: rbindP=> v Hv Hw ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= x' a e' /andP [Hlval He].
    have [v' [He' Uvv']] := (check_eP He Hvalid Hv).
    move: (check_lvalP Hlval Hvalid Uvv' Hw)=> [s2' [Hw' Hvalid']].
    exists s2'; split=> //.
    apply: S.Eassgn;by rewrite He'.
  Qed.

  Local Lemma Hopn s1 s2 t o xs es :
    sem_sopn gd o s1 xs es = ok s2 ->
    Pi_r s1 (Copn xs t o es) s2.
  Proof.
    apply: rbindP=> vs.
    apply: rbindP=> w He Hop Hw ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= xs' t' o' es' /andP [/andP [Hlvals /eqP Ho] Hes].
    have [vs' [He' Uvv']] := (check_esP Hes Hvalid He);subst o'.
    have [w' [Hop' Uww']]:= vuincl_exec_opn Uvv' Hop.
    have [s2' [Hw' Hvalid']] := check_lvalsP Hlvals Hvalid Uww' Hw.
    exists s2'; split=> //.
    by apply: S.Eopn;rewrite /sem_sopn He' /= Hop'.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr gd s1 e in to_bool x = Ok error true ->
    sem P gd s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP=> v Hv Htrue ? Hc ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c1' c2' /andP [/andP [He Hcheck] _].
    move: (Hc _ Hcheck _ Hvalid)=> [s2' [Hsem Hvalid']].
    exists s2'; split=> //.
    apply: S.Eif_true=> //.
    have [v' [-> ]]:= check_eP He Hvalid Hv.
    by move=> /value_uincl_bool -/(_ _ Htrue) [_ ->].
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr gd s1 e in to_bool x = Ok error false ->
    sem P gd s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    apply: rbindP=> v Hv Hfalse ? Hc ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= e' c1' c2' /andP [/andP [He _] Hcheck].
    move: (Hc _ Hcheck _ Hvalid)=> [s2' [Hsem Hvalid']].
    exists s2'; split=> //.
    apply: S.Eif_false=> //.
    have [v' [-> ]]:= check_eP He Hvalid Hv.
    by move=> /value_uincl_bool -/(_ _ Hfalse) [_ ->].
  Qed.

  Local Lemma Hwhile_true s1 s2 s3 s4 c e c' :
    sem P gd s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr gd s2 e in to_bool x = ok true ->
    sem P gd s2 c' s3 -> Pc s2 c' s3 ->
    sem_i P gd s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
  Proof.
    move=> _ Hc.
    apply: rbindP=> v Hv Htrue ? Hc' ? Hwhile ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= c2 e2 c2' /andP [/andP [Hc2 He2] Hc2'].
    move: (Hc _ Hc2 _ Hvalid)=> [s2' [Hsem' Hvalid']].
    move: (Hc' _ Hc2' _ Hvalid')=> [s2'' [Hsem'' Hvalid'']].
    have [|s3' [Hsem''' Hvalid''']] := (Hwhile ii1 ii2 (Cwhile c2 e2 c2') _ _ Hvalid'').
    by rewrite /= Hc2 He2 Hc2'.
    exists s3'; split=> //.
    apply: S.Ewhile_true; eauto.
    have [v' [-> ]]:= check_eP He2 Hvalid' Hv.
    by move=> /value_uincl_bool -/(_ _ Htrue) [_ ->].
  Qed.

  Local Lemma Hwhile_false s1 s2 c e c' :
    sem P gd s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr gd s2 e in to_bool x = ok false ->
    Pi_r s1 (Cwhile c e c') s2.
  Proof.
    move=> _ Hc.
    apply: rbindP=> v Hv Hfalse ii1 ii2 i2 Hi2 s1' Hvalid.
    case: i2 Hi2=> //= c2 e2 c2' /andP [/andP [Hc2 He2] _].
    move: (Hc _ Hc2 _ Hvalid)=> [s2' [Hsem' Hvalid']].
    exists s2'; split=> //.
    apply: S.Ewhile_false; eauto.
    have [v' [-> ]]:= check_eP He2 Hvalid' Hv.
    by move=> /value_uincl_bool -/(_ _ Hfalse) [_ ->].
  Qed.

  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr gd s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr gd s1 hi in to_int x = Ok error vhi ->
    sem_for P gd i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof. by []. Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof. by []. Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem P gd s1' c s2 ->
    Pc s1' c s2 ->
    sem_for P gd i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof. by []. Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs gd s1 args = Ok error vargs ->
    sem_call P gd (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_lvals gd {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof. by []. Qed.

  Local Lemma Hproc m1 m2 fn f vargs s1 vm2 vres:
    get_fundef P fn = Some f ->
    write_vars (f_params f) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem P gd s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    Pc s1 (f_body f) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res f) = ok vres ->
    List.Forall is_full_array vres ->
    Pfun m1 fn vargs m2 vres.
  Proof. by []. Qed.

  Lemma check_cP s1 c s2: sem P gd s1 c s2 -> Pc s1 c s2.
  Proof.
    apply (@sem_Ind P gd Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.
End PROOF.

Lemma init_mapP nstk pstk l sz m m1 m2 :
  Memory.alloc_stack m1 sz = ok (pstk, m2) -> 
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
  + elim:l => [|vp l Hrec] p p'//=.
    + by move=>[] <- ???;split=>//;omega.
    rewrite {2}/f1;case:ifPn=> //= /Z.leb_le Hle.
    case Hs : size_of=> [svp|]//= /Hrec /= {Hrec}Hrec H2 H3 H4. 
    have Hpos := size_of_pos Hs.
    case:Hrec.
    + move=> x px;rewrite Mvar.setP;case:ifPn => /eqP Heq.
      + move=> [] ?;subst;exists svp;split=>//;split.
        + omega. + omega.
        move=> y py sy Hne.
        by rewrite Mvar.setP_neq // => /H4 H /H ?;omega.
      move=> /H2 [sx] [Hsx] [] Hle0 Hpx Hy;exists sx;split=>//;split=>//.
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
  rewrite /g;case:ifP => //= /Z.leb_le Hp [] <- /=.
  split=>// x px Hx.
  case :(Hv x px Hx) => //= sx [] Hsx [] H1 H2 H3.
  by exists sx;split=>//;split=>//;omega.
Qed.

Import Memory.

Lemma check_fdP (P: prog) (gd: glob_defs) (SP: sprog) l fn fn' fd fd':
  get_fundef P fn = Some fd ->
  get_fundef SP fn' = Some fd' ->
  check_fd l fd fd' ->
  forall m1 va m1' vr, 
    sem_call P gd m1 fn va m1' vr ->
    (exists p, Memory.alloc_stack m1 (sf_stk_sz fd') = ok p) ->
    S.sem_call SP gd m1 fn' va m1' vr.
Proof.
  move=> get Sget.
  rewrite /check_fd.
  case Hinit: init_map => [m|] //= /andP[]/andP[] Hp Hr Hi.
  move=> m1 va m1' vr H; sinversion H=> -[[pstk m2] Halloc].
  have Hf: Some f = Some fd.
    by rewrite -get -H0.
  move: Hf=> [] Hf.
  subst f.
  have [/= Hv Hestk] := init_mapP Halloc Hinit.
  have Hstk: stk_ok pstk (sf_stk_sz fd').
    by move: Halloc=> /alloc_stackP [].
  have Hval'': valid m (sf_stk_sz fd') pstk {| emem := m1; evm := vmap0 |} {| emem := m2; evm := vmap0.[{| vtype := sword; vname := sf_stk_id fd' |} <- ok pstk] |}.
    move: Halloc=> /alloc_stackP [] Ha1 Ha2 Ha3 Ha4.
    split=> //=.
    + move=> x.
      case Heq: (x == {| vtype := sword; vname := sf_stk_id fd' |}).
      + move: Heq=> /eqP -> /=.
        rewrite /is_vstk /vstk.
        by rewrite Hestk eq_refl.
      + rewrite Fv.setP_neq=> //.
        apply/eqP=> Habs.
        by rewrite Habs eq_refl in Heq.
    + split.
      by rewrite /vstk Hestk /= /get_var Fv.setP_eq.
      move=> x.
      case Hget: (Mvar.get m.1 x)=> [a|//].
      case Htype: (vtype x)=> [| |n|] //.
      + move=> off Hoff; split.
        rewrite Ha3.
        apply/orP; right.
        rewrite -!add_repr_r.
        have Hx: x = {| vtype := sarr n; vname := vname x |}.
          case: x Hget Htype=> [vt vn] Hget Htype /=.
          by rewrite -Htype.
        rewrite Hx in Hget.
        apply: (valid_get_a_off _ Hv Hget)=> //.
        rewrite /vmap0=> a0 Habs v Habs'; exfalso.
        rewrite /Fv.get /= in Habs.
        move: Habs=> [] Habs.
        rewrite -Habs in Habs'.
        by rewrite /FArray.get /Array.empty /FArray.cnst /= in Habs'.
      + split.
        rewrite Ha3.
        apply/orP; right.
        rewrite -!add_repr_r.
        have Hx: x = {| vtype := sword; vname := vname x |}.
          case: x Hget Htype=> [vt vn] Hget Htype /=.
          by rewrite -Htype.
        rewrite Hx in Hget.
        apply: (valid_get_w _ Hv Hget)=> //.
        rewrite /vmap0 /= /Fv.empty /= => v Habs.
        by rewrite /Fv.get /= in Habs.
  have := check_varsW Hp Hval'' _ H1.
  move=> /(_ va) [ |s2 [Hs2 Hv2]];first by apply List_Forall2_refl.
  have [[m2' vm2'] [Hs2' Hv2']] := check_cP SP Hstk Hv H2 Hi Hv2.
  apply: S.EcallRun; eauto=> //.
  + move: Hv2'=> [] _ _ _ Heqvm _.
    have [vr' [/= ->]] := check_varsP Hr Heqvm H3.
    by move=> /(is_full_array_uincls H4) ->.
  + apply eq_memP=> w.
    pose sz := sf_stk_sz fd'.
    have -> := @free_stackP m2' (free_stack m2' pstk sz) pstk sz (erefl _) w.
    case Hv2' => /=;rewrite /disjoint_stk => Hdisj Hmem Hvalw _ _.
    move: (Hdisj w) (Hmem w) (Hvalw w)=> {Hdisj Hmem Hvalw} Hdisjw Hmemw Hvalw.
    case Heq1: (read_mem m1' w) => [w'|].
    + have Hw : valid_addr m1' w by apply /readV;exists w'.
      have -> : ((pstk <=? w) && (w <? pstk + sz))=false. 
      + by apply /negbTE /negP => /andP[] /Z.leb_le ? /Z.ltb_lt ?;apply Hdisjw.
      by rewrite -Heq1;apply Hmemw.
    have ? := read_mem_error Heq1;subst;case:ifP=> Hbound //.
    case Heq2: (read_mem m2' w) => [w'|];last by rewrite (read_mem_error Heq2).
    have : valid_addr m2' w by apply /readV;exists w'.
    by rewrite Hvalw Hbound orbC /= => /readV [w1];rewrite Heq1.
  Qed.

Definition alloc_ok SP fn m1 :=
  forall fd, get_fundef SP fn = Some fd ->
  exists p, Memory.alloc_stack m1 (sf_stk_sz fd) = ok p.

Lemma check_progP (P: prog) (gd: glob_defs) (SP: sprog) l fn:
  check_prog P SP l ->
  forall m1 va m1' vr, 
    sem_call P gd m1 fn va m1' vr ->
    alloc_ok SP fn m1 ->
    S.sem_call SP gd m1 fn va m1' vr.
Proof.
  move=> Hcheck m1 va m1' vr H Halloc.
  have H' := H; sinversion H'.
  move: (all_progP Hcheck H0)=> [fd' [l' [Hfd' Hl']]].
  by apply: check_fdP=> //; eauto.
Qed.
