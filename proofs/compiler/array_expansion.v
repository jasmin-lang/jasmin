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
Require Import psem allocation.
Require Import compiler_util ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.

Local Open Scope seq_scope.

Module CmpIndex.

  Definition t := [eqType of Z].

  Definition cmp : t -> t -> comparison := Z.compare.

  Lemma cmpO : Cmp cmp.
  Proof. apply ZO. Qed.

End CmpIndex.

Local Notation index:= Z.

Module Mi := gen_map.Mmake CmpIndex.

Module Ma := MakeMalloc Mi.

Module CBEA.

  Module M.

    Record array_info := {
      ai_ty    : wsize;
      ai_elems : Ma.t;
    }.

    Definition alloc_t := Mvar.t array_info.

    Definition empty_alloc : alloc_t := Mvar.empty array_info.

    Definition get_alloc (alloc:alloc_t) (x:var) (p:index) :=
      match Mvar.get alloc x with
      | Some ai =>
        match Ma.get ai.(ai_elems) p with
        | Some id => Some (ai.(ai_ty), id)
        | None => None
        end
      | None => None
      end.

    Definition valid (alloc: alloc_t) (allocated:Sv.t) :=
      forall x p wz id,
        get_alloc alloc x p = Some (wz, id) ->
        Sv.In x allocated /\ Sv.In ({|vtype := sword wz; vname := id |}) allocated.

    Record expansion := mkExpansion {
      alloc     : alloc_t;
      allocated : Sv.t;
      Valid     : valid alloc allocated
    }.

    Definition t := expansion.

    Lemma valid_empty : valid empty_alloc Sv.empty.
    Proof. by move=> x p wz id;rewrite /get_alloc Mvar.get0. Qed.

    Definition empty := mkExpansion valid_empty.

    Definition get (m:expansion) (x:var) (p:index) :=
      get_alloc m.(alloc) x p.

    Definition merge_alloc (m1 m2: alloc_t) :=
      Mvar.fold
       (fun x ai m =>
          match Mvar.get m2 x with
          | Some ai' =>
            let wz := ai.(ai_ty) in
            if wz == ai'.(ai_ty) then
              Mvar.set m x {|ai_ty := wz; ai_elems := Ma.merge ai.(ai_elems) ai'.(ai_elems) |}
            else m
          | None      => m
          end) m1 empty_alloc.

    Lemma merge_allocP_ai (m1 m2: alloc_t) x ai :
        Mvar.get (merge_alloc m1 m2) x = Some ai →
        exists ai1 ai2,
          [/\ Mvar.get m1 x = Some ai1,  Mvar.get m2 x = Some ai2,
              ai.(ai_ty) = ai1.(ai_ty), ai.(ai_ty) = ai2.(ai_ty) &
              ai.(ai_elems) = Ma.merge ai1.(ai_elems) ai2.(ai_elems)].
    Proof.
      rewrite /merge_alloc Mvar.foldP;set f := (f in foldl f).
      pose P := fun m =>
         Mvar.get m x = Some ai ->
         exists ai1 ai2,
          [/\ Mvar.get m1 x = Some ai1,  Mvar.get m2 x = Some ai2,
               ai.(ai_ty) = ai1.(ai_ty), ai.(ai_ty) = ai2.(ai_ty) &
              ai.(ai_elems) = Ma.merge ai1.(ai_elems) ai2.(ai_elems)].
      have H : forall (l:seq (var * array_info)) m,
                 (forall p, List.In p l -> Mvar.get m1 p.1 = Some p.2) ->
                 P m -> P (foldl f m l).
      + elim=> [|xai l Hrec] //= m Hl Hm;apply Hrec.
        + by move=> ? H;apply Hl; auto.
        rewrite /f /P; case Heq2: (Mvar.get m2 xai.1) => [ai'|//].
        case: eqP => heq; last by apply Hm.
        rewrite /get_alloc Mvar.setP.
        case: eqP => Heq /=;last by apply Hm.
        subst; rewrite Heq2 (Hl xai); last by auto.
        move=> [<-]; exists xai.2, ai';split => //.
      apply H; first by move=> ?;apply Mvar.elementsIn.
      by rewrite /P Mvar.get0.
    Qed.

    Lemma merge_allocP (m1 m2: alloc_t) x p wz id :
      get_alloc (merge_alloc m1 m2) x p = Some (wz,id) →
      get_alloc m1 x p = Some (wz,id) ∧ get_alloc m2 x p = Some (wz, id).
    Proof.
      rewrite /get_alloc.
      case heq : (Mvar.get (merge_alloc m1 m2) x) => [m|//].
      have [ai1 [ai2 [-> -> <- <- ->]]]:= merge_allocP_ai heq.
      case heqa : Ma.get => [ma |//].
      move=> [??];subst wz ma.
      by have [-> ->]:= Ma.mergeP heqa.
    Qed.

    Lemma valid_merge r1 r2 :
       valid (merge_alloc (alloc r1) (alloc r2))
             (Sv.union (allocated r1) (allocated r2)).
    Proof.
      move=> x p wz id /merge_allocP [] /(@Valid r1)[??]/(@Valid r2)[??];SvD.fsetdec.
    Qed.

    Definition merge r1 r2 :=
       mkExpansion (@valid_merge r1 r2).

    Definition test_incl_alloc (m2:alloc_t) (x:var) (ai:array_info) :=
      match Mvar.get m2 x with
      | Some ai' => (ai.(ai_ty) == ai'.(ai_ty)) && Ma.incl ai.(ai_elems) ai'.(ai_elems)
      | None     => false
      end.

    Definition incl_alloc (m1 m2:alloc_t) :=
      Mvar.fold (fun x ai b => b && test_incl_alloc m2 x ai) m1 true.

    Lemma incl_allocP m1 m2 :
      reflect (forall x ai, Mvar.get m1 x = Some ai -> test_incl_alloc m2 x ai)
        (incl_alloc m1 m2).
    Proof.
      rewrite /incl_alloc Mvar.foldP;set f := (f in foldl f).
      set l := (Mvar.elements _); set b := true.
      have : forall p, List.In p l -> Mvar.get m1 p.1 = Some p.2.
      + by move=> p /Mvar.elementsIn.
      have : uniq [seq x.1 | x <- l] by apply Mvar.elementsU.
      have :
         reflect (forall x ai, ~ List.In (x,ai) l ->
                    Mvar.get m1 x = Some ai -> test_incl_alloc m2 x ai) b.
      + by constructor=> x ai /Mvar.elementsIn.
      elim:l b=> /= [|p ps Hrec] b Hb => [Hu | /andP[Hnin Hu]] Hin.
      + by apply (equivP Hb);split=> H ?? => [|_];apply H.
      apply Hrec=> //;last by move=> ? Hp0;apply Hin;auto.
      rewrite /f;case: Hb=> {Hrec} /= Hb.
      + case Heq : test_incl_alloc;constructor.
        + move=> x ai hin; case: (x =P p.1) => hx.
          + by subst x;rewrite Hin => [[<-]|];auto.
          by apply Hb => -[ ?| //];subst p;apply hx.
        move=> /(_ p.1 p.2); rewrite Heq Hin;last by auto.
        have h: ¬ List.In (p.1, p.2) ps.
        + move=> hin; move: Hnin; have ->// : p.1 \in [seq x.1 | x <- ps].
          by apply /xseq.InP; apply List.in_map; case: (p) hin.
        by move=> /(_ h erefl).
      by constructor=> H;apply Hb=> x id h; apply H;intuition.
    Qed.

    Lemma incl_alloc_refl m : incl_alloc m m.
    Proof.
      apply /incl_allocP => x ai; rewrite /test_incl_alloc => ->.
      rewrite eq_refl /=; apply Ma.incl_refl.
    Qed.

    Lemma incl_alloc_trans m2 m1 m3 :
      incl_alloc m1 m2 -> incl_alloc m2 m3 -> incl_alloc m1 m3.
    Proof.
      move=> /incl_allocP h1 /incl_allocP h2; apply /incl_allocP => x ai /h1.
      rewrite /test_incl_alloc.
      case heq : (Mvar.get m2 x) => [ ai2| //] /andP [/eqP -> hi1].
      have := h2 _ _ heq;rewrite /test_incl_alloc.
      by case: Mvar.get => // ai3 /andP [->];apply Ma.incl_trans.
    Qed.

    Definition incl r1 r2 :=
      incl_alloc (alloc r1) (alloc r2) && Sv.subset (allocated r2) (allocated r1).

    Lemma incl_refl r: incl r r.
    Proof. rewrite /incl incl_alloc_refl /=;apply SvP.subset_refl. Qed.

    Lemma incl_trans r2 r1 r3: incl r1 r2 -> incl r2 r3 -> incl r1 r3.
    Proof.
      rewrite /incl=> /andP[]Hi1 Hs1 /andP[] Hi2 Hs2.
      rewrite (incl_alloc_trans Hi1 Hi2) /=.
      apply: SvP.subset_trans Hs2 Hs1.
    Qed.

    Lemma merge_incl_l r1 r2: incl (merge r1 r2) r1.
    Proof.
      rewrite /incl /merge /= SvP.union_subset_1 andbT.
      apply /incl_allocP => x ai /merge_allocP_ai [ai1 [ai2 [heq1 heq2 ht1 ht2 heq3]]].
      by rewrite /test_incl_alloc heq1 ht1 heq3 eq_refl Ma.merge_incl_l.
    Qed.

    Lemma merge_incl_r r1 r2: incl (merge r1 r2) r2.
    Proof.
      rewrite /incl /merge /= SvP.union_subset_2 andbT.
      apply /incl_allocP => x ai /merge_allocP_ai [ai1 [ai2 [heq1 heq2 ht1 ht2 heq3]]].
      by rewrite /test_incl_alloc heq2 ht2 heq3 eq_refl Ma.merge_incl_r.
    Qed.

    Definition remove_alloc id (m:alloc_t) :=
      Mvar.map (fun ai => {| ai_ty := ai.(ai_ty);
                             ai_elems := Ma.remove ai.(ai_elems) id |}) m.

    Lemma valid_remove_alloc id r :
      valid (remove_alloc id (alloc r)) (allocated r).
    Proof.
      move=> y ny wzy idy; have := @Valid r y ny wzy idy.
      rewrite /get_alloc /remove_alloc Mvar.mapP.
      case: (Mvar.get (alloc r) y) => //= ai.
      by rewrite Ma.removeP; case: Ma.get => [id1 | ] //=; case: eqP.
    Qed.

    Definition set_alloc wz x p id (m:alloc_t) :=
      let m := remove_alloc id m in
      let ai :=
        match Mvar.get m x with
        | Some ai =>
          if ai.(ai_ty) == wz then
            {| ai_ty := wz; ai_elems := Ma.set ai.(ai_elems) p id |}
          else
            {| ai_ty := wz; ai_elems := Ma.set Ma.empty p id |}
        | None =>
            {| ai_ty := wz; ai_elems := Ma.set Ma.empty p id |}
        end in
      Mvar.set m x ai.

    Lemma valid_set_arr wz x nx id r:
      valid (set_alloc wz x nx id (alloc r))
            (Sv.add {|vtype := sword wz; vname := id|} (Sv.add x (allocated r))).
    Proof.
      move=> y ny wzy idy; rewrite /get_alloc /set_alloc.
      have := @valid_remove_alloc id r.
      move: (remove_alloc _ _) => m hval.
      case: (x =P y) => [<- | /eqP Hneq].
      + rewrite Mvar.setP_eq.
        have aux :
          match Ma.get (Ma.set Ma.empty nx id) ny with
          | Some id0 => Some (wz, id0)
          | None => None
          end = Some (wzy, idy) →
          Sv.In x (Sv.add {| vtype := sword wz; vname := id |} (Sv.add x (allocated r)))
          ∧ Sv.In {| vtype := sword wzy; vname := idy |}
              (Sv.add {| vtype := sword wz; vname := id |} (Sv.add x (allocated r))).
        + case: (nx =P ny) => [? | /eqP ne].
          + by subst nx;rewrite Ma.setP_eq => -[??];subst wz id; SvD.fsetdec.
          case heq : Ma.get => [n | //].
          by have := Ma.setP_neq ne heq; rewrite Ma.get0 => -[].
        case heq: Mvar.get => [ai |] //=.
        case : eqP => eqty //=.
        case heqa: Ma.get => [i| //].
        move=> [??];subst wz i wzy => /=;split; first by SvD.fsetdec.
        move: heqa; case: (nx =P ny) => [-> | /eqP heqn].
        + by rewrite Ma.setP_eq => -[->];SvD.fsetdec.
        move=> /(Ma.setP_neq heqn) [h1 h2].
        have := @hval x ny (ai.(ai_ty)) idy.
        by rewrite /get_alloc heq h1 => -[] //; SvD.fsetdec.
      rewrite Mvar.setP_neq //.
      by move=> /hval; SvD.fsetdec.
    Qed.

    Definition set_arr wz x N id r := mkExpansion (@valid_set_arr wz x N id r).

    Lemma incl_alloc_get r1 r2 x n wz id :
      incl_alloc (M.alloc r1) (M.alloc r2) ->
      get r1 x n = Some (wz, id) ->
      get r2 x n = Some (wz, id).
    Proof.
      move=> /incl_allocP; rewrite /get /get_alloc.
      case heq: (Mvar.get (alloc r1) x) => [ai | //].
      move=> /(_ _ _ heq); rewrite /test_incl_alloc.
      case: Mvar.get => // ai' /andP [] /eqP -> /Ma.inclP hma.
      case heq1: Ma.get => [id1 |// ].
      by move=> [??];subst;rewrite (hma _ _ heq1).
    Qed.

    Lemma get_set_arr sw1 wz x1 i nx2 r x n0 id:
      get (set_arr sw1 x1 i nx2 r) x n0 = Some (wz, id) ->
      if x1 == x then
        (wz = sw1 /\ if i == n0 then id = nx2 else nx2 <> id /\ get r x1 n0 = Some (sw1, id))
      else
        nx2 <> id /\ M.get r x n0 = Some (wz, id).
    Proof.
      rewrite /set_arr /get /= /set_alloc /get_alloc.
      pose m := remove_alloc nx2 (alloc r).
      have hdef :
       match
         Mvar.get (Mvar.set m x1
                     {| ai_ty := sw1; ai_elems := Ma.set Ma.empty i nx2 |}) x with
       | Some ai =>
          match Ma.get (ai_elems ai) n0 with
          | Some id0 => Some (ai_ty ai, id0)
          | None => None
          end
       | None => None
       end = Some (wz, id) →
       if x1 == x
       then wz = sw1 ∧ (if i == n0 then id = nx2 else nx2 <> id /\ None = Some (sw1, id))
       else  nx2 <> id /\
       match Mvar.get (alloc r) x with
       | Some ai =>
         match Ma.get (ai_elems ai) n0 with
         | Some id0 => Some (ai_ty ai, id0)
         | None => None
         end
       | None => None
       end = Some (wz, id).
      + case: eqP => [ ?| /eqP hne].
        + subst x1; rewrite Mvar.setP_eq /=.
          case: eqP => [ ?| /eqP hnei].
          + by subst n0; rewrite Ma.setP_eq => -[-> ->].
          case heq : Ma.get => [id0 | //].
          by have := Ma.setP_neq hnei heq; rewrite Ma.get0 => -[].
        rewrite Mvar.setP_neq // /m Mvar.mapP.
        case: (Mvar.get (alloc r) x) => //= ai.
        by rewrite Ma.removeP; case: Ma.get => // id'; case: eqP => //= ? [<- <-].
      rewrite /remove_alloc Mvar.mapP.
      case : (Mvar.get (alloc r) x1) => //= ai.
      case : eqP => [? {hdef}| ?]; last first.
      + by move=> /hdef; case: ifP => ? //; case: ifP => // ? [? []].
      case: eqP => [ ? | /eqP hne];last first.
      + rewrite Mvar.setP_neq // Mvar.mapP.
        case: (Mvar.get (alloc r) x) => //= ai1.
        by rewrite Ma.removeP; case: Ma.get => // id'; case: eqP => //= ? [<- <-].
      subst sw1 x1; rewrite Mvar.setP_eq /=.
      case: eqP => [ ?| /eqP hnei].
      + by subst n0; rewrite Ma.setP_eq => -[-> ->].
      case heq : Ma.get => // -[<- <-];split => //.
      have [ ]:= Ma.setP_neq hnei heq.
      by rewrite Ma.removeP; case:Ma.get => //= id1;case:eqP => // _ [<-].
    Qed.

  End M.

  Definition eq_alloc (r:M.t) (vm vm':vmap) :=
    (forall x, ~Sv.In x (M.allocated r) -> eval_uincl vm.[x] vm'.[x]) /\
    (forall x (n:Z) wz id, M.get r x n = Some (wz,id) ->
     match x with
     | Var (sarr s) id' =>
       let x := Var (sarr s) id' in
       let x' := Var (sword wz) id in
       exists t, vm.[x] = ok t /\
       ((@WArray.get s AAscale wz t n) >>= (fun w => ok (pword_of_word w))) = vm'.[x']
     | _ => False
     end).

  Lemma eq_alloc_empty : eq_alloc M.empty vmap0 vmap0.
  Proof. by done. Qed.

  Lemma eq_alloc_incl r1 r2 vm vm':
    M.incl r2 r1 ->
    eq_alloc r1 vm vm' ->
    eq_alloc r2 vm vm'.
  Proof.
    move=> /andP[] Hincl /Sv.subset_spec Hsub [] Hv Ha;split.
    + move=> x Hx;apply: Hv;SvD.fsetdec.
    by move=> x n wz id /(M.incl_alloc_get Hincl) -/Ha.
  Qed.

  Definition check_var m (x1 x2:var) :=
    (x1 == x2) && ~~Sv.mem x1 (M.allocated m).

  Definition check_gvar m (x1 x2 : gvar) := 
    (x1.(gs) == x2.(gs)) &&
      if is_lvar x1 then check_var m x1.(gv) x2.(gv) 
      else x1.(gv).(v_var) == x2.(gv).(v_var).

  Fixpoint check_eb m (e1 e2:pexpr) : bool :=
    match e1, e2 with
    | Pconst   n1, Pconst   n2 => n1 == n2
    | Pbool    b1, Pbool    b2 => b1 == b2
    | Parr_init n1, Parr_init n2 => n1 == n2
    | Pvar     x1, Pvar     x2 => check_gvar m x1 x2
    | Pget aa1 wz1 x1 e1, Pget aa2 wz2 x2 e2 => 
      (aa1 == aa2) && (wz1 == wz2) && check_gvar m x1 x2 && check_eb m e1 e2
    | Pget aa1 wz1 x1 e1, Pvar  x2    =>
      (aa1 == AAscale) && is_lvar x1 && is_lvar x2 &&
      match is_const e1 with
      | Some n1 => (M.get m x1.(gv).(v_var) n1 == Some (wz1, vname x2.(gv))) && (vtype x2.(gv) == sword wz1)
      | _ => false
      end
    | Pload sw1 x1 e1, Pload sw2 x2 e2 => (sw1 == sw2) && check_var m x1 x2 && check_eb m e1 e2
    | Papp1 o1 e1, Papp1 o2 e2 => (o1 == o2) && check_eb m e1 e2
    | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
      (o1 == o2) && check_eb m e11 e21 && check_eb m e12 e22
    | PappN o1 es1, PappN o2 es2 =>
      (o1 == o2) && all2 (check_eb m) es1 es2
    | Pif t e e1 e2, Pif t' e' e1' e2' =>
      (t == t') && check_eb m e e' && check_eb m e1 e1' && check_eb m e2 e2'
    | _, _ => false
    end.

  Definition check_e (e1 e2:pexpr) m :=
    if check_eb m e1 e2 then cok m else cerror (Cerr_arr_exp e1 e2).

  Definition check_lval (_:option (stype * pexpr)) (r1 r2:lval) m :=
    match r1, r2 with
    | Lnone _ t1, Lnone _ t2 =>
      if t1 == t2 then cok m
      else cerror (Cerr_arr_exp_v r1 r2)
    | Lvar x1, Lvar x2 =>
      if check_var m x1 x2 then cok m
      else cerror (Cerr_arr_exp_v r1 r2)
    | Lmem sw1 x1 e1, Lmem sw2 x2 e2 =>
      if (sw1 == sw2) && check_var m x1 x2 && check_eb m e1 e2 then cok m
      else cerror (Cerr_arr_exp_v r1 r2)
    | Laset AAscale sw1 x1 e1, Lvar x2 =>
      match is_const e1 with
      | Some n1 =>
        if vtype x2 == sword sw1 then
          ok (M.set_arr sw1 x1 n1 (vname x2) m)
        else cerror (Cerr_arr_exp_v r1 r2)
      | None    => cerror (Cerr_arr_exp_v r1 r2)
      end
    | Laset aa1 sw1 x1 e1, Laset aa2 sw2 x2 e2 =>
      if (aa1 == aa2) && (sw1 == sw2) && check_var m x1 x2 && check_eb m e1 e2 then cok m
      else cerror (Cerr_arr_exp_v r1 r2)
    | _, _ => cerror (Cerr_arr_exp_v r1 r2)
    end.

  Lemma check_varP r vm1 vm2 x1 x2 v1 :
    eq_alloc r vm1 vm2 ->
    check_var r x1 x2 ->
    get_var vm1 x1 = ok v1 ->
    exists2 v2, get_var vm2 x2 = ok v2 & value_uincl v1 v2.
  Proof.
    move=> [Hee _] /andP[]/eqP <- /Sv_memP /Hee Hin Hget;move: Hin;rewrite /get_var.
    apply: on_vuP Hget => // z -> ?;subst v1.
    by case: vm2.[x1] => //= a Ha; eauto.
  Qed.

  Lemma check_gvarP r gd vm1 vm2 x1 x2 v1 : 
    eq_alloc r vm1 vm2 ->
    check_gvar r x1 x2 ->
    get_gvar gd vm1 x1 = ok v1 ->
    exists2 v2, get_gvar gd vm2 x2 = ok v2 & value_uincl v1 v2.
  Proof.
    rewrite /check_gvar /get_gvar /is_lvar; case: eqP => //= ->.
    case: ifP => hgv; first by apply: check_varP.
    by move=> heq /eqP -> ->;eauto.
  Qed.

  Section CHECK_EBP.

    Context (gd: glob_decls) (r: M.expansion) (m: mem) (vm1 vm2: vmap)
            (Hrn: eq_alloc r vm1 vm2).

    Let P e1 : Prop :=
      ∀ e2 v1, check_eb r e1 e2 →
        sem_pexpr gd {| emem := m ; evm := vm1 |} e1 = ok v1 →
      exists2 v2, 
        sem_pexpr gd {| emem := m ; evm := vm2 |} e2 = ok v2 & value_uincl v1 v2.

    Let Q es1 : Prop :=
      ∀ es2 vs1, all2 (check_eb r) es1 es2 →
        sem_pexprs gd {| emem := m ; evm := vm1 |} es1 = ok vs1 →
      exists2 vs2, sem_pexprs gd {| emem := m ; evm := vm2 |} es2 = ok vs2 &
        List.Forall2 value_uincl vs1 vs2.

    Lemma check_e_esbP : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; subst P Q; split => /=.
      - by case => // _ _ [<-]; exists [::]; eauto.
      - move => e rec es ih [] // e' es' q /andP [] he hes.
        t_xrbindP => v ok_v vs ok_vs <-{q} /=.
        move: rec => /(_ _ _ he ok_v) [] v' -> h.
        by move: ih => /(_ _ _ hes ok_vs) [] vs' -> hs /=; eauto.
      - by move => z1 [] // z2 _ /eqP <- [<-] /=; exists z1.
      - by move => z1 [] // z2 _ /eqP <- [<-] /=; exists z1.
      - by move => n1 [] // n2 _ /eqP <- [<-] /=; eexists => //=.
      - by move => x1 [] // x2 v h; apply: check_gvarP h.
      - move => aa1 sz1 x1 e1 ih1 [] //.
        + case: x1 => -[[ty1 x1] ii1] [] //= [[[ty2 x2] ii2] []] //= v1 /= /andP [] /andP [] /andP [] /eqP ? h1 h2 // {h1 h2}.
          case: is_constP => //= ze /andP [] /eqP hget /eqP ?;subst aa1 ty2.
          rewrite /get_gvar /=.
          apply: on_arr_varP => n t Htx1.
          rewrite /get_var /=; apply: on_vuP => //= x1t.
          have [_ /(_ _ _ _ _ hget) {hget}] := Hrn. 
          case: ty1 Htx1 x1t => //= n' hle x1t [x1t' [->]].
          move=> h [] ? /Varr_inj [en];subst n' x1t' => /= ?; subst x1t.
          t_xrbindP => w hg ?;subst v1.
          by (move: h;rewrite hg /= => <- /=; eexists; first reflexivity) => /=.
        move=> aa ws v p v1 /andP[] /andP[] /andP []/eqP ? /eqP ?;subst ws aa1.
        move=> /(check_gvarP Hrn) /= hget /ih1 hrec {ih1}.
        apply: on_arr_gvarP => n t /= Htx1 /hget [v2 hget2 hincl].
        t_xrbindP => n1 v3 /hrec [v4 -> hv3].   
        move=> /(value_uincl_int hv3) [??];subst v3 v4.
        rewrite /on_arr_var hget2 /= => w1.
        have [n' [t' ? hu]]:= value_uinclE hincl;subst v2.
        (move=> /(WArray.uincl_get hu) -> <- /=; eexists; first reflexivity) => /=.
        by apply word_uincl_refl.

    - move => sz1 x1 e1 He1 [] // sz2 x2 e2 v1.
      move=> /andP[] /andP[] /eqP <- Hcv /He1 Hce;apply: rbindP => w1.
      t_xrbindP => vx1 /(check_varP Hrn Hcv) [] vx2 /= ->.
      move=> /value_uincl_word H/H{H} H.
      move => w2 ve1 /Hce [] ve2 -> /=; rewrite H /= => {H}.
      by move=>  /value_uincl_word H/H{H} -> /= h2 -> <- /=;exists (Vword h2) => //; exists erefl.
    - move => op1 e1 He1 [] //= op2 e2 v1.
      move=> /andP[]/eqP <- /He1 H; apply: rbindP => ve1 /H [ve2 ->].
      by move=> /vuincl_sem_sop1 U /U;exists v1.
    - move => op1 e11 He11 e12 He12 [] //= op2 e21 e22 v1.
      move=> /andP[]/andP[]/eqP <- /He11 He1 /He12 He2.
      apply: rbindP => ? /He1 [? -> U1] /=; apply: rbindP => ? /He2 [? -> U2].
      by move=> /(vuincl_sem_sop2 U1 U2); exists v1.
    - move => op1 es1 ih [] //= _ es2 v1 /andP [] /eqP <- rec.
      t_xrbindP => vs ok_vs ok_v1; rewrite -!/(sem_pexprs _ _).
      move: ih => /(_ _ _ rec ok_vs) [] vs' ->.
      exact: (vuincl_sem_opN ok_v1).
    move => t e He e11 He11 e12 He12 [] //= t' e2 e21 e22 v1.
    move=> /andP[]/andP[]/andP[]/eqP? /He{He}He /He11{He11}He11 /He12{He12}He12;subst t'.
    apply: rbindP => b;apply: rbindP => w /He [ve ->] /=.
    move=> /value_uincl_bool H/H [_ ->] /=.
    t_xrbindP => vt2 v2 /He11 [] v2' -> Hv2' ht2 vt3 v3 /He12 [] v3' -> Hv3' ht3 <- /=.
    have [? -> ?]:= truncate_value_uincl Hv2' ht2.
    have [? -> ? /=]:= truncate_value_uincl Hv3' ht3.
    eexists; first reflexivity.
    by case: (b).
  Qed.

  End CHECK_EBP.

  Definition check_ebP gd r m vm1 vm2 e h :=
    (@check_e_esbP gd r m vm1 vm2 h).1 e.

  Lemma check_eP gd e1 e2 r re vm1 vm2 :
    check_e e1 e2 r = ok re ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    forall m v1, sem_pexpr gd (Estate m vm1) e1 = ok v1 ->
    exists v2, sem_pexpr gd (Estate m vm2) e2 = ok v2 /\ value_uincl v1 v2.
  Proof.
    rewrite /check_e; case: ifP => //= h [<-] hr; split => // m v1 ok_v1.
    have [] := check_ebP hr h ok_v1.
    by eauto.
  Qed.

  Lemma eq_alloc_set x1 (v1 v2:exec (psem_t (vtype x1))) r vm1 vm2  :
    ~ Sv.In x1 (M.allocated r) ->
    eq_alloc r vm1 vm2 ->
    eval_uincl v1 v2 ->
    eq_alloc r vm1.[x1 <- apply_undef v1]
               vm2.[x1 <- apply_undef v2].
  Proof.
    move=> Hin [] Hu Hget Huv;split.
    + move=> x Hx; case:( x1 =P x) => [<-|/eqP Hne].
      + by rewrite !Fv.setP_eq;apply eval_uincl_apply_undef.
      by rewrite !Fv.setP_neq //;apply: Hu.
    move=> x n ws id H; have := Hget _ _ _ _ H;have [{H}]:= M.Valid H.
    case:x => //= -[] //= p xn ?? [t [h1 h2]]; exists t.
    by rewrite h2 !Fv.setP_neq //; apply /eqP => H; subst; apply Hin.
  Qed.

  Lemma check_rvarP (x1 x2:var_i) r1 vm1 v1 v2 s1 s1' :
    check_var r1 x1 x2 ->
    eq_alloc r1 (evm s1) vm1 ->
    value_uincl v1 v2 ->
    write_var x1 v1 s1 = ok s1' ->
    exists vm1' : vmap,
      write_var x2 v2 (with_vm s1 vm1) = ok (with_vm s1' vm1') /\
     eq_alloc r1 (evm s1') vm1'.
  Proof.
    move=> /andP[]/eqP Heq /Sv_memP Hin [] Hu Hget Huv.
    rewrite /write_var /=;apply:rbindP => vm1'.
    apply: set_varP => [v1' | ];rewrite -Heq /set_var.
    + move=> /(pof_val_uincl Huv) [v2' [->]] /= Hv' <- [<-] /=.
      eexists; rewrite !with_vm_idem.
      by split; eauto; apply: (@eq_alloc_set x1 (ok v1') (ok v2')).
    move=> {Heq x2}; case: x1 Hin => -[tx1 nx1] ii /= Hin /eqP ?;subst tx1.
    move=> /pof_val_bool_undef ?;subst v1 => <- [<-] /=.
    set x1 := {| vname := nx1 |}.
    have [->|[b ->]] /= := pof_val_undef Huv erefl; eexists;(split;first by reflexivity).
    + by apply (@eq_alloc_set x1 undef_error undef_error).
    by apply (@eq_alloc_set x1 undef_error (ok b)).
  Qed.

  Lemma check_lvalP gd r1 r1' x1 x2 oe2 s1 s1' vm1 v1 v2 :
    check_lval oe2 x1 x2 r1 = ok r1' ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    oapp (fun te2 =>
     sem_pexpr gd (with_vm s1 vm1) te2.2 >>= truncate_val te2.1 = ok v2) true oe2 ->
    write_lval gd x1 v1 s1 = ok s1' ->
    exists vm1',
      write_lval gd x2 v2 (with_vm s1 vm1) = ok (with_vm s1' vm1') /\
      eq_alloc r1' s1'.(evm) vm1'.
  Proof.
    move=> H1 H2 H3 _; move: H1 H2 H3.
    case: x1 x2 => [vi1 t1 | x1 | sw1 x1 e1 | aa1 sw1 x1 e1] [vi2 t2 | x2 | sw2 x2 e2 | aa2 sw2 x2 e2] //=.
    + case:ifP => //= /eqP <- [<-].
      move=> Heqa Hv H; have [-> _]:= write_noneP H.
      by rewrite (uincl_write_none _ Hv H);exists vm1.
    + by case:ifP=>//= Hc [<-];apply check_rvarP.
    + case:ifP=>//= /andP[] /andP[] /eqP <- Hcx Hce [<-] Hea Hu.
      t_xrbindP => z1 vx1  /(check_varP Hea Hcx) [vx1' ->] /=.
      move=> /value_uincl_word H/H{H} -> we ve.
      case: s1 Hea => sm1 svm1 Hea h. 
      have [ve2 ->] := check_ebP Hea Hce h.
      move=> /value_uincl_word H/H{H} /= -> w /(value_uincl_word Hu) -> /=.
      by move=> m -> <- /=;eexists;eauto.
    + by case: aa1 => //.
    + case: aa1 => //.
      case:is_constP => //= i.
      case: x1 x2 => -[tx1 nx1] ii1 [[tx2 nx2] ii2] /=.
      set x1 := {| vname := nx1 |}; set x2 := {|vname := nx2|}.
      case:ifP=>//= /eqP ? [?] heqa huv; subst tx2 r1'.
      apply: on_arr_varP => n t /= ? Hget; subst tx1.
      t_xrbindP=> w /(value_uincl_word huv) H => {huv} t' Ht' vm1' Hset <- /=.
      move: Hget Hset; rewrite /get_var/set_var/=;apply:on_vuP => //=.
      move=> t'' Hget /Varr_inj [] heq.
      rewrite (Eqdep_dec.UIP_dec Pos.eq_dec heq erefl) /= => {heq} ? [?]; subst t'' vm1'.
      rewrite /write_var /set_var /= (to_word_to_pword H) /=.
      eexists;split;first reflexivity.
      rewrite /WArray.inject Z.ltb_irrefl.
      have -> : {| WArray.arr_data := WArray.arr_data t' |} = t' by case: (t').
      case: heqa => Hina Hgeta.
      split.
      + move=> x /= Hx;rewrite !Fv.setP_neq; 
        [by apply Hina;SvD.fsetdec | | ];apply /eqP; SvD.fsetdec. 
      move=> x n0 wz id /M.get_set_arr.
      case: eqP => [? [? hi]| /eqP hnx].
      + subst x wz => /=; rewrite Fv.setP_eq; eexists; split; first reflexivity.
        rewrite (WArray.setP n0 Ht').
        case: eqP hi => [?? | /eqP hni].
        + by subst n0 id; rewrite Fv.setP_eq.
        move=> [hnid] /Hgeta /= [t0]; rewrite Hget => -[[?]]; subst t0.
        by rewrite Fv.setP_neq //; apply /eqP => -[].
      move=> [hnid /Hgeta]; case: x hnx => -[]// px nx /= hnx.
      by rewrite !Fv.setP_neq //; apply /eqP => -[].
    + by case: aa1 => //.
    case:ifP; last by case: aa1.
    move=> /andP[] /andP[] /andP[] /eqP ? /eqP ? Hca Hce h.
    have <- : r1 = r1'.
    + by case: (aa1) h => -[].
    move=> {h} Hea Hvu; subst aa2 sw2.
    apply: on_arr_varP;rewrite /on_arr_var => n t Htx1 /(check_varP Hea Hca) [v3 ->] /=.
    case: v3=> //= n0 t' Ht;subst.
    apply: rbindP => z;apply: rbindP => ve. 
    case: s1 Hea=> sm1 svm1 Hea /(check_ebP Hea Hce) [v3 ->] /value_uincl_int H /H [_ ->].
    apply: rbindP => w /(value_uincl_word Hvu) -> /=.
    apply: rbindP => t'' /(WArray.uincl_set Ht) [t2 [-> ht'']].
    have /(check_rvarP Hca Hea) : value_uincl (Varr t'') (Varr t2) by done.
    by rewrite /write_var /=;case: set_var => //= vm' H1 /H1.
  Qed.

End CBEA.

Module CBEAU := CheckBU CBEA.
Module CheckExpansion :=  MakeCheckAlloc CBEAU.
