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

(*
Definition type_in_array t :=
  match t with
  | sarr ws _ => sword ws
  | _         => sword U64
  end.
*)

Module CBEA.

  Module M.

    (* array_info is a record consisting of array informations *)
    Record array_info := {
      ai_ty    : wsize;
      ai_elems : Ma.t;
    }.

    Definition alloc_t := Mvar.t array_info.

    Definition empty_alloc : alloc_t := Mvar.empty array_info.

    (* get_alloc access the array's information associated with variable x and then gives out 
       the element's information stored at index p in the array *)
    Definition get_alloc (alloc:alloc_t) (x:var) (p:index) :=
      match Mvar.get alloc x with
      | Some ai =>
        match Ma.get ai.(ai_elems) p with
        | Some id => Some (ai.(ai_ty), id)
        | None => None
        end
      | None => None
      end.

    (* valid checks whether the information generated from get_alloc is a valid array information or not *)
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
       ((@WArray.get s wz t n) >>= (fun w => ok (pword_of_word w))) = vm'.[x']
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
    ((x1 == x2) && ~~Sv.mem x1 (M.allocated m), LT_id).

  Section ALL2_MAP.
    Context (A B C: Type) (f: A -> B -> bool * C).
    
    Fixpoint all2_map l1 l2 :=
      match l1, l2 with
      | [::], [::] => (true, [::])
      | x1::l1, x2::l2 =>
        let px := f x1 x2 in
        if px.1 then let pl := all2_map l1 l2 in (pl.1, px.2::pl.2)
        else (false, [::])
      | _, _ => (false, [::])
      end.
  End ALL2_MAP.

  Fixpoint check_eb m (e1 e2:pexpr) : bool * leak_e_tr :=
    match e1, e2 with
    | Pconst   n1, Pconst   n2 => (n1 == n2, LT_remove)
    | Pbool    b1, Pbool    b2 => (b1 == b2, LT_remove)
    | Parr_init n1, Parr_init n2 => (n1 == n2, LT_remove)
    | Pvar     x1, Pvar     x2 => let bl := check_var m x1 x2 in
                                  (bl.1, bl.2)
    | Pglobal g1, Pglobal g2 => (g1 == g2, LT_remove)
    | Pget wz1 x1 e1, Pget wz2 x2 e2 => let bl := check_eb m e1 e2 in
                                        let bl' := check_var m x1 x2 in
                            (((wz1 == wz2) && bl'.1 && bl.1), LT_map [:: bl.2; bl'.2])
    | Pget wz1 x1 e1, Pvar  x2    =>
      match is_const e1 with
      | Some n1 => ((M.get m x1.(v_var) n1 == Some (wz1, vname x2)) && (vtype x2 == sword wz1),
                    LT_remove)
      | _ => (false, LT_remove)
      end
    | Pload sw1 x1 e1, Pload sw2 x2 e2 => let bl := check_eb m e1 e2 in
                                          let bl' := check_var m x1 x2 in 
                             (((sw1 == sw2) && bl'.1 && bl.1), LT_map [:: bl.2 ; bl'.2])
    | Papp1 o1 e1, Papp1 o2 e2 => let bl := check_eb m e1 e2 in
                                  (((o1 == o2) && bl.1), bl.2)
    | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
      let bl := check_eb m e11 e21 in
      let bl' := check_eb m e12 e22 in 
      (((o1 == o2) && bl.1 && bl'.1), LT_map [:: bl.2; bl'.2])
    | PappN o1 es1, PappN o2 es2 =>
      let bl := all2_map (check_eb m) es1 es2 in
      ((o1 == o2) && bl.1, LT_map bl.2)
    | Pif t e e1 e2, Pif t' e' e1' e2' =>
      let bl1 := check_eb m e e' in
      let bl2 := check_eb m e1 e1' in
      let bl3 := check_eb m e2 e2' in 
      ((t == t') && bl1.1 && bl2.1 && bl3.1, LT_map [:: bl1.2; bl2.2; bl3.2])
    | _, _ => (false, LT_remove)
    end.
  
  Definition check_e (e1 e2:pexpr) m :=
    let bl := check_eb m e1 e2 in 
    if bl.1 then cok (m, bl.2) else cerror (Cerr_arr_exp e1 e2).

  Definition check_lval (_:option (stype * pexpr)) (r1 r2:lval) m :=
    match r1, r2 with
    | Lnone _ t1, Lnone _ t2 =>
      if t1 == t2 then cok (m, LT_remove)
      else cerror (Cerr_arr_exp_v r1 r2)
    | Lvar x1, Lvar x2 =>
      let bl := check_var m x1 x2 in
      if bl.1 then cok (m, LT_id)
      else cerror (Cerr_arr_exp_v r1 r2)
    | Lmem sw1 x1 e1, Lmem sw2 x2 e2 =>
      let bl := check_eb m e1 e2 in
      let bl' := check_var m x1 x2 in 
      if (sw1 == sw2) && bl'.1 && bl.1 then cok (m, LT_map [:: bl.2; bl'.2])
      else cerror (Cerr_arr_exp_v r1 r2)
    | Laset sw1 x1 e1, Lvar x2 =>
      match is_const e1 with
      | Some n1 =>
        if vtype x2 == sword sw1 then
          ok ((M.set_arr sw1 x1 n1 (vname x2) m), LT_remove)
        else cerror (Cerr_arr_exp_v r1 r2)
      | None    => cerror (Cerr_arr_exp_v r1 r2)
      end
    | Laset sw1 x1 e1, Laset sw2 x2 e2 =>
      let bl := check_eb m e1 e2 in
      let bl' := check_var m x1 x2 in
      if (sw1 == sw2) && bl'.1 && bl.1 then cok (m, LT_map [:: bl.2; bl'.2])
      else cerror (Cerr_arr_exp_v r1 r2)
    | _, _ => cerror (Cerr_arr_exp_v r1 r2)
    end.

  Lemma check_varP r vm1 vm2 x1 x2 v1 :
    eq_alloc r vm1 vm2 ->
    (check_var r x1 x2).1 ->
    get_var vm1 x1 = ok v1 ->
    exists2 v2, get_var vm2 x2 = ok v2 & value_uincl v1 v2.
  Proof.
    move=> [Hee _] /andP[]/eqP <- /Sv_memP /Hee Hin Hget;move: Hin;rewrite /get_var.
    apply: on_vuP Hget => // z -> ?;subst v1.
    by case: vm2.[x1] => //= a Ha; eauto.
  Qed.

  Section CHECK_EBP.

    Context (gd: glob_decls) (r: M.expansion) (m: mem) (vm1 vm2: vmap)
            (Hrn: eq_alloc r vm1 vm2).
    
    Variable stk : pointer.

    Let P e1 : Prop :=
      ∀ e2 v1 l,
        (check_eb r e1 e2).1 →
        sem_pexpr gd {| emem := m ; evm := vm1 |} e1 = ok (v1, l) →
        exists2 v2, sem_pexpr gd {| emem := m ; evm := vm2 |} e2 =
                    ok (v2, leak_E  stk (check_eb r e1 e2).2 l)
                    & value_uincl v1 v2.

    Let Q es1 : Prop :=
      ∀ es2 vs1,
        (all2_map  (check_eb r) es1 es2).1 ->
        sem_pexprs gd {| emem := m ; evm := vm1 |} es1 = ok vs1 →
        exists vs2, sem_pexprs gd {| emem := m ; evm := vm2 |} es2 = ok vs2 /\
                    List.Forall2 value_uincl (unzip1 vs1) (unzip1 vs2) /\
                    LSub (unzip2 vs2) = leak_E stk (LT_map (all2_map (check_eb r) es1 es2).2) (LSub (unzip2 vs1)).
    
    Lemma check_e_esbP : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; subst P Q; split => /=.
      - (* Base case *)
        move=> [] //. move=> vs1 ht [] <- /=. exists [::].
        rewrite /sem_pexprs //=. 
      - move=> e rec es ih [] //.
        move=> e' es' vs1. case: ifP=> //.
        move=> he hall. t_xrbindP.
        move=> [v le] ok_v vs ok_vs <- /=.
        move: (rec e' v le he ok_v). move=> [] v' -> /= hv.
        move: (ih es' vs hall ok_vs). move=> [] vs' [] -> /= [] hvs hls.
        exists ((v', leak_E stk (check_eb r e e').2 le) :: vs'). split=> //.
        split. apply List.Forall2_cons; eauto. rewrite /=. case: hls => hls1.
        by rewrite -hls1 /=.
      - (* Pconst *)
        move=> z [] // z1 v1 l /eqP <- [] <- <-. exists z. rewrite /=.
        auto. auto.
      - (* Pbool *)
        move=> b [] //= b0 v l /eqP <- [] <- hl. exists b; auto.
      - (* Parr_init *)
        move=> n [] //= p v l /eqP <- [] <- hl. exists (Varr (WArray.empty n)).
        auto. auto.
      - (* Pvar *)
        move=> x [] //= x' v l /check_varP Hg. t_xrbindP. move=> v' Hg' <- <-.
        move: (Hg vm1 vm2 v' Hrn Hg'). move=> [] v'' {Hg'} Hg' Hv. rewrite Hg' /=.
        by exists v''.
      - (* Pglobal *)
        move=> g [] //= g' v l /eqP <-. t_xrbindP. move=> v' -> /= <- hl.
        by exists v'. 
      - (* Pget *)
        move => sz1 [[ty1 x1] ii1] e1 ih1 [] //.
        + move=> [[ty2 x2] ii2] v1 l.
          case: is_constP => //= ze /andP [] /eqP hget /eqP ?;subst ty2.
          apply: on_arr_varP => n t Htx1.
          rewrite /get_var /=; apply: on_vuP => //= x1t.
          have [_ /(_ _ _ _ _ hget) {hget}] := Hrn.
          case: ty1 Htx1 x1t => //= n' hle x1t [x1t' [->]].
          move=> h [] ? /Varr_inj [en];subst n' x1t' => /= ?; subst x1t.
          t_xrbindP => w hg ?;subst v1.
          (move: h;rewrite hg /= => <- /=; eexists; first reflexivity) => /=.
          by apply word_uincl_refl.
        move=> ws v p v1 l /andP[] /andP[] /eqP ?;subst ws.
        move=> /(check_varP Hrn) /= hget /ih1 hrec {ih1}.
        apply: on_arr_varP => n t /= Htx1 /hget [v2 hget2 hincl].
        t_xrbindP. move=> [ve le] /hrec [v4 -> hv3].
        move=> vi /(value_uincl_int hv3) [h1 h2]; subst ve v4.
        rewrite /on_arr_var hget2 /= => w1.
        have [n' [t' ? hu]]:= value_uinclE hincl;subst v2.
        move=> /(WArray.uincl_get hu) -> <- <- /=. exists (Vword w1).
        auto. by apply word_uincl_refl.
      - (* Pload *)
        move=> sz x e He [] // sz1 x1 e1 v1 l.
        move=> /andP [] /andP [] /eqP Hsz Hcv Hce. t_xrbindP.
        move=> v1' v2' Hg /value_uincl_word Hp [ve le] He' v2 /value_uincl_word Hp' v3 Hr <- <- /=.
        move: (He e1 ve le Hce He'). move=> [] ve'' He'' Hv {He}.
        move: check_varP. move=> Hcv'. move: (Hcv' r vm1 vm2 x x1 v2' Hrn Hcv Hg).
        move=> [] v4 -> /= Hv' {Hcv'}. move: (Hp v4 Hv'). move=> -> /=. rewrite He'' /=.
        move: (Hp' ve'' Hv). move=> -> /=.  rewrite -Hsz. rewrite Hr /=.
        exists (Vword v3). rewrite /=. auto. auto.
      - (* Papp1 *)
        move=> op e He [] // op1 e2 v1 l /=.
        move=> /andP [] /eqP <- /= Hce. t_xrbindP.
        move=> [ve le] He' vo Ho <- <-. move: (He e2 ve le Hce He'). move=> {He} [] ve' -> /= Hv.

        move: vuincl_sem_sop1. move=> Ho'. move: (Ho' op ve ve' vo Hv Ho). move=> -> /=.
        by exists vo.
      - (* Papp2 *)
        move=> op e1 He1 e2 He2 [] //= op1 e1' e2' v1 l.
        move=> /andP [] /andP [] /eqP <- Hce1 Hce2. t_xrbindP.
        move=> [ve le] He [ve' le'] He' vo Ho <- <- /=.
        move: (He1 e1' ve le Hce1 He). move=> [] ve'' -> Hv.
        move: (He2 e2' ve' le' Hce2 He'). move=> [] ve''' ->  Hv' /=.
        move: vuincl_sem_sop2. move=> H. move: (H op ve ve'' ve' ve''' vo Hv Hv' Ho).
        move=> -> /=. by exists vo.
      - (* PappN *)
        move=> op1 es1 ih [] //= o es2 v1 l /andP [] /eqP <- rec.
        t_xrbindP. move=> vs ok_vs v' ok_v1 <- <- /=. rewrite /sem_pexprs in ih.
        move: (ih es2 vs rec ok_vs). move=> [] vs' [] -> /= [] hvs hls.
        move: (vuincl_sem_opN). move=> Ho. move: (Ho op1 (unzip1 vs) v' (unzip1 vs') ok_v1 hvs).
        move=> [] v'' -> /= hv'. case: hls=> hls1. exists v''.
        by rewrite hls1 /=. auto.
      (* Pif *)
      move=> t e He e1 He1 e2 He2 [] //= t' e' e1' e2' v1 l.
      move=> /andP [] /andP [] /andP [] /eqP <- Hce Hce1 Hce2.
      t_xrbindP. move=> [ve le] He' b Hb [ve1 le1] He1' [ve2 le2] He2'.
      move=> vt Ht vt' Ht' <- <- /=. move: (He e' ve le Hce He'). move=> [] ve' -> /= Hve.
      move: value_uincl_bool. move=> Hb'. move: (Hb' ve ve' b Hve Hb). move=> [] h1 h2.
      rewrite h1 in Hb. rewrite -h2 in Hb. rewrite Hb /=.
      move: (He1 e1' ve1 le1 Hce1 He1').
      move=> [] ve1' -> /= Hve1. move: (He2 e2' ve2 le2 Hce2 He2').
      move=> [] ve2' -> /= Hve2. move: truncate_value_uincl. move=> Htt.
      move: (Htt t ve1 ve1' vt Hve1 Ht). move=> {Htt} [] vt'' -> /= Htv.
      move: truncate_value_uincl. move=> Htt.
      move: (Htt t ve2 ve2' vt' Hve2 Ht'). move=> {Htt} [] vt''' -> /= Htv' /=.
      case: (b). by exists vt''. by exists vt'''.
     Qed.

  End CHECK_EBP.

  Definition check_ebP gd r m vm1 vm2 e h stk:=
    (@check_e_esbP gd r m vm1 vm2 h stk).1 e.

  Lemma check_eP gd e1 e2 r re lte vm1 vm2 stk:
    check_e e1 e2 r = ok (re, lte) ->
    eq_alloc r vm1 vm2 ->
    eq_alloc re vm1 vm2 /\
    forall m v1 l,  sem_pexpr gd (Estate m vm1) e1 = ok (v1, l) ->
    exists v2, sem_pexpr gd (Estate m vm2) e2 = ok (v2, leak_E stk lte l) /\ value_uincl v1 v2.
  Proof.
    rewrite /check_e; case: ifP => //= h [<-] hr; split => // m v1 l1 ok_v1.
    move: check_ebP. move=> Hce. move: (Hce gd r m vm1 vm2 e1 H stk e2 v1 l1 h ok_v1).
    move=> [] v2 He Hv. exists v2. split. by rewrite -hr. auto.
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
    (check_var r1 x1 x2).1 ->
    eq_alloc r1 (evm s1) vm1 ->
    value_uincl v1 v2 ->
    write_var x1 v1 s1 = ok s1' ->
    exists vm1' : vmap,
      write_var x2 v2 {| emem := emem s1; evm := vm1 |} =
         ok {| emem := emem s1'; evm := vm1' |} /\
     eq_alloc r1 (evm s1') vm1'.
  Proof.
    move=> /andP[]/eqP Heq /Sv_memP Hin [] Hu Hget Huv.
    rewrite /write_var /=;apply:rbindP => vm1'.
    apply: set_varP => [v1' | ];rewrite -Heq /set_var.
    + move=> /(pof_val_uincl Huv) [v2' [->]] /= Hv' <- [<-] /=.
      by eexists;split;eauto; apply: (@eq_alloc_set x1 (ok v1') (ok v2')).
    move=> {Heq x2}; case: x1 Hin => -[tx1 nx1] ii /= Hin /eqP ?;subst tx1.
    move=> /pof_val_bool_undef ?;subst v1 => <- [<-] /=.
    set x1 := {| vname := nx1 |}.
    have [->|[b ->]] /= := pof_val_undef Huv erefl; eexists;(split;first by reflexivity).
    + by apply (@eq_alloc_set x1 undef_error undef_error).
    by apply (@eq_alloc_set x1 undef_error (ok b)).
  Qed.

  Lemma check_lvalP gd r1 r1' ltr x1 x2 e2 s1 s1' le1' vm1 v1 v2 stk:
    check_lval e2 x1 x2 r1 = ok (r1', ltr) ->
    eq_alloc r1 s1.(evm) vm1 ->
    value_uincl v1 v2 ->
    oapp (fun te2 =>
            Let vl := sem_pexpr gd (Estate s1.(emem) vm1) te2.2 in
            truncate_val te2.1 vl.1 = ok v2) true e2 ->
    write_lval gd x1 v1 s1 = ok (s1', le1') ->
    exists vm1',
      write_lval gd x2 v2 (Estate s1.(emem) vm1) = ok (Estate s1'.(emem) vm1', leak_E stk ltr le1') /\
      eq_alloc r1' s1'.(evm) vm1'.
  Proof.
    move=> H1 H2 H3 _; move: H1 H2 H3.
    case: x1 x2 => [vi1 t1 | x1 | sw1 x1 e1 | sw1 x1 e1] [vi2 t2 | x2 | sw2 x2 e2' | sw2 x2 e2'] //=.
    + (* Lone *)
      case:ifP => //= /eqP <- [<-] <-.
      move=> Heqa Hv. t_xrbindP. move=> vw H <- <-.
      have [-> _]:= write_noneP H.
      rewrite (uincl_write_none _ Hv H) /=. by exists vm1.
    + (* Lvar *)
      case:ifP=> //= Hc [<- <-] Hvm Hv. t_xrbindP. move=> vw Hw <- <-.
      move: check_rvarP. move=> Hcv. move: (Hcv x1 x2 r1 vm1 v1 v2 s1 vw Hc Hvm Hv Hw).
      move=> [] vm1' [] -> Hvm1' /=. exists vm1'. by split.
    + (* Lmem *)
      case: ifP=> //=. move=> /andP [] /andP [] /eqP <- Hcx Hce [] <- <- Hvm Hv.
      t_xrbindP. move=> vg vp Hg /value_uincl_word Hp [ve le] He
                        vp' /value_uincl_word Hp' vw /value_uincl_word Hw vw' Hw' <- <-.
      move: check_varP. move=> Hcc. move: (Hcc r1 (evm s1) vm1 x1 x2 vp Hvm Hcx Hg).
      move=> [] vp'' -> /= Hv' {Hcc}. move: (Hp vp'' Hv' ). move=> -> /=.
      move: check_ebP.  move=> Hce'. replace s1 with {| emem := emem s1; evm := evm s1 |} in He.
      move: (Hce' gd r1 (emem s1) (evm s1) vm1 e1 Hvm stk e2' ve le Hce He).
      move=> [] ve' -> {Hce'} /= Hve. move: (Hp' ve' Hve). move=> -> /=.
      move: (Hw v2 Hv). move=> -> /=. rewrite Hw' /=. exists vm1. split. auto. auto.
      case: (s1). by rewrite /=.
    + (* Laset *)
      case: is_constP=> //= i.
      case: x1 x2=> -[tx1 nx1] ii1 [[tx2 nx2] ii2] /=.
      set x1 := {| vname := nx1 |}; set x2 := {|vname := nx2|}.
      case:ifP=>//= /eqP hws [h1 h2] heqa huv; subst tx2 r1' ltr.
      apply: on_arr_varP => n t /subtypeEl [n' /= [? hnn']] Hget; subst tx1.
      t_xrbindP=> w /(value_uincl_word huv) H => {huv} t' Ht' vm1' Hset <- hl /=.
      move: Hget Hset; rewrite /get_var/set_var/=;apply:on_vuP => //=.
      move=> t'' Hget /Varr_inj [?]; subst n' => /= ? [?]; subst t'' vm1'.
      rewrite /write_var /set_var /= (to_word_to_pword H) /=.
      eexists;split; auto.
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
    (* Laset *)
    case:ifP=>//=/andP[] /andP[] /eqP ? Hca Hce [<- <-] Hea Hvu; subst sw2.
    apply: on_arr_varP;rewrite /on_arr_var => n t Htx1 /(check_varP Hea Hca) [v3 ->] /=.
    case: v3=> //= n0 t' Ht;subst. t_xrbindP.
    move=> [ve le] He vi Hi vw /value_uincl_word Hw t''
           /(WArray.uincl_set Ht) [] va [] Ha Ht' vs Hs <- <-.
    replace s1 with {| emem := emem s1; evm := evm s1 |} in He. move: check_ebP.
    move=> Hce'. move: (Hce' gd r1 (emem s1) (evm s1) vm1 e1 Hea stk e2' ve le Hce He).
    move=> {Hce'} [] ve' -> /= Hv. move: value_uincl_int. move=> Hi'. move: (Hi' ve ve' vi Hv Hi).
    move=> {Hi'} [] h1 h2. rewrite h1 in Hi. rewrite -h2 in Hi. rewrite Hi /=.
    move: (Hw v2 Hvu). move=> -> /=. rewrite Ha /=.
    move: check_rvarP. move=> Hcv. rewrite /write_var in Hcv.
    have /(check_rvarP Hca Hea) : value_uincl (Varr t'') (Varr va) by done.
    rewrite /write_var /=. move=> H. move: (H {| emem := emem s1; evm := vs |}).
    rewrite Hs /=. move=> []. auto. move=> vs' []. t_xrbindP. move=> vs'' -> /= <- Hvm1.
    exists vs''. by split. by case: (s1).
   Qed.


End CBEA.

Module CheckExpansion :=  MakeCheckAlloc CBEA.
