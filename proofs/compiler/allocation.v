(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
From mathcomp Require Import word_ssrZ.
Require Import expr compiler_util ZArith.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module E.

Definition pass_name := "allocation"%string.

(* FIXME: are there internal errors? *)
Definition gen_error (internal:bool) (ii:option instr_info) (msg:string) := 
  {| pel_msg      := pp_s msg
   ; pel_fn       := None
   ; pel_fi       := None
   ; pel_ii       := ii
   ; pel_vi       := None
   ; pel_pass     := Some pass_name
   ; pel_internal := internal
  |}.

Definition error msg := gen_error true None msg.

Definition loop_iterator := loop_iterator pass_name.

Definition fold2 := error "fold2".

End E.

Module M.

  Module Mv.

  Definition oget (mid: Mvar.t Sv.t) id := odflt Sv.empty (Mvar.get mid id).

  Definition valid (mvar: Mvar.t var) (mid: Mvar.t Sv.t) :=
    forall x id, Mvar.get mvar x = Some id <-> Sv.In x (oget mid id).

  Record t_ := mkT { mvar : Mvar.t var; mid : Mvar.t Sv.t; mvalid : valid mvar mid }.
  Definition t := t_.

  Definition get (m:t) (x:var) := Mvar.get (mvar m) x.

  Definition rm_id (m:t) id :=
     Sv.fold (fun x m => Mvar.remove m x) (oget (mid m) id) (mvar m).

  Definition ms_upd (m:Mvar.t Sv.t) (f:Sv.t -> Sv.t) id :=
    Mvar.set m id (f (oget m id)).

  Definition rm_x (m:t) x :=
    match Mvar.get (mvar m) x with
    | Some id => ms_upd (mid m) (Sv.remove x) id
    | None    => (mid m)
    end.

  Lemma valid_get_in m id x :
    get m x = Some id -> x \in Sv.elements (oget (mid m) id).
  Proof. by move=> /(mvalid) /Sv_elemsP. Qed.

  Lemma rm_idP m id x :
     Mvar.get (rm_id m id) x =
      if Sv.mem x (oget (mid m) id) then None
      else get m x.
  Proof.
    rewrite /rm_id; have := @valid_get_in m id.
    rewrite Sv.fold_spec /get Sv_elems_eq.
    elim: (Sv.elements _) (mvar m) => //= v vs Hrec mv Hget.
    rewrite Hrec ?inE.
    + rewrite Mvar.removeP eq_sym.
      by case: ( _ \in _);[rewrite orbT | case: (_ == _)].
    by move=> z;rewrite Mvar.removeP;case:ifP => //= H /Hget;rewrite inE eq_sym H.
  Qed.

  Lemma rm_id_eq m id x : Mvar.get (rm_id m id) x <> Some id.
  Proof.
    by rewrite rm_idP;case:ifPn => // /negP; rewrite mvalid => H /Sv_memP -/H.
  Qed.

  Lemma rm_idP_neq m x id id' : id != id' ->
    Mvar.get (rm_id m id) x = Some id' <-> Mvar.get (mvar m) x = Some id'.
  Proof.
    rewrite rm_idP => Hneq.
    case:ifP => //= /Sv_memP Hin;split=>// Hg.
    by move: Hin Hg Hneq; rewrite -mvalid => -> [->];rewrite eq_refl.
  Qed.

  Lemma oget_set m id id' s:
    oget (Mvar.set m id' s) id =
     if id' == id then s else oget m id.
  Proof. by rewrite /oget Mvar.setP;case:ifP. Qed.

  Lemma oget_rm m id id':
    oget (Mvar.remove m id') id =
     if id' == id then Sv.empty else oget m id.
  Proof. by rewrite /oget Mvar.removeP;case:ifP. Qed.

  Lemma rm_xP m x id : Sv.Equal (oget (rm_x m x) id) (Sv.remove x (oget (mid m) id)).
  Proof.
    rewrite /rm_x;case Heq: (Mvar.get (mvar m) x) => [id'|];last first.
    + case: (SvP.MP.In_dec x (oget (mid m) id));last by SvD.fsetdec.
      by rewrite -mvalid Heq.
    rewrite /ms_upd oget_set;case:ifPn => [/eqP -> //| /eqP].
    case: (SvP.MP.In_dec x (oget (mid m) id));last by SvD.fsetdec.
    by rewrite -mvalid Heq => -[->].
  Qed.

  Lemma valid_rm m id : valid (rm_id m id) (Mvar.remove (mid m) id).
  Proof.
    move=> x id';rewrite oget_rm;case:ifPn => [/eqP <- | Hne].
    + by split => [/rm_id_eq | ] //;SvD.fsetdec.
    by rewrite rm_idP_neq // mvalid.
  Qed.

  Definition remove m id := @mkT (rm_id m id) (Mvar.remove (mid m) id) (valid_rm m id).

  Lemma removeP m id x' :
    get (remove m id) x' =
      match get m x' with
      | Some id' => if id == id' then None else Some id'
      | None     => None
      end.
  Proof.
    rewrite /remove /get /= rm_idP /get; case: ifPn.
    + by move=> /Sv_memP;rewrite -mvalid => ->;rewrite eq_refl.
    move=> /Sv_memP;case Hg: Mvar.get => [id'|]//=;case:ifP => //= /eqP ?;subst id'.
    by move:Hg; rewrite mvalid => H /(_ H).
  Qed.

  Lemma valid_set m x id :
    valid (Mvar.set (rm_id m id) x id) (Mvar.set (rm_x m x) id (Sv.singleton x)).
  Proof.
    move=> y idy;rewrite Mvar.setP;case:eqP => [<- | Hne].
    + rewrite oget_set;case:eqP => [<- | Hne'];first by split => //;SvD.fsetdec.
      by rewrite rm_xP;split => [[]/Hne' | ] //;SvD.fsetdec.
    rewrite rm_idP oget_set;case:eqP => [<-| Hne'].
    + split;last by SvD.fsetdec.
      by case:ifPn => // /Sv_memP;rewrite -mvalid => H /H.
    rewrite rm_xP;case: ifPn => /Sv_memP H;split => // H1.
    + by move: H1 H Hne'=> /SvD.F.remove_3;rewrite -!mvalid => -> [->].
    + by move:H1;rewrite mvalid;SvD.fsetdec.
    by move: H1 => /SvD.F.remove_3;rewrite mvalid.
  Qed.

  Definition set m x id := mkT (valid_set m x id).

  Lemma valid_add m x id :
    valid (Mvar.set (mvar m) x id) (ms_upd (rm_x m x) (fun s => Sv.add x s) id).
  Proof.
    move=> y idy;rewrite Mvar.setP;case:eqP => Hxy.
    + subst y; rewrite /ms_upd;rewrite oget_set;split => [ [<-]| ].
      + by rewrite eq_refl;SvD.fsetdec.
      by case:eqP => [<- //| ?];rewrite rm_xP;SvD.fsetdec.
    by rewrite /ms_upd oget_set mvalid;case:eqP => [<- | ]; rewrite rm_xP;SvD.fsetdec.
  Qed.

  Definition add m x id := mkT (valid_add m x id).

  Lemma valid_empty : valid (@Mvar.empty _) (@Mvar.empty _).
  Proof. move=> x id;rewrite Mvar.get0 /oget Mvar.get0;split => //=;SvD.fsetdec. Qed.

  Definition empty := mkT valid_empty.

  End Mv.

  Definition bool_dec (b:bool) : {b} + {~~b} :=
    if b as b0 return ({b0} + {~~ b0}) then left (erefl true)
    else right (erefl true).

  Section WSW.
  Context {wsw : WithSubWord}.

  Definition v_compat_type x y := compat_type sw_allowed (vtype x) (vtype y).

  Definition v_compat_typeP x y := bool_dec (v_compat_type x y).

  Definition mset_valid (mvar: Mvar.t var) (mset:Sv.t) :=
    forall x id, Mvar.get mvar x = Some id -> Sv.In x mset /\ v_compat_type x id.

  Record t_ := mkT {
    mv : Mv.t;
    mset : Sv.t;
    svalid: mset_valid (Mv.mvar mv) mset;
  }.

  Definition t := t_.

  Definition get (m:t) (x:var) := Mv.get (mv m) x.

  Lemma mset_valid_set m x id :
    v_compat_type x id ->
    mset_valid (Mv.mvar (Mv.set (mv m) x id)) (Sv.add x (mset m)).
  Proof.
    move=> hsub y idy;rewrite Mvar.setP;case: eqP => ?.
    + move=> [?];subst; split=> //; SvD.fsetdec.
    by rewrite Mv.rm_idP;case:ifPn => //_ /svalid [??];split => //;SvD.fsetdec.
  Qed.

  Definition set m x id h := mkT (@mset_valid_set m x id h).
  Arguments set m x id h : clear implicits.

  Lemma mset_valid_add m x id :
    v_compat_type x id ->
    mset_valid (Mv.mvar (Mv.add (mv m) x id)) (Sv.add x (mset m)).
  Proof.
    move=> h y idy;rewrite Mvar.setP;case: eqP => ?.
    + by move=> [?];subst; split=> //;SvD.fsetdec.
    by move=> /svalid [??];split=> //;SvD.fsetdec.
  Qed.

  Definition add m x id h := mkT (@mset_valid_add m x id h).
  Arguments add m x id h : clear implicits.

  Definition addc m x id :=
    if v_compat_typeP x id is left h then add m x id h
    else m.

  Lemma mset_valid_empty s : mset_valid (Mv.mvar Mv.empty) s.
  Proof. by move=> x id;rewrite Mvar.get0. Qed.

  Definition empty_s s := mkT (mset_valid_empty s).

  Definition empty := empty_s Sv.empty.

  Definition merge_aux m1 m2 :=
    Mvar.map2 (fun x ox ox' =>
      match ox, ox' with
      | Some idx, Some idx' => if idx == idx' then Some idx else None
      | Some idx, None      => if ~~(Sv.mem x (mset m2)) then Some idx else None
      | None, Some idx      => if ~~(Sv.mem x (mset m1)) then Some idx else None
      | None, None          => None
      end) (Mv.mvar m1.(mv)) (Mv.mvar m2.(mv)).

  Definition merge m1 m2 :=
    let mv := merge_aux m1 m2 in
    Mvar.fold (fun x idx m => addc m x idx) mv (empty_s (Sv.union (mset m1) (mset m2))).

  Lemma mset_valid_rm m id : mset_valid (Mv.mvar (Mv.remove (mv m) id)) (mset m).
  Proof.
    move=> y idy.
    have := Mv.removeP (mv m) id y.
    rewrite /Mv.get => ->.
    case: Mvar.get (@svalid m y) => [id'|] //.
    by move=> /(_ _ (refl_equal _));case:eqP => // ?? [<-].
  Qed.

  Definition remove m id :=  mkT (@mset_valid_rm m id).

  Lemma get0_s x s: get (empty_s s) x = None.
  Proof. apply Mvar.get0. Qed.

  Lemma setP m x id y h :
    get (set m x id h) y =
      if x == y then Some id
      else if Sv.mem y (Mv.oget (Mv.mid (mv m)) id) then None
      else get m y.
  Proof. by rewrite /get/set /Mv.get/Mv.set /= Mvar.setP Mv.rm_idP. Qed.

  Lemma setP_mset m x id h : mset (set m x id h) = Sv.add x (mset m).
  Proof. by []. Qed.

  Lemma addP m x id y h :
    get (add m x id h) y = if x == y then Some id else get m y.
  Proof. by rewrite /get/add /Mv.get/Mv.add /= Mvar.setP. Qed.

  Lemma addP_mset m x id h : mset (add m x id h) = Sv.add x (mset m).
  Proof. by []. Qed.

  Lemma addcP m x id y :
    get (addc m x id) y =
     if v_compat_type x id && (x == y) then Some id else get m y.
  Proof.
    rewrite /addc;case: v_compat_typeP => [ heq | /negbTE -> //].
    by rewrite heq addP.
  Qed.

  Lemma merge_auxP m1 m2 x id :
    Mvar.get (merge_aux m1 m2) x = Some id ->
      get m1 x = Some id /\ get m2 x = Some id \/
      get m1 x = Some id /\ ~Sv.In x (mset m2) \/
      get m2 x = Some id /\ ~Sv.In x (mset m1).
  Proof.
    rewrite /merge_aux Mvar.map2P //.
    rewrite /get /Mv.get;case: Mvar.get => [id1 |];case: Mvar.get => [id2 |];
      last by tauto.
    + case:ifPn => // /eqP ->;tauto.
    + case:ifPn => // /Sv_memP;tauto.
    case:ifPn => // /Sv_memP;tauto.
  Qed.

  Lemma mergeP m1 m2 x id :
    get (merge m1 m2) x = Some id ->
      get m1 x = Some id /\ get m2 x = Some id \/
      get m1 x = Some id /\ ~Sv.In x (mset m2) \/
      get m2 x = Some id /\ ~Sv.In x (mset m1).
  Proof.
    rewrite /merge Mvar.foldP. set f := (f in foldl f).
    pose P := fun m =>
      get m x = Some id ->
       get m1 x = Some id /\ get m2 x = Some id \/
       get m1 x = Some id /\ ~Sv.In x (mset m2) \/
       get m2 x = Some id /\ ~Sv.In x (mset m1).
    have H : forall (l:list (var * var)) m,
      (forall p, p \in l -> Mvar.get (merge_aux m1 m2) p.1 = Some p.2) ->
      P m -> P (foldl f m l).
    + elim=> [|p l Hrec] //= m Hl Hm;apply Hrec.
      + by move=> ? H;apply Hl;rewrite in_cons H orbC.
      rewrite /f /P.
      have /Hl -/merge_auxP Hp := mem_head p l.
      have : v_compat_type p.1 p.2.
      + have : get m1 p.1 = Some p.2 \/ get m2 p.1 = Some p.2 by intuition.
        by move=> [] /svalid [].
      by rewrite addcP => ->; case:eqP => [<- [<-] //| ne ];apply Hm.
    apply H;first by move=> p /Mvar.elementsP.
    by rewrite /P get0_s.
  Qed.

  Lemma mergeP_mset m1 m2 : Sv.Subset (Sv.union (mset m1) (mset m2)) (mset (merge m1 m2)).
  Proof.
    rewrite /merge Mvar.foldP. set f := (f in foldl f).
    pose P := fun m => Sv.Subset (Sv.union (mset m1) (mset m2)) (mset m).
    have : P (empty_s (Sv.union (mset m1) (mset m2))).
    + by rewrite /P /empty_s.
    have :
      (forall p, p \in Mvar.elements (merge_aux m1 m2) -> v_compat_type p.1 p.2).
    + move=> p /Mvar.elementsP -/merge_auxP ?.
      have : get m1 p.1 = Some p.2 \/ get m2 p.1 = Some p.2 by intuition.
      by move=> [] /svalid [].
    elim : Mvar.elements (empty_s _) => //= -[x idx] l Hl m Hp Hm.
    apply Hl;first by move=> p hin;apply Hp;rewrite in_cons hin orbT.
    move:Hm;rewrite /f /P /addc /=.
    case: v_compat_typeP => [? | ].
    + rewrite addP_mset;SvD.fsetdec.
    by have /= -> := Hp _ (mem_head (x, idx) l).
  Qed.

  Lemma removeP m id x :
    get (remove m id) x =
      match get m x with
      | Some id' => if id == id' then None else Some id'
      | None     => None
      end.
  Proof. apply Mv.removeP. Qed.

  Definition incl m1 m2 :=
    Sv.subset (mset m2) (mset m1) &&
    let mv1 := Mv.mvar m1.(mv) in
    let mv2 := Mv.mvar m2.(mv) in
    Sv.for_all (fun x =>
       match Mvar.get mv1 x with
       | Some idx => Mvar.get mv2 x == Some idx
       | None     => true
       end) (mset m2).

  Lemma inclP m1 m2 :
    reflect ((forall x id, Sv.In x (mset m2) -> get m1 x = Some id -> get m2 x = Some id) /\
             Sv.Subset (mset m2) (mset m1))
            (incl m1 m2).
  Proof.
    rewrite /incl andbC; apply (equivP andP).
    match goal with |- (is_true ?A /\ _) <-> (?B /\ _) => have : reflect B A end.
    + apply: (equivP idP).
      rewrite /is_true -SvD.F.for_all_iff;split => [ H x id| H x] /H;
        rewrite /get /Mv.get.
      + by move=> H1 H2;move: H1; rewrite H2 => /eqP.
      by case: Mvar.get => // idx /(_ _ (refl_equal _)) /eqP.
    by move=> /rwP ->;rewrite SvD.F.subset_iff.
  Qed.

  Lemma incl_refl r : incl r r.
  Proof. by apply/inclP;split. Qed.

  Lemma incl_trans r2 r1 r3 : incl r1 r2 -> incl r2 r3 -> incl r1 r3.
  Proof.
    move=> /inclP [H1 H3] /inclP [H2 H4];apply/inclP;split;last by SvD.fsetdec.
    by move=> x id Hin Hget;apply H2 => //;apply H1 => //;SvD.fsetdec.
  Qed.

  Lemma merge_incl_l r1 r2 : incl (merge r1 r2) r1.
  Proof.
    apply/inclP;split;first by move=> x idx Hin /mergeP;tauto.
    by have := @mergeP_mset r1 r2;SvD.fsetdec.
  Qed.

  Lemma merge_incl_r r1 r2 : incl (merge r1 r2) r2.
  Proof.
    apply/inclP;split;first by move=> x idx Hin /mergeP;tauto.
    by have := @mergeP_mset r1 r2;SvD.fsetdec.
  Qed.

  End WSW.
  Arguments add {wsw} m x id h.
  Arguments set {wsw} m x id h.

End M.

Section WSW.
Context {wsw : WithSubWord}.

Definition alloc_error := pp_internal_error_s "allocation".

Definition cerr_varalloc xi1 xi2 s:=
  pp_internal_error "Variable allocation" (pp_box [:: pp_var xi1; pp_s "and"; pp_var xi2; pp_s ":"; pp_s s]).

Definition check_v xi1 xi2 (m:M.t) : cexec M.t :=
  let x1 := xi1.(v_var) in
  let x2 := xi2.(v_var) in
  if M.v_compat_typeP x1 x2 is left h then
    match M.get m x1 with
    | None     =>
      Let _ := assert (~~Sv.mem x1 (M.mset m)) (cerr_varalloc xi1 xi2 "variable already set") in
      ok (M.set m x1 x2 h)
    | Some x2' =>
      Let _ := assert (x2 == x2') (cerr_varalloc xi1 xi2 "variable mismatch") in ok m
    end
  else Error (cerr_varalloc xi1 xi2 "type mismatch").

Definition error_e := pp_internal_error_s "allocation" "expression are not equal".

Definition check_gv x1 x2 (m:M.t) : cexec M.t :=
  Let _ := assert (x1.(gs) == x2.(gs)) error_e in
  if is_lvar x1 then check_v x1.(gv) x2.(gv) m
  else
    Let _ := assert (x1.(gv).(v_var) == x2.(gv).(v_var)) error_e in ok m.

Fixpoint check_e (e1 e2:pexpr) (m:M.t) : cexec M.t :=
  match e1, e2 with
  | Pconst n1, Pconst n2 =>
    Let _ := assert (n1 == n2) error_e in ok m
  | Pbool  b1, Pbool  b2 =>
    Let _ := assert (b1 == b2) error_e in ok m
  | Parr_init n1, Parr_init n2 =>
    Let _  := assert (n1 == n2) error_e in ok m
  | Pvar   x1, Pvar   x2 => check_gv x1 x2 m
  | Pget al1 aa1 w1 x1 e1, Pget al2 aa2 w2 x2 e2 =>
    Let _ := assert ((al1 == al2) && (aa1 == aa2) && (w1 == w2)) error_e in
    check_gv x1 x2 m >>= check_e e1 e2
  | Psub aa1 w1 len1 x1 e1, Psub aa2 w2 len2 x2 e2 =>
    Let _ := assert ([&& aa1 == aa2, w1 == w2 & len1 == len2]) error_e in
    check_gv x1 x2 m >>= check_e e1 e2
  | Pload al1 w1 x1 e1, Pload al2 w2 x2 e2 =>
    Let _ := assert ((al1 == al2) && (w1 == w2)) error_e in
    check_v x1 x2 m >>= check_e e1 e2
  | Papp1 o1 e1, Papp1 o2 e2 =>
    Let _ := assert (o1 == o2) error_e in check_e e1 e2 m
   | Papp2 o1 e11 e12, Papp2 o2 e21 e22 =>
    Let _ := assert (o1 == o2) error_e in check_e e11 e21 m >>= check_e e12 e22
  | PappN o1 es1, PappN o2 es2 =>
    Let _ := assert (o1 == o2) error_e in
    fold2 (alloc_error "check_e (appN)") check_e es1 es2 m
  | Pif t e e1 e2, Pif t' e' e1' e2' =>
    Let _ := assert (t == t') error_e in
    check_e e e' m >>= check_e e1 e1' >>= check_e e2 e2'
  | _, _ => Error error_e
  end.

Definition check_var_aux (x1 x2:var) m (h:M.v_compat_type x1 x2): cexec M.t :=
  ok (M.set m x1 x2 h).

Definition check_varc (xi1 xi2:var_i) m : cexec M.t :=
  let x1 := xi1.(v_var) in
  let x2 := xi2.(v_var) in
  if M.v_compat_typeP x1 x2 is left h then check_var_aux m h
  else Error (cerr_varalloc xi1 xi2 "type mismatch").

Definition is_Pvar (e:option (stype * pexpr)) :=
  match e with
  | Some (ty, Pvar x) => if is_lvar x then Some (ty,x.(gv)) else None
  | _ => None
  end.

Definition error_lv := pp_internal_error_s "allocation" "lval not equal".

Definition check_lval (e2:option (stype * pexpr)) (x1 x2:lval) m : cexec M.t :=
  match x1, x2 with
  | Lnone  _ t1, Lnone _ t2  =>
    Let _ := assert (compat_type sw_allowed t1 t2) error_lv in
    ok m
  | Lnone  _ t1, Lvar x      =>
    Let _ := assert (compat_type sw_allowed t1 x.(v_var).(vtype)) error_lv in
    ok (M.remove m x.(v_var))
  | Lvar x1    , Lvar x2     =>
    match is_Pvar e2 with
    | Some (ty, x2') =>
      if M.v_compat_typeP x1 x2 is left h then
        if [&& vtype x1 == ty, vtype x1 == vtype x2 & x2.(v_var) == x2'] then ok (M.add m x1 x2 h)
        else check_var_aux m h
      else Error (cerr_varalloc x1 x2 "type mismatch")
    | _               => check_varc x1 x2 m
    end
  | Lmem al1 w1 x1 e1, Lmem al2 w2 x2 e2  =>
    Let _ := assert ((al1 == al2) && (w1 == w2)) error_lv in
    check_v x1 x2 m >>= check_e e1 e2
  | Laset al1 aa1 w1 x1 e1, Laset al2 aa2 w2 x2 e2 =>
    Let _ := assert ((al1 == al2) && (aa1 == aa2) && (w1 == w2)) error_lv in
    check_v x1 x2 m >>= check_e e1 e2 >>= check_varc x1 x2
  | Lasub aa1 w1 len1 x1 e1, Lasub aa2 w2 len2 x2 e2 =>
    Let _ := assert [&& aa1 == aa2, w1 == w2 & len1 == len2] error_lv in
    check_v x1 x2 m >>= check_e e1 e2 >>= check_varc x1 x2
  | _          , _           => Error error_lv
  end.

Section LOOP.

  Variable check_c : M.t -> cexec M.t.

  Fixpoint loop (n:nat) (m:M.t) :=
    match n with
    | O => Error E.loop_iterator 
    | S n =>
      Let m' := check_c m in
      if M.incl m m' then ok m
      else loop n (M.merge m m')
    end.

  Variable check_c2 : M.t -> cexec (M.t * M.t).

  Fixpoint loop2 (n:nat) (m:M.t) :=
    match n with
    | O => Error E.loop_iterator 
    | S n =>
      Let m' := check_c2 m in
      if M.incl m m'.2 then ok m'.1
      else loop2 n (M.merge m m'.2)
    end.

End LOOP.

Definition check_es es1 es2 r := fold2 E.fold2 check_e es1 es2 r.

Definition check_lvals := fold2 E.fold2 (check_lval None).

Definition check_var x1 x2 r := check_lval None (Lvar x1) (Lvar x2) r.

Definition check_vars xs1 xs2 r := check_lvals (map Lvar xs1) (map Lvar xs2) r.

Section WITH_PARAMS.

Context
  {asm_op syscall_state : Type}
  {asmop:asmOp asm_op}.

Fixpoint check_i (i1 i2:instr_r) r :=
  match i1, i2 with
  | Cassgn x1 _ ty1 e1, Cassgn x2 _ ty2 e2 =>
    Let _ := assert (ty1 == ty2) (alloc_error "bad type in assignment") in
    check_e e1 e2 r >>= check_lval (Some (ty2,e2)) x1 x2

  | Copn xs1 _ o1 es1, Copn xs2 _ o2 es2 =>
    Let _ := assert (o1 == o2) (alloc_error "operators not equals") in
    check_es es1 es2 r >>= check_lvals xs1 xs2

  | Csyscall xs1 o1 es1, Csyscall xs2 o2 es2 =>
    Let _ := assert (o1 == o2) (alloc_error "syscall not equals") in
    check_es es1 es2 r >>= check_lvals xs1 xs2

  | Ccall x1 f1 arg1, Ccall x2 f2 arg2 =>
    Let _ := assert (f1 == f2) (alloc_error "functions not equals") in
    check_es arg1 arg2 r >>= check_lvals x1 x2

  | Cif e1 c11 c12, Cif e2 c21 c22 =>
    Let re := check_e e1 e2 r in
    Let r1 := fold2 E.fold2 check_I c11 c21 re in
    Let r2 := fold2 E.fold2 check_I c12 c22 re in
    ok (M.merge r1 r2)

  | Cfor x1 (d1,lo1,hi1) c1, Cfor x2 (d2,lo2,hi2) c2 =>
    Let _ := assert (d1 == d2) (alloc_error "loop directions not equals") in
    Let rhi := check_e lo1 lo2 r >>=check_e hi1 hi2 in
    let check_c r :=
      check_var x1 x2 r >>=
      fold2 E.fold2 check_I c1 c2 in
    loop check_c Loop.nb rhi

  | Cwhile a1 c1 e1 c1', Cwhile a2 c2 e2 c2' =>
    let check_c r :=
      Let r := fold2 E.fold2 check_I c1 c2 r in
      Let re := check_e e1 e2 r in
      Let r' := fold2 E.fold2 check_I c1' c2' re in
      ok (re, r') in
    Let r := loop2 check_c Loop.nb r in
    ok r

  | _, _ => Error (alloc_error "instructions not equals")
  end

with check_I i1 i2 r :=
  match i1, i2 with
  | MkI _ i1, MkI ii i2 => add_iinfo ii (check_i i1 i2 r)
  end.

Definition check_cmd := fold2 E.fold2 check_I.

Section PROG.

Context {pT: progT}.

Variable (init_alloc : extra_fun_t -> extra_prog_t -> extra_prog_t -> cexec M.t).
Variable (check_f_extra: M.t → extra_fun_t → extra_fun_t → seq var_i → seq var_i → cexec M.t).

Definition check_fundef (ep1 ep2 : extra_prog_t) (f1 f2: funname * fundef) (_:Datatypes.unit) :=
  let (f1,fd1) := f1 in
  let (f2,fd2) := f2 in
  add_funname f1 (add_finfo fd1.(f_info) (
    Let _ := assert [&& f1 == f2, fd1.(f_tyin) == fd2.(f_tyin) & fd1.(f_tyout) == fd2.(f_tyout) ]
                        (E.error "functions not equal") in
    Let r := init_alloc fd1.(f_extra) ep1 ep2 in
    Let r := check_f_extra r fd1.(f_extra) fd2.(f_extra) fd1.(f_params) fd2.(f_params) in
    Let r := check_cmd fd1.(f_body) fd2.(f_body) r in
    let es1 := map Plvar fd1.(f_res) in
    let es2 := map Plvar fd2.(f_res) in
    Let _r := check_es es1 es2 r in
    ok tt)).

Definition check_prog_error := alloc_error "check_fundef (fold2)".

Definition check_prog ep1 p_funcs1 ep2 p_funcs2 := 
  fold2 check_prog_error (check_fundef ep1 ep2) p_funcs1 p_funcs2 tt.

End PROG.

Section UPROG.

#[local]
Existing Instance progUnit.

Definition init_alloc_uprog (_: extra_fun_t) (_ _: extra_prog_t) : cexec M.t :=
  ok M.empty.

Definition check_f_extra_u (r: M.t) (e1 e2: extra_fun_t) p1 p2 :=
  Let _ := assert (e1 == e2) (E.error "extra not equal") in
  check_vars p1 p2 r.

Definition check_ufundef := check_fundef init_alloc_uprog check_f_extra_u.
Definition check_uprog := check_prog init_alloc_uprog check_f_extra_u.

End UPROG.

Section SPROG.

Context {pd:PointerData}.

#[local]
Existing Instance progStack.

Definition init_alloc_sprog (ef: extra_fun_t) (ep1 ep2: extra_prog_t) : cexec M.t :=
  check_vars [:: vid ep1.(sp_rsp); vid ep1.(sp_rip)]
             [:: vid ep2.(sp_rsp); vid ep2.(sp_rip)] M.empty.

Definition check_f_extra_s (r: M.t) (e1 e2: extra_fun_t) p1 p2 : cexec M.t :=
  Let _ :=
    assert [&&
  (e1.(sf_align) == e2.(sf_align)),
  (e1.(sf_stk_sz) == e2.(sf_stk_sz)),
  (e1.(sf_stk_ioff) == e2.(sf_stk_ioff)),
  (e1.(sf_stk_extra_sz) == e2.(sf_stk_extra_sz)),
  (e1.(sf_stk_max) == e2.(sf_stk_max)),
  (e1.(sf_max_call_depth) == e2.(sf_max_call_depth)),
  (e1.(sf_to_save) == e2.(sf_to_save)),
  (e1.(sf_save_stack) == e2.(sf_save_stack)),
  (e1.(sf_return_address) == e2.(sf_return_address)) &
  (e1.(sf_align_args) == e2.(sf_align_args))]
      (E.error "extra not equal") in
  if e1.(sf_return_address) == RAnone then
    check_vars p1 p2 r
  else
    check_vars p1 p2 r.

Definition check_sfundef := check_fundef init_alloc_sprog check_f_extra_s.
Definition check_sprog := check_prog init_alloc_sprog check_f_extra_s.

End SPROG.

End WITH_PARAMS.

End WSW.
