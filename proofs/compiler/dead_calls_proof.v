(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* ------- *) Require Import expr compiler_util sem gen_map dead_calls.
(* ------- *) (* - *) Import PosSet.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Fixpoint i_Calls (i : instr) {struct i} : Sp.t :=
  let: MkI _ i := i in i_Calls_r i

with i_Calls_r (i : instr_r) {struct i} : Sp.t :=
  let c_Calls (cmd : cmd) :=
    foldr Sp.union Sp.empty [seq i_Calls c | c <- cmd]
  in

  match i with
  | Cassgn _  _  _    => Sp.empty
  | Copn   _  _  _    => Sp.empty
  | Cif    _  c1 c2   => Sp.union (c_Calls c1) (c_Calls c2)
  | Cfor   _  _  c1   => c_Calls c1
  | Cwhile c1 _  c2   => Sp.union (c_Calls c1) (c_Calls c2)
  | Ccall  _  _  f  _ => Sp.singleton f
  end.

Definition c_Calls (cmd : cmd) :=
  foldr Sp.union Sp.empty [seq i_Calls c | c <- cmd].

(* -------------------------------------------------------------------- *)
Lemma i_Calls_MkI ii i :
  i_Calls (MkI ii i) = i_Calls_r i.
Proof. by []. Qed.

Lemma i_Calls_asgn lv tg e :
  i_Calls_r (Cassgn lv tg e) = Sp.empty.
Proof. by []. Qed.

Lemma i_Calls_opn lv op es :
  i_Calls_r (Copn lv op es) = Sp.empty.
Proof. by []. Qed.

Lemma i_Calls_if e c1 c2 :
  i_Calls_r (Cif e c1 c2) = Sp.union (c_Calls c1) (c_Calls c2).
Proof. by []. Qed.

Lemma i_Calls_for v rg c1 :
  i_Calls_r (Cfor v rg c1) = c_Calls c1.
Proof. by []. Qed.

Lemma i_Calls_while c1 e c2 :
  i_Calls_r (Cwhile c1 e c2) = Sp.union (c_Calls c1) (c_Calls c2).
Proof. by []. Qed.

Lemma i_Calls_call ii lv f es :
  i_Calls_r (Ccall ii lv f es) = Sp.singleton f.
Proof. by []. Qed.

Lemma c_Calls_nil : c_Calls [::] = Sp.empty.
Proof. by []. Qed.

Lemma c_Calls_cons i c : c_Calls (i :: c) = Sp.union (i_Calls i) (c_Calls c).
Proof. by []. Qed.

Hint Rewrite i_Calls_MkI  i_Calls_asgn i_Calls_opn   : calls.
Hint Rewrite i_Calls_if   i_Calls_for  i_Calls_while : calls.
Hint Rewrite i_Calls_call c_Calls_nil  c_Calls_cons  : calls.

Definition CallsE :=
  (i_Calls_MkI , i_Calls_asgn, i_Calls_opn  ,
   i_Calls_if  , i_Calls_for , i_Calls_while,
   i_Calls_call, c_Calls_nil , c_Calls_cons ).

(* -------------------------------------------------------------------- *)
Lemma c_callsE c i : Sp.Equal (c_calls c i) (Sp.union c (c_Calls i)).
Proof.
move: c.
apply (@cmd_rect
         (fun i => forall c, Sp.Equal (i_calls_r c i) (Sp.union c (i_Calls_r i)))
         (fun i => forall c, Sp.Equal (i_calls c i) (Sp.union c (i_Calls i)))
         (fun i => forall c, Sp.Equal (c_calls c i) (Sp.union c (c_Calls i)))) => /=
  [ i0 ii Hi | | i0 c0 Hi Hc | x t e | xs o es | e c1 c2 Hc1 Hc2
    | v dir lo hi c0 Hc | c0 e c' Hc Hc' | ii xs f es] c //.
+ rewrite CallsE; SpD.fsetdec.
+ rewrite /= CallsE Hc Hi; SpD.fsetdec.
+ SpD.fsetdec.
+ SpD.fsetdec.
+ rewrite -/(foldl _ _) -/(foldl _ _) -/(c_calls _ _) -/(c_calls _ _) Hc2 Hc1 -/(c_Calls _) -/(c_Calls _); SpD.fsetdec.
+ rewrite -/(foldl _ _) -/(foldl _ _) -/(c_calls _ _) -/(c_calls _ _) Hc' Hc -/(c_Calls _) -/(c_Calls _); SpD.fsetdec.
+ SpD.fsetdec.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dead_calls_subseq c p : subseq (dead_calls c p) p.
Proof.
elim: p c => [|[f fd] p ih] c //=; case: ifPn => _; last first.
+ case E: (dead_calls _ _) => [//|[f' fd'] p'].
  case: ifPn => _; last by rewrite -E. have := ih c.
  by rewrite E => /(subseq_trans _); apply; apply/subseq_cons.
rewrite eqxx; exact: ih.
Qed.

(* -------------------------------------------------------------------- *)
Section PgCompat.
Variables (c : Sp.t) (p p' : prog).

Definition pg_compat_cmd :=
  forall m cmd m', sem p m cmd m' -> sem p' m cmd m'.

Definition pg_compat_Instr :=
  forall m i m', sem_I p m i m' -> sem_I p' m i m'.

Definition pg_compat_instr :=
  forall m i m', sem_i p m i m' -> sem_i p' m i m'.

Definition pg_compat_for :=
  forall v rg m cmd m',
    sem_for p v rg m cmd m' -> sem_for p' v rg m cmd m'.

Definition pg_compat_call :=
  forall m f args m' res, Sp.In f c ->
    sem_call p  m f args m' res ->
    sem_call p' m f args m' res.
End PgCompat.

Lemma subseq_in {T: eqType} (s: seq T) s' x: subseq s s' -> x \in s -> x \in s'.
Proof.
elim: s' s=> [|a' l' IH] s //=.
+ by move=> /eqP ->.
move: s IH=> [] // a l IH.
case: ifP.
+ move=> /eqP -> Hsub // H.
  rewrite in_cons in H.
  move: H=> /orP; case.
  + move=> /eqP ->.
    exact: mem_head.
  + move=> /(IH _ Hsub) H.
    by rewrite in_cons H orbT.
move=> _ Hsub Hin.
have H := IH _ Hsub Hin.
by rewrite in_cons H orbT.
Qed.

Lemma get_same (p p': prog) fn fd fd':
  uniq (map fst p) ->
  subseq p' p ->
  get_fundef p fn = Some fd ->
  get_fundef p' fn = Some fd' ->
  fd = fd'.
Proof.
  elim: p p'=> [] // -[fn0 fd0] l IH /= p' /andP [Hnot Huniq].
  case: p' IH=> [] // [fn1 fd1] l1 IH.
  case: ifP.
  + move=> /eqP ->.
    rewrite !get_fundef_cons /=.
    case: ifP.
    + by move=> _ _ []<- []<-.
    move=> _ Hsub H0 H1.
    exact: (IH _ _ Hsub).
  move=> Hdiff Hsub.
  move: Hdiff=> /eqP Hdiff.
  rewrite !get_fundef_cons /=.
  case: ifP.
  + move=> /eqP? []?; subst fn fd.
    move=> H.
    exfalso; move: Hnot=> /negP; apply.
    apply: subseq_in.
    apply: map_subseq Hsub.
    case: ifP H.
    + move=> /eqP?[]?; subst fn1 fd1.
      by rewrite /= in_cons eq_refl.
    move=> _ Hget.
    have Hin := get_fundef_in Hget.
    by rewrite in_cons /= Hin orbT.
  move=> _ H.
  case: ifP.
  + move=> /eqP? []?; subst fn fd'.
    apply: (IH _ _ Hsub)=> //.
    by rewrite get_fundef_cons /= eq_refl.
  move=> Hneq H1.
  apply: (IH _ _ Hsub H)=> //.
  by rewrite get_fundef_cons /= Hneq.
Qed.

Lemma get_dead_calls p fn f f0:
  Sp.In fn f ->
  get_fundef p fn = Some f0 ->
  get_fundef (dead_calls f p) fn = Some f0.
Proof.
  elim: p f=> [] // -[fn0 fd0] l IH /= f Hin.
  rewrite get_fundef_cons /=.
  case: ifP.
  + move=> /eqP?[]?; subst fn0 f0.
    move: Hin=> /SpD.F.mem_1 ->.
    by rewrite get_fundef_cons /= eq_refl.
  move=> Hneq H.
  have Hin': Sp.In fn (c_calls f (f_body fd0)).
    rewrite c_callsE; SpD.fsetdec.
  case: ifP.
  + move=> ?.
    rewrite get_fundef_cons /= Hneq.
    exact: IH.
  move=> _; exact: IH.
Qed.

Section PROOF.
  Variables (f : Sp.t) (p: prog).
  Hypothesis p_uniq: uniq (map fst p).
  Definition p' := dead_calls f p.

  Definition def_incl sv :=
    forall x : positive, Sp.In x sv -> exists fd, get_fundef p' x = Some fd.

  Lemma call_stbl fn fd:
    get_fundef p' fn = Some fd -> def_incl (c_Calls fd.(f_body)).
  Proof.
  Admitted.

  Lemma def_incl_union a b:
    def_incl (Sp.union a b) -> def_incl a /\ def_incl b.
  Proof.
    split=> x Hx; apply: H; SpD.fsetdec.
  Qed.

  Let Pi (s:estate) (i:instr) (s':estate) :=
    def_incl (i_Calls i) -> sem_I p s i s' -> sem_I p' s i s'.

  Let Pi_r (s:estate) (i:instr_r) (s':estate) :=
    def_incl (i_Calls_r i) -> sem_i p s i s' -> sem_i p' s i s'.

  Let Pc (s:estate) (c:cmd) (s':estate) :=
    def_incl (c_Calls c) -> sem p s c s' -> sem p' s c s'.

  Let Pfor (i:var_i) vs s c s' :=
    def_incl (c_Calls c) -> sem_for p i vs s c s' -> sem_for p' i vs s c s'.

  Let Pfun m1 fn vargs m2 vres :=
    def_incl (Sp.singleton fn) -> sem_call p m1 fn vargs m2 vres -> sem_call p' m1 fn vargs m2 vres.

  Local Lemma Hskip s : Pc s [::] s.
  Proof. move=> _ _; exact: Eskip. Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p s1 i s2 ->
    Pi s1 i s2 -> sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> Hsi Hi Hsc Hc Hincl.
    rewrite CallsE in Hincl.
    move: Hincl=> /def_incl_union [Hincli Hinclc] H.
    exact: (Eseq (Hi Hincli Hsi) (Hc Hinclc Hsc)).
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof.
    move=> Hs Hi Hincl _.
    apply: EmkI.
    exact: (Hi Hincl Hs).
  Qed.

  Local Lemma Hassgn s1 s2 l tag e :
    Let v := sem_pexpr s1 e in write_lval l v s1 = Ok error s2 ->
    Pi_r s1 (Cassgn l tag e) s2.
  Proof.
    move=> H _ _; exact: (Eassgn _ _ H).
  Qed.

  Local Lemma Hopn s1 s2 o xs es :
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_lvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    move=> H _ _; exact: (Eopn _ H).
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> H Hsi Hc Hincl _.
    rewrite CallsE in Hincl.
    move: Hincl=> /def_incl_union [Hincl1 Hincl2].
    apply: (Eif_true _ H).
    exact: (Hc Hincl1 Hsi).
  Qed.

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> H Hsi Hc Hincl _.
    rewrite CallsE in Hincl.
    move: Hincl=> /def_incl_union [Hincl1 Hincl2].
    apply: (Eif_false _ H).
    exact: (Hc Hincl2 Hsi).
  Qed.

  Local Lemma Hwhile_true s1 s2 s3 s4 c e c' :
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = ok true ->
    sem p s2 c' s3 -> Pc s2 c' s3 ->
    sem_i p s3 (Cwhile c e c') s4 -> Pi_r s3 (Cwhile c e c') s4 -> Pi_r s1 (Cwhile c e c') s4.
  Proof.
    move=> Hs1 Hc1 H Hs2 Hc2 Hsw Hiw Hinclw _.
    rewrite CallsE in Hinclw.
    have /def_incl_union [Hincl Hincl'] := Hinclw.
    exact: (Ewhile_true (Hc1 Hincl Hs1) H (Hc2 Hincl' Hs2) (Hiw Hinclw Hsw)).
  Qed.

  Local Lemma Hwhile_false s1 s2 c e c' :
    sem p s1 c s2 -> Pc s1 c s2 ->
    Let x := sem_pexpr s2 e in to_bool x = ok false ->
    Pi_r s1 (Cwhile c e c') s2.
  Proof.
    move=> Hs1 Hc1 H Hinclw _.
    rewrite CallsE in Hinclw.
    have /def_incl_union [Hincl Hincl'] := Hinclw.
    exact: (Ewhile_false _ (Hc1 Hincl Hs1) H).
  Qed.

  Local Lemma Hfor s1 s2 (i:var_i) d lo hi c vlo vhi :
    Let x := sem_pexpr s1 lo in to_int x = Ok error vlo ->
    Let x := sem_pexpr s1 hi in to_int x = Ok error vhi ->
    sem_for p i (wrange d vlo vhi) s1 c s2 ->
    Pfor i (wrange d vlo vhi) s1 c s2 -> Pi_r s1 (Cfor i (d, lo, hi) c) s2.
  Proof.
    move=> Hlo Hhi Hsf Hf Hincl _.
    rewrite CallsE in Hincl.
    apply: (Efor Hlo Hhi).
    exact: (Hf Hincl Hsf).
  Qed.

  Local Lemma Hfor_nil s i c: Pfor i [::] s c s.
  Proof.
    move=> Hincl _; exact: EForDone.
  Qed.

  Local Lemma Hfor_cons s1 s1' s2 s3 (i : var_i) (w:Z) (ws:seq Z) c :
    write_var i w s1 = Ok error s1' ->
    sem p s1' c s2 ->
    Pc s1' c s2 ->
    sem_for p i ws s2 c s3 -> Pfor i ws s2 c s3 -> Pfor i (w :: ws) s1 c s3.
  Proof.
   move=> H Hsc Hc Hsf Hf Hincl _.
   exact: (EForOne H (Hc Hincl Hsc) (Hf Hincl Hsf)).
  Qed.

  Local Lemma Hcall s1 m2 s2 ii xs fn args vargs vs:
    sem_pexprs s1 args = Ok error vargs ->
    sem_call p (emem s1) fn vargs m2 vs ->
    Pfun (emem s1) fn vargs m2 vs ->
    write_lvals {| emem := m2; evm := evm s1 |} xs vs = Ok error s2 ->
    Pi_r s1 (Ccall ii xs fn args) s2.
  Proof.
    move=> Hargs Hcall Hfun Hres Hincl Hsi.
    apply: (Ecall _ Hargs _ Hres).
    exact: Hfun.
  Qed.

  Local Lemma Hproc m1 m2 fn fd vargs s1 vm2 vres:
    get_fundef p fn = Some fd ->
    write_vars (f_params fd) vargs {| emem := m1; evm := vmap0 |} = ok s1 ->
    sem p s1 (f_body fd) {| emem := m2; evm := vm2 |} ->
    Pc s1 (f_body fd) {| emem := m2; evm := vm2 |} ->
    mapM (fun x : var_i => get_var vm2 x) (f_res fd) = ok vres ->
    List.Forall is_full_array vres ->
    Pfun m1 fn vargs m2 vres.
  Proof.
    move=> Hget Hvargs Hsem Hc Hvres Hfull Hin Hcall.
    have [|fd' Hfd'] := Hin fn; first by SpD.fsetdec.
    have H := (get_same p_uniq (dead_calls_subseq f p) Hget Hfd'); subst fd'.
    apply: (EcallRun _ Hvargs _ Hvres Hfull)=> //.
    apply: Hc=> //.
    apply: (call_stbl Hfd').
  Qed.

  Lemma dead_calls_callP fd mem mem' va vr:
    Sp.In fd f ->
    sem_call p mem fd va mem' vr ->
    sem_call p' mem fd va mem' vr.
  Proof.
    move=> Hincl H.
    apply: (@sem_call_Ind p Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc)=> //.
    sinversion H.
    move=> {H1 H2 H3 H4} x Hx.
    have ? : x = fd by SpD.fsetdec.
    subst x=> {Hx}.
    exists f0.
    rewrite /p'.
    exact: get_dead_calls.
  Qed.
End PROOF.

(* -------------------------------------------------------------------- *)
(*
Lemma pg_compat_sub c1 c2 p p' : Sp.Subset c2 c1 ->
     pg_compat_call c1 p p'
  -> pg_compat_call c2 p p'.
Proof.
by move=> lt h m f args m' res f_in_c2 /h; apply; SpD.fsetdec.
Qed.

Lemma pg_compat_cmd_consl i c p p' :
     pg_compat_call (c_Calls (i :: c)) p p'
  -> pg_compat_call (i_Calls i) p p'.
Proof.
by apply: pg_compat_sub; rewrite CallsE; SpD.fsetdec.
Qed.

Lemma pg_compat_cmd_consr i c p p' :
     pg_compat_call (c_Calls (i :: c)) p p'
  -> pg_compat_call (c_Calls c) p p'.
Proof.
by apply: pg_compat_sub; rewrite CallsE; SpD.fsetdec.
Qed.

Lemma pg_compat_while_pre c e c' p p' :
     pg_compat_call (i_Calls_r (Cwhile c e c')) p p'
  -> pg_compat_call (c_Calls c) p p'.
Proof.
by apply: pg_compat_sub; rewrite CallsE; SpD.fsetdec.
Qed.

Lemma pg_compat_while_post c e c' p p' :
     pg_compat_call (i_Calls_r (Cwhile c e c')) p p'
  -> pg_compat_call (c_Calls c') p p'.
Proof.
by apply: pg_compat_sub; rewrite CallsE; SpD.fsetdec.
Qed.

Lemma pg_compat_for_body v rg c p p' :
     pg_compat_call (i_Calls_r (Cfor v rg c)) p p'
  -> pg_compat_call (c_Calls c) p p'.
Proof.
by apply: pg_compat_sub; rewrite CallsE; SpD.fsetdec.
Qed.

(* -------------------------------------------------------------------- *)
Local Hint Resolve pg_compat_cmd_consl pg_compat_cmd_consr.
Local Hint Resolve pg_compat_while_pre pg_compat_while_post.
Local Hint Resolve pg_compat_for_body.
Local Hint Constructors sem sem_I sem_i sem_for sem_call.

(* -------------------------------------------------------------------- *)
Lemma __ok p m f args m' res fd p' :
     pg_compat_call (c_Calls fd.(f_body)) p p'
  -> sem_call ((f, fd) :: p ) m f args m' res
  -> sem_call ((f, fd) :: p') m f args m' res.
Proof.
move=> Hcompat Hcall.
sinversion Hcall.
apply: (EcallRun _ H0 _ H2)=> //.
rewrite get_fundef_cons /= eq_refl.
by rewrite get_fundef_cons /= eq_refl in H.
admit.
Admitted.

Lemma _ok p m f args m' res fd p' :
     pg_compat_call (c_Calls fd.(f_body)) p p'
  -> sem_call ((f, fd) :: p ) m f args m' res
  -> sem_call ((f, fd) :: p') m f args m' res.
Proof.
pose Pc m c m' :=
     pg_compat_call (c_Calls c) p p'
  -> sem p m c m' -> sem p' m c m'.
pose PI m i m' :=
     pg_compat_call (i_Calls i) p p'
  -> sem_I p m i m' -> sem_I p' m i m'.
pose Pi m i m' :=
     pg_compat_call (i_Calls_r i) p p'
  -> sem_i p m i m' -> sem_i p' m i m'.
pose Pf v rg m c m' :=
     pg_compat_call (c_Calls c) p p'
  -> sem_for p v rg m c m' -> sem_for p' v rg m c m'.
pose PC m f args m' res :=
     pg_compat_call (c_Calls fd.(f_body)) p p'
  -> sem_call ((f, fd) :: p ) m f args m' res
  -> sem_call ((f, fd) :: p') m f args m' res.
apply: (@sem_call_Ind p Pc Pi PI Pf PC);
  rewrite {}/Pc {}/Pi {}/PI {}/Pf {}/PC; try by eauto 7.
+ move=> ?????????.
  move=> Hargs Hcall _ Hres Hcompat Hi.
  apply: (Ecall _ Hargs _ Hres).
  apply: Hcompat=> //.
  rewrite CallsE; SpD.fsetdec.
+ move=> ???????? Hget Hargs ? IH Hres ? Hcompat Hcall.
  admit.
  apply: EcallRun.
  rewrite get_fundef_cons /= eq_refl //.
  admit.
  apply: (EcallRun _ Hargs _ Hres)=> //.
  rewrite get_fundef_cons /= eq_refl.
+ admit.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma dead_calls_ok (f : Sp.t) (p : prog) : uniq (map fst p) ->
  pg_compat_call f p (dead_calls f p).
Proof.
elim: p=> [|[fn fd] l IH] Huniq //=.
case: ifP=> Hmem.
+ move=> m e args m' res e_in_f Hcall.
  case/boolP: (e == fn)=> /eqP.
  + move=> ?; subst e.
    apply: (_ok _ Hcall).
    admit. (* using IH *)
  admit.
move=> m e args m' res e_in_f Hcall.
apply: IH=> //.
admit.
  have := _ok _ Hcall.
  apply: _ok.
Print dead_calls.
*)

Lemma foldl_compat x y l (x_eq_y: Sp.Equal x y):
  Sp.Equal (foldl (fun f c => Sp.add c f) x l)
           (foldl (fun f c => Sp.add c f) y l).
Proof.
elim: l x y x_eq_y=> // a l IH /= x y x_eq_y.
by apply: IH; SpD.fsetdec.
Qed.

Lemma foldlE a l x:
  Sp.Equal (foldl (fun f c => Sp.add c f) x (a :: l))
           (Sp.add a (foldl (fun f c => Sp.add c f) x l)).
Proof.
elim: l a x=> // a0 l IH a x.
rewrite /= in IH.
rewrite /=.
rewrite -IH.
apply: foldl_compat; SpD.fsetdec.
Qed.

(* -------------------------------------------------------------------- *)
Lemma dead_calls_errP (s : seq funname) (p p': prog) : 
  dead_calls_err s p = ok p' ->
  forall f m args m' res, f \in s -> 
    sem_call p  m f args m' res ->
    sem_call p' m f args m' res.
Proof.
rewrite /dead_calls_err; case: ifP=> // /negbFE H []<- f m args m' res fins Hcall.
apply: dead_calls_callP=> //.
elim: s fins=> // a l IH Hin.
rewrite foldlE.
rewrite in_cons in Hin; case/orP: Hin=> [/eqP ->|/IH Hin]; SpD.fsetdec.
Qed.
