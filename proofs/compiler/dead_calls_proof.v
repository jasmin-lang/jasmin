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
Lemma i_callsE c i : i_calls c i = Sp.union c (i_Calls i).
Proof. Admitted.

Lemma c_callsE c i : c_calls c i = Sp.union c (c_Calls i).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Lemma dead_calls_subseq c p : subseq (dead_calls c p) p.
Proof.
elim: p c => [|[f fd] p ih] c //=; case: ifPn => _; last first.
+ case E: (dead_calls _ _) => [//|[f' fd'] p'].
  case: ifPn => _; last by rewrite -E. have := ih c.
  by rewrite E => /(subseq_trans _); apply; apply/subseq_cons.
by rewrite eqxx c_callsE; apply: ih.
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

(* -------------------------------------------------------------------- *)
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
Lemma ok p m f args m' res fd p' :
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
+ admit.
+ admit.
+ admit.
Admitted.
