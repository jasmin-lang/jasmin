(* * The semantics of an instruction, from its total semantics and its
   conditions.

   An instruction is described like an operator (see [op_semi.v]), by a total
   semantics, a list of conditions on its arguments and the error it raises
   when one of them fails; [mk_semi] assembles them.  Two things are specific
   to the instructions: an instruction has several outputs, some of which may
   be left undefined (one condition of [seq safety_cond] per output says when
   an output is defined), and its safety conditions are the ones of
   [wsize.safe_cond], decided by [values.check_safe_cond]. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype ssralg.
From mathcomp Require Import word_ssrZ.
Require Export op_semi.
Require Import values.
Import Utf8.

Local Open Scope seq_scope.

(* -------------------------------------------------------------------- *)
(* ** Auxiliary facts about [of_val] and [truncate_val]                  *)

Lemma truncate_val_to_val t (x : sem_t t) : truncate_val t (to_val x) = ok (to_val x).
Proof. by rewrite /truncate_val of_val_to_val. Qed.

Lemma of_val_subctype_ok t t' (x : sem_t t) :
  subctype t' t -> exists y : sem_t t', of_val t' (to_val x) = ok y.
Proof.
move=> hsub; have [v2] := subctype_truncate_val hsub (truncate_val_to_val x).
by rewrite /truncate_val; case hof: (of_val t' (to_val x)) => [y|e] //= _; exists y.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Well-formed conditions                                             *)

Lemma safety_cond_wf_wt tin c : safety_cond_wf tin c -> safety_cond_wt tin c.
Proof. by move=> /andP []. Qed.

Lemma safety_cond_wf_total tin c : safety_cond_wf tin c -> safety_cond_total c.
Proof. by move=> /andP []. Qed.

Lemma all_safety_cond_wf_wt tin l : all (safety_cond_wf tin) l -> all (safety_cond_wt tin) l.
Proof. by apply: sub_all; apply: safety_cond_wf_wt. Qed.

Lemma all_safety_cond_wf_total tin l : all (safety_cond_wf tin) l -> all safety_cond_total l.
Proof. by apply: sub_all; apply: safety_cond_wf_total. Qed.

(* -------------------------------------------------------------------- *)
(* ** Basic properties of the interpretation                             *)

Lemma safety_cond_type_below tin c t :
  safety_cond_type tin c = Some t -> safety_cond_below (size tin) c.
Proof.
elim: c t => //=.
+ by move=> k t; case: ifP.
+ move=> o c ih t; case heq: (safety_cond_type tin c) => [t1|] //=; case: ifP => // _ _.
  by apply: ih heq.
move=> o c1 ih1 c2 ih2 t.
case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
case: ifP => // _ _.
by rewrite (ih1 _ heq1) (ih2 _ heq2).
Qed.

(* The interpretation only depends on the arguments the condition reads. *)
Lemma sem_safety_cond_cat (vs vs' : values) c :
  safety_cond_below (size vs) c -> sem_safety_cond (vs ++ vs') c = sem_safety_cond vs c.
Proof.
elim: c => //=.
+ by move=> k hk; rewrite nth_cat hk.
+ by move=> o c ih h; rewrite ih.
by move=> o c1 ih1 c2 ih2 /andP [h1 h2]; rewrite ih1 // ih2.
Qed.

(* A well-typed total condition evaluates to a value on arguments of the
   announced types. *)
Lemma safety_cond_type_ok tin (vs : values) c t :
  List.Forall2 (fun (t : ctype) v => exists x : sem_t t, v = to_val x) tin vs ->
  safety_cond_total c ->
  safety_cond_type tin c = Some t ->
  exists x : sem_t t, sem_safety_cond vs c = ok (to_val x).
Proof.
move=> hall; elim: c t => /=.
1,2: by move=> x t _ [<-]; eexists.
+ move=> k t _; case: ifP => // hk [<-].
  by have [x hx] := Forall2_nth hall cbool undef_b hk; exists x; rewrite hx.
+ move=> o c ih t /andP [hto htot].
  case heq: (safety_cond_type tin c) => [t1|] //=; case: ifP => // hsub [<-].
  have [x1 ->] := ih _ htot heq.
  have [y hy] := of_val_subctype_ok x1 hsub.
  by rewrite /= hy /=; eexists.
move=> o c1 ih1 c2 ih2 t /and3P [hto ht1 ht2].
case heq1: (safety_cond_type tin c1) => [t1|] //=; case heq2: (safety_cond_type tin c2) => [t2|] //=.
case: ifP => // /andP [hsub1 hsub2] [<-].
have [x1 ->] := ih1 _ ht1 heq1; have [x2 ->] := ih2 _ ht2 heq2.
have [y1 hy1] := of_val_subctype_ok x1 hsub1.
have [y2 hy2] := of_val_subctype_ok x2 hsub2.
by rewrite /= hy1 /= hy2 /=; eexists.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Extensionally equal semantics                                      *)

Lemma sem_prod_eq_refl {T} tin (f : sem_prod tin T) : sem_prod_eq tin f f.
Proof. by elim: tin f => //= t tin ih f v; apply ih. Qed.

Lemma sem_prod_eq_sym {T} tin (f g : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_prod_eq tin g f.
Proof. by elim: tin f g => /= [f g -> // | t tin ih f g h v]; apply: ih (h v). Qed.

Lemma sem_prod_eq_trans {T} tin (f g h : sem_prod tin T) :
  sem_prod_eq tin f g -> sem_prod_eq tin g h -> sem_prod_eq tin f h.
Proof.
by elim: tin f g h => /= [f g h -> // | t tin ih f g h h1 h2 v]; apply: ih (h1 v) (h2 v).
Qed.

Lemma sem_prod_eq_app {A B} tin (g : A -> B) (f1 f2 : sem_prod tin A) :
  sem_prod_eq tin f1 f2 -> sem_prod_eq tin (sem_prod_app f1 g) (sem_prod_app f2 g).
Proof. by elim: tin f1 f2 => /= [f1 f2 -> // | t tin ih f1 f2 h v]; apply: ih (h v). Qed.

(* Two pointwise equal post-treatments give two equal semantics. *)
Lemma mk_semi_aux_eq {T T'} (P Q : values -> T -> exec T') vs tin (f : sem_prod tin T) :
  (forall vs t, P vs t = Q vs t) ->
  sem_prod_eq tin (mk_semi_aux P vs tin f) (mk_semi_aux Q vs tin f).
Proof. by move=> h; elim: tin vs f => /= [vs f | t tin ih vs f v]; [apply h | apply ih]. Qed.

(* Post-composing the result is the same as post-composing the post-treatment. *)
Lemma sem_prod_app_mk_semi_aux {T T' T''} (P : values -> T -> exec T')
    (g : exec T' -> exec T'') vs tin (f : sem_prod tin T) :
  sem_prod_eq tin (sem_prod_app (mk_semi_aux P vs tin f) g)
                  (mk_semi_aux (fun vs t => g (P vs t)) vs tin f).
Proof. by elim: tin vs f => //= t tin ih vs f v; apply ih. Qed.

(* Pre-composing the total semantics is the same as pre-composing the
   post-treatment. *)
Lemma mk_semi_aux_sem_prod_app {T T' T''} (Q : values -> T'' -> exec T')
    (h : T -> T'') vs tin (f : sem_prod tin T) :
  sem_prod_eq tin (mk_semi_aux Q vs tin (sem_prod_app f h))
                  (mk_semi_aux (fun vs t => Q vs (h t)) vs tin f).
Proof. by elim: tin vs f => //= t tin ih vs f v; apply ih. Qed.

(* If the post-treatment succeeds on the arguments, so does the construction. *)
Lemma mk_semi_aux_safe {T T'} (P : values -> T -> exec T') (Q : values -> Prop) vs tin
    (f : sem_prod tin T) :
  (forall vs t, Q vs -> exists t', P vs t = ok t') ->
  interp_safe_cond_ty_aux (fun vs r => Q vs -> exists t, r = ok t) vs (mk_semi_aux P vs tin f).
Proof. by move=> h; elim: tin vs f => //= t tin ih vs f v; apply ih. Qed.

(* Extensionally equal semantics are applied to the same arguments with the
   same result. *)
Lemma sem_prod_eq_app_sopn_v tin tout (f g : sem_prod tin (exec (sem_tuple tout))) vs :
  sem_prod_eq tin f g -> app_sopn_v f vs = app_sopn_v g vs.
Proof.
move=> heq; rewrite /app_sopn_v.
suff h : app_sopn tin f vs = app_sopn tin g vs by rewrite h.
elim: tin f g vs heq => /= [f g vs -> // | t tin ih f g [ | v vs] //= heq].
by case: of_val => //= x; apply ih.
Qed.

(* -------------------------------------------------------------------- *)
(* ** Total tuples and filtering                                         *)

(* Like [sem_tuple], but boolean components are [bool] instead of
   [option bool]: the result of a total semantics. *)
Definition sem_tuple_t (ts : seq ctype) := ltuple (map sem_t ts).

(* A boolean component is kept when the mask says so, every other component is
   left untouched. *)
Definition filter_ot (b : bool) (t : ctype) : sem_t t -> sem_ot t :=
  if t is cbool then (fun x => if b then Some x else None) else id.

(* A component whose condition holds is the value itself. *)
Lemma filter_ot_true t (x : sem_t t) : filter_ot true x = sem_prod_id x.
Proof. by case: t x. Qed.

Fixpoint filter_tuple (ts : seq ctype) (mask : seq bool) : sem_tuple_t ts -> sem_tuple ts :=
  match ts return sem_tuple_t ts -> sem_tuple ts with
  | [::] => fun _ => tt
  | t :: ts =>
    let rec := @filter_tuple ts (behead mask) in
    match ts return (sem_tuple_t ts -> sem_tuple ts) ->
                    sem_tuple_t (t :: ts) -> sem_tuple (t :: ts) with
    | [::] => fun _ (x : sem_t t) => filter_ot (head false mask) x
    | t1 :: ts' => fun rec (p : sem_t t * sem_tuple_t (t1 :: ts')) =>
        (filter_ot (head false mask) p.1, rec p.2)
    end rec
  end.
Arguments filter_tuple : clear implicits.

(* A default total tuple, for the operators that have no semantics. *)
Definition dflt_t (t : ctype) : sem_t t :=
  match t return sem_t t with
  | cbool => false
  | cint => 0%Z
  | carr n => WArray.empty n
  | cword ws => 0%R
  end.

Fixpoint dflt_tuple (ts : seq ctype) : sem_tuple_t ts :=
  match ts return sem_tuple_t ts with
  | [::] => tt
  | t :: ts =>
    match ts return sem_tuple_t ts -> sem_tuple_t (t :: ts) with
    | [::] => fun _ => dflt_t t
    | t1 :: ts' => fun r => (dflt_t t, r)
    end (dflt_tuple ts)
  end.

(* [defined_as b v] : [v] is defined exactly when [b] holds, for a boolean
   component; a component of any other type is always defined. *)
Definition defined_as (b : bool) (v : value) : Prop :=
  if type_of_val v is cbool then is_defined v = b else is_defined v.

Lemma filter_add_tuple (t : ctype) (lt : seq ctype) (b : bool) (mask : seq bool)
   (v : sem_t t) (xs : sem_tuple_t lt) :
  filter_tuple (t :: lt) (b :: mask) (add_tuple v xs)
  = add_tuple (filter_ot b v) (filter_tuple lt mask xs).
Proof. by case: lt xs => [ | t1 lt] xs //=; case: xs. Qed.

(* Total counterpart of [sem_prod_tuple]: the identity on a tuple of
   arguments, without wrapping the booleans in [Some]. *)
Fixpoint sem_prod_tuple_t (lt : seq ctype) : sem_prod lt (sem_tuple_t lt) :=
  match lt return sem_prod lt (sem_tuple_t lt) with
  | [::] => tt
  | t :: lt' =>
      fun v => sem_prod_app (sem_prod_tuple_t lt') (fun xs => add_tuple v xs)
  end.

(* -------------------------------------------------------------------- *)
(* ** The construction for the instructions                              *)

Definition is_ErrType (e : error) : bool := if e is ErrType then true else false.

(* The safety check of an instruction: its conditions are the old
   [wsize.safe_cond], decided by [values.check_safe_cond]; if one of them
   fails, the instruction raises the error it declares. *)
Definition check_safe_old (vs : values) (safe : seq safe_cond) (err : error) : exec unit :=
  if all (check_safe_cond vs) safe then ok tt else Error err.

Lemma check_safe_old_ok vs safe err :
  all (check_safe_cond vs) safe -> check_safe_old vs safe err = ok tt.
Proof. by rewrite /check_safe_old => ->. Qed.

Lemma all_check_safe_cond vs safe :
  List.Forall (interp_safe_cond vs) safe -> all (check_safe_cond vs) safe.
Proof. by elim => //= sc l hsc _ ih; apply/andP; split => //; apply/check_safe_condP. Qed.

(* The semantics of an instruction: the safety conditions are checked on the
   arguments, then the total semantics is filtered by the initialisation
   conditions, one per output. *)
Definition mk_semi (tin tout : seq ctype) (safe : seq safe_cond) (err : error)
    (init : seq safety_cond)
    (f : sem_prod tin (sem_tuple_t tout)) : sem_prod tin (exec (sem_tuple tout)) :=
  mk_semi_aux
    (fun vs t => Let _ := check_safe_old vs safe err in
                 ok (filter_tuple tout (map (safety_cond_holds vs) init) t))
    [::] tin f.
Arguments mk_semi {tin tout} safe err init f : assert.

(* -------------------------------------------------------------------- *)
(* ** Generic properties of [mk_semi]                                    *)

(* If the safety conditions hold, [mk_semi] succeeds. *)
Lemma mk_semi_safe tin tout safe err init f :
  values.interp_safe_cond_ty (tin := tin) safe (@mk_semi tin tout safe err init f).
Proof.
apply: mk_semi_aux_safe => vs t hall.
rewrite (check_safe_old_ok err (all_check_safe_cond hall)) /=.
by eexists; reflexivity.
Qed.

(* Same, when the post-treatment is only known on the arguments prefixed by
   [vs1]. *)
Lemma mk_semi_aux_ok_cat {T T'} (P : values -> T -> exec T') (g : T -> T') vs1
    (tin : seq ctype) (f : sem_prod tin T) :
  (forall vs2 t, P (vs1 ++ vs2) t = ok (g t)) ->
  sem_prod_eq tin (mk_semi_aux P vs1 tin f) (sem_prod_ok tin (sem_prod_app f g)).
Proof.
elim: tin vs1 f => /= [vs1 f h | t tin ih vs1 f h v].
+ by have := h [::] f; rewrite cats0.
by apply: ih => vs2 t2; rewrite cat_rcons h.
Qed.

(* Same, when the total semantics is a constant. *)
Lemma mk_semi_aux_const {T T'} (P : values -> T -> exec T') vs1
    (tin : seq ctype) (t0 : T) (r : exec T') :
  (forall vs2, P (vs1 ++ vs2) t0 = r) ->
  sem_prod_eq tin (mk_semi_aux P vs1 tin (sem_prod_const tin t0)) (sem_prod_const tin r).
Proof.
elim: tin vs1 => /= [vs1 h | t tin ih vs1 h v].
+ by have := h [::]; rewrite cats0.
by apply: ih => vs2; rewrite cat_rcons h.
Qed.

Lemma sem_prod_ok_app {A} (lt : seq ctype) (X : sem_prod lt A) :
  sem_prod_eq lt (sem_prod_ok lt X) (sem_prod_app X (fun a : A => ok a)).
Proof. by elim: lt X => //= t lt ih X v. Qed.

Lemma sem_prod_app_comp {A B C} (lt : seq ctype) (f : sem_prod lt A)
    (g : A -> B) (h : B -> C) :
  sem_prod_eq lt (sem_prod_app (sem_prod_app f g) h) (sem_prod_app f (fun x => h (g x))).
Proof. by elim: lt f => //= t lt ih f v. Qed.

(* Building a tuple out of the arguments and filtering it with an all-true
   mask is building the tuple of the semantics. *)
Lemma sem_prod_tuple_filter {A} (lt : seq ctype) (mask : seq bool)
      (K : sem_tuple lt -> A) (K' : sem_tuple_t lt -> A) :
  all id mask -> size mask = size lt ->
  (forall t, K' t = K (filter_tuple lt mask t)) ->
  sem_prod_eq lt (sem_prod_app (sem_prod_tuple_t lt) K') (sem_prod_app (sem_prod_tuple lt) K).
Proof.
elim: lt mask K K'.
+ by move=> mask K K' _ _ h /=; rewrite h.
move=> t lt ih [ | b mask] // K K' /andP [hb hall] [hsz] h v /=.
apply: sem_prod_eq_trans; first by apply: sem_prod_app_comp.
apply: sem_prod_eq_trans; last by apply: sem_prod_eq_sym; apply: sem_prod_app_comp.
apply: (ih mask _ _ hall hsz) => t2.
by rewrite h filter_add_tuple hb filter_ot_true.
Qed.


(* -------------------------------------------------------------------- *)
(* ** Guarded conditions                                                 *)

(* The initialisation condition of a conditional instruction: the output keeps
   its previous value when the guard (the argument [g]) is false, so it is
   defined in that case too. *)
Definition cond_init (g : nat) (c : safety_cond) : safety_cond :=
  sc_or (sc_not (IVar g)) c.

Lemma safety_cond_wt_cond_init tin tin' c :
  safety_cond_wt tin c -> safety_cond_wt (tin ++ cbool :: tin') (cond_init (size tin) c).
Proof.
rewrite /safety_cond_wt /cond_init /sc_or /sc_not /= => /eqP /safety_cond_type_cat -> /=.
rewrite size_cat /= nth_cat ltnn subnn /=.
by have -> : (size tin < size tin + (size tin').+1)%nat by rewrite -addn1 leq_add2l.
Qed.

Lemma safety_cond_total_cond_init g c :
  safety_cond_total c -> safety_cond_total (cond_init g c).
Proof. by move=> h; rewrite /cond_init /= h. Qed.

Lemma safety_cond_wf_cond_init tin tin' c :
  safety_cond_wf tin c -> safety_cond_wf (tin ++ cbool :: tin') (cond_init (size tin) c).
Proof.
by move=> /andP [h1 h2];
  rewrite /safety_cond_wf safety_cond_wt_cond_init // safety_cond_total_cond_init.
Qed.

Lemma safety_cond_holds_cond_init (vs0 vs2 : values) (b : bool) (c : safety_cond) (bb : bool) :
  safety_cond_below (size vs0) c ->
  sem_safety_cond vs0 c = ok (Vbool bb) ->
  safety_cond_holds (vs0 ++ Vbool b :: vs2) (cond_init (size vs0) c) = (~~ b) || bb.
Proof.
move=> hb hev; rewrite /safety_cond_holds /cond_init /sc_or /sc_not /=.
rewrite nth_cat ltnn subnn /=.
by rewrite (sem_safety_cond_cat (Vbool b :: vs2) hb) hev /=.
Qed.

Lemma cond_init_val (ts : seq ctype) (vs0 vs2 : values) (b : bool) (c : safety_cond) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  safety_cond_total c -> safety_cond_wt ts c ->
  safety_cond_holds (vs0 ++ Vbool b :: vs2) (cond_init (size ts) c)
  = (~~ b) || safety_cond_holds vs0 c.
Proof.
move=> hall htot hwt.
have hsz : size ts = size vs0 by apply: Forall2_size hall.
have [x hx] := safety_cond_type_ok hall htot (eqP hwt).
have hbelow : safety_cond_below (size vs0) c.
+ by rewrite -hsz; apply: (safety_cond_type_below (eqP hwt)).
have -> : safety_cond_holds vs0 c = x by rewrite /safety_cond_holds hx.
by rewrite hsz; apply: (@safety_cond_holds_cond_init vs0 vs2 b c x hbelow hx).
Qed.

(* The mask seen by the generic construction under a guard: everything is
   defined when the guard is false, and the original mask otherwise. *)
Lemma cond_init_mask (ts : seq ctype) (vs0 : values) (init : seq safety_cond) (b : bool)
    (vs2 : values) (n : nat) :
  List.Forall2 (fun t v => exists x : sem_t t, v = to_val x) ts vs0 ->
  all safety_cond_total init -> all (safety_cond_wt ts) init ->
  size init = n ->
  map (safety_cond_holds (rcons vs0 (Vbool b) ++ vs2)) (map (cond_init (size ts)) init)
  = (if b then map (safety_cond_holds vs0) init else nseq n true).
Proof.
move=> hall htot hwt <-; rewrite cat_rcons.
elim: init htot hwt => [ | c init ih] /=; first by case: b.
move=> /andP [htc htot] /andP [hwc hwt].
rewrite (cond_init_val vs2 b hall htc hwc) (ih htot hwt) => {ih}.
by case: b.
Qed.


(* The safety conditions of a conditional instruction are the [Guarded] ones;
   under a false guard they all hold. *)
Lemma check_safe_cond_cat vs1 vs2 sc :
  ssrnat.leq (sc_needed_args sc) (size vs1) ->
  check_safe_cond (vs1 ++ vs2) sc = check_safe_cond vs1 sc.
Proof.
move=> h; apply/idP/idP => /check_safe_condP hc; apply/check_safe_condP.
+ by apply/(@interp_safe_cond_cat vs1 vs2 sc h).
by apply/(@interp_safe_cond_cat vs1 vs2 sc h).
Qed.

Lemma check_safe_cond_all_guarded (n : nat) (vs0 vs2 : values) (safe : seq safe_cond)
    (b : bool) :
  size vs0 = n ->
  all (fun sc => ssrnat.leq (sc_needed_args sc) n) safe ->
  all (check_safe_cond (rcons vs0 (Vbool b) ++ vs2)) (map (Guarded n) safe)
  = (if b then all (check_safe_cond vs0) safe else true).
Proof.
move=> hsz; rewrite cat_rcons -hsz.
elim: safe => [ | sc safe ih] /=.
+ by case: b.
move=> /andP [h1 h2]; rewrite nth_cat ltnn subnn /= (ih h2).
by case: b {ih} => //=; rewrite check_safe_cond_cat.
Qed.

Lemma sc_needed_args_guarded n sc :
  ssrnat.leq (sc_needed_args sc) n ->
  ssrnat.leq (sc_needed_args (Guarded n sc)) (S n).
Proof.
by move=> h; rewrite /= ssrnat.geq_max ssrnat.leqnn /=; apply: (ssrnat.leq_trans h).
Qed.

Lemma all_sc_needed_args_guarded n safe :
  all (fun sc => ssrnat.leq (sc_needed_args sc) n) safe ->
  all (fun sc => ssrnat.leq (sc_needed_args sc) (S n)) (map (Guarded n) safe).
Proof.
by move=> h; rewrite all_map; apply: sub_all h => sc; apply: sc_needed_args_guarded.
Qed.
