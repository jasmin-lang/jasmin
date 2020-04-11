(* ** Imports and settings *)
From CoqWord Require Import ssrZ.
Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.

Definition var := nat.

Inductive expr :=
 | Ebool `(bool)
 | Evar  `(var)
 | Eand  `(expr) `(expr).

Inductive leak :=
  | Lempty 
  | Lv     `(var)
  | Land   `(leak) `(leak).

Definition vmap := var -> bool.

Fixpoint sem_e (vm:vmap) (e:expr) : bool * leak := 
  match e with
  | Ebool b => (b, Lempty)
  | Evar x  => (vm x, Lv x)
  | Eand e1 e2 => 
    let vl1 := sem_e vm e1 in 
    let vl2 := sem_e vm e2 in
    (vl1.1 && vl2.1, Land vl1.2 vl2.2)
  end.
 
Definition is_bool e := 
  match e with
  | Ebool b => Some b
  | _       => None
  end.
 
Definition sand e1 e2 :=
  match is_bool e1, is_bool e2 with
  | Some b, _ => if b then e2 else Ebool false
  | _, Some b => if b then e1 else Ebool false 
  | _, _      => Eand e1 e2
  end.

Fixpoint compile e := 
  match e with
  | Ebool _ => e
  | Evar _  => e
  | Eand e1 e2 => sand (compile e1) (compile e2)
  end.

(* Exercice prove correctness of the compiler *)

Lemma is_boolP e b : is_bool e = Some b -> e = Ebool b.
Admitted.

Lemma sandP vm e1 e2 : 
  (sem_e vm (Eand e1 e2)).1 = (sem_e vm (sand e1 e2)).1.
Proof.
  rewrite /sand.
  case heq1 : (is_bool e1) => [b1 | ].
  + by have -> /= := is_boolP heq1; case: (b1).     
  case heq2 : (is_bool e2) => [b2 | //].
  by have -> /= := is_boolP heq2; case: (b2); rewrite ?andbT ?andbF.
Qed.

Lemma compileP e vm: 
   (sem_e vm e).1 = (sem_e vm (compile e)).1.
Proof.
  elim:e => //= e1 he1 e2 he2.
  by rewrite he1 he2 -sandP.
Qed.

(* Add leakage *)

Inductive leak_tr :=
 | LTid 
 | LTremove 
 | LTsub1
 | LTsub2
 | LTsub     `(leak_tr) `(leak_tr)
 | LTcompose `(leak_tr) `(leak_tr).


Definition sand_l e1 e2 :=
  match is_bool e1, is_bool e2 with
  | Some b, _ => if b then (e2, LTsub2) else (Ebool false, LTremove)
  | _, Some b => if b then (e1, LTsub1) else (Ebool false, LTremove)
  | _, _      => (Eand e1 e2, LTid)
  end.

Fixpoint compile_l e := 
  match e with
  | Ebool _ => (e, LTid)
  | Evar _  => (e, LTid)
  | Eand e1 e2 => 
    let elt1 := compile_l e1 in
    let elt2 := compile_l e2 in
    let eltand:= sand_l elt1.1 elt2.1 in
    (eltand.1, LTcompose (LTsub elt1.2 elt2.2) eltand.2)
  end.

Fixpoint leak_F (t:leak_tr) (l:leak)  : leak := 
  match t, l with
  | LTid, _ => l
  | LTremove, _ => Lempty
  | LTsub1, Land l1 l2 => l1
  | LTsub2, Land l1 l2 => l2
  | LTsub t1 t2, Land l1 l2 => Land (leak_F t1 l1) (leak_F t2 l2)
  | LTcompose t1 t2, _ => leak_F t2 (leak_F t1 l) 
  | _, _ => Lempty (* absurd cases *)
  end.

Definition trans_sem t (vl:bool * leak) := (vl.1, leak_F t vl.2).

Lemma surj_pairing {T1 T2:Type} (p:T1 * T2) : (p.1,p.2) = p. 
Proof. by case: p. Qed.
Hint Resolve surj_pairing.

Lemma sand_lP vm e1 e2: 
  let e := (sand_l e1 e2).1 in
  let t := (sand_l e1 e2).2 in
  trans_sem t (sem_e vm (Eand e1 e2)) = sem_e vm e.
Proof.
  rewrite /sand_l /trans_sem.
  case heq1 : (is_bool e1) => [b1 | ].
  + by have -> /= := is_boolP heq1; case: (b1) => /=. 
  case heq2 : (is_bool e2) => [b2 | //].
  by have -> /= := is_boolP heq2; case: (b2); rewrite ?andbT ?andbF /=.
Qed.

Lemma compile_lP e vm: 
  let e' := (compile_l e).1 in
  let t  := (compile_l e).2 in
  trans_sem t (sem_e vm e) = sem_e vm e'.
Proof.
  elim:e => //= e1 he1 e2 he2.
  by rewrite -sand_lP /= -he1 -he2 /trans_sem /=.
Qed.

Inductive leak_base :=
  | Lbv     `(var).

Definition leak' := seq leak_base.

Fixpoint sem_e' (vm:vmap) (e:expr) : bool * leak' := 
  match e with
  | Ebool b => (b, [::])
  | Evar x  => (vm x, [::Lbv x])
  | Eand e1 e2 => 
    let vl1 := sem_e' vm e1 in 
    let vl2 := sem_e' vm e2 in
    (vl1.1 && vl2.1, vl1.2 ++ vl2.2)
  end.

Fixpoint flatten_lt (l:leak) := 
  match l with 
  | Lempty => [::]
  | Lv x   => [::Lbv x]
  | Land l1 l2 => flatten_lt l1 ++ flatten_lt l2
  end.
  
Lemma foo vm e v l : 
  sem_e vm e = (v, l) ->
  sem_e' vm e = (v, flatten_lt l).
Proof.
Admitted.

Lemma foo' vm e v l' : 
  sem_e' vm e = (v, l') ->
  exists l, l' = flatten_lt l /\ sem_e vm e = (v, l).
Proof.
Admitted.




