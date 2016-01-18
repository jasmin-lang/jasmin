(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice fintype.
Require Import div seq ssralg ssrint zmodp finmap ssrring.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Local Scope ring_scope.

(* -------------------------------------------------------------------- *)
Parameter ident : countType.

(* -------------------------------------------------------------------- *)
Axiom LEM : forall {T : Type}, forall (x y : T), {x=y}+{x<>y}.

(* -------------------------------------------------------------------- *)
Definition obind1 {A B : Type} (f : A -> option A) (v : option (A * B)) :=
  if v is Some (x, y) then
    if f x is Some x then Some (x, y) else None
  else None.

Definition obind2 {A B : Type} (f : B -> option B) (v : option (A * B)) :=
  if v is Some (x, y) then
    if f y is Some y then Some (x, y) else None
  else None.

(* -------------------------------------------------------------------- *)
(* Definition word := nosimpl 'I_(2^64). FIXME: abstract this *)
Parameter word : ringType.

Parameter w2n : word -> nat.
Parameter wsz : nat.

(* -------------------------------------------------------------------- *)
Module Type IArray.
Parameter T : Type.

Parameter get : T -> word -> option word.
Parameter set : T -> word -> word -> option T.
End IArray.

(* -------------------------------------------------------------------- *)
Module Array : IArray.
Definition T := (word -> word).

Definition get (a : T) (w : word) := Some (a w).

Definition set (a : T) (w x : word) :=
  Some (fun w' => if w == w' then x else a w).
End Array.

Notation array := Array.T.

(* -------------------------------------------------------------------- *)
Inductive stype : Type := TBool | TU64 | TArray of nat.

Inductive sop :=
  OGet | OSet | OAdd | OAddCarry.

Inductive sctt :=
  CBool of bool | CU64 of word.

Inductive sexpr : Type :=
  | ECtt of sctt
  | EVar of ident
  | EApp of sop & seq sexpr.

Inductive stmt : Type :=
  | SSkip
  | SSeq    of stmt & stmt
  | SAssign of seq ident & sexpr
  | SCall   of seq ident & ident & seq sexpr
  | SIf     of sexpr & stmt & stmt
  | SFor    of ident & (sexpr * sexpr) & stmt
  | SLoad   of ident & sexpr
  | SStore  of sexpr & sexpr.

(* -------------------------------------------------------------------- *)
Definition stype_eqMixin := comparableClass (@LEM stype).
Canonical  stype_eqType  := Eval hnf in EqType stype stype_eqMixin.

Definition sexpr_eqMixin := comparableClass (@LEM sexpr).
Canonical  sexpr_eqType  := Eval hnf in EqType sexpr sexpr_eqMixin.

(* -------------------------------------------------------------------- *)
Section SExpr.
  Variable P : sexpr -> Prop.

  Hypothesis PVar :
    forall x, P (EVar x).

  Hypothesis PApp :
    forall o es, (forall e, e \in es -> P e) -> P (EApp o es).

  Lemma sexpr_ind' : forall e, P e.
  Proof using PVar PApp. admit. Qed.
End SExpr.

(* -------------------------------------------------------------------- *)
Definition etype (t : stype) : Type :=
  match t with
  | TBool    => bool
  | TU64     => word
  | TArray n => (int -> word)
  end.

(* -------------------------------------------------------------------- *)
Inductive bvalue : Type :=
  | VBool  of bool
  | VU64   of word
  | VArray of array.

Definition bv2t (bv : bvalue) : stype :=
  match bv with
  | VBool  _ => TBool
  | VU64   _ => TU64
  | VArray _ => TArray 0
  end.

Notation value := (seq bvalue).

Definition lmem := ident -> option bvalue.
Definition gmem := word -> word.

Notation mem := (gmem * lmem)%type.

(* -------------------------------------------------------------------- *)
Definition asbool (v : value) :=
  if v is [:: VBool b] then Some b else None.

Definition asword (v : value) :=
  if v is [:: VU64 w] then Some w else None.

Definition asarray (v : value) :=
  if v is [:: VArray a] then Some a else None.

(* -------------------------------------------------------------------- *)
Definition upd (xv : ident * bvalue) (m : lmem) : option lmem :=
  if m xv.1 is Some v then
     if bv2t xv.2 == bv2t v then
       Some (fun y => Some (if y == xv.1 then xv.2 else v))
     else None
  else None.

Definition gupd (sd : word * word) (g : gmem) : gmem :=
  fun i => if i == sd.1 then sd.2 else g i.

(* -------------------------------------------------------------------- *)
Definition upds idvs (m : lmem) :=
  foldr (fun xv m => obind (upd xv) m) (Some m) idvs.

(* -------------------------------------------------------------------- *)
Definition value_of_ctt (c : sctt) : bvalue :=
   match c with
   | CBool b => VBool b
   | CU64  w => VU64  w
   end.

Definition b2v (v : bvalue) : value := [:: v].

Definition v2b (v : value) :=
  if v is [:: b] then Some b else None.

Definition eapp (o : sop) (vs : seq bvalue) : option value :=
  match o, vs with
  | OGet, [:: VArray a; VU64 i] =>
      omap (b2v \o VU64) (Array.get a i)

  | OSet, [:: VArray a; VU64 i; VU64 v] =>
      omap (b2v \o VArray) (Array.set a i v)

  | OAdd, [:: VU64 x; VU64 y] =>
      Some [:: VU64 (x + y : word)]

  | OAddCarry, [:: VU64 x; VU64 y; VBool c] =>
      let n : nat := (w2n x + w2n y + c)%N in
      Some [:: VBool (n < 2^wsz); (VU64 n%:R)]

  | _, _ => None
  end.

Fixpoint esem (m : lmem) (e : sexpr) : option value :=
  match e with
  | ECtt c => Some [:: value_of_ctt c]
  | EVar x => omap b2v (m x)

  | EApp o es =>
      let vs := pmap v2b (pmap (esem m) es) in
      if size vs < size es then None else eapp o vs
  end.

(* -------------------------------------------------------------------- *)
Inductive sem : mem -> stmt -> mem -> Prop :=
| ESkip m : sem m SSkip m

| ESeq m2 m1 m3 s1 s2 :
    sem m1 s1 m2 -> sem m2 s2 m3 -> sem m1 (SSeq s1 s2) m3

| EAssign (g : gmem) (m m' : lmem) (ids : seq ident) (e : sexpr) (vs : value) :
      esem m e = Some vs
    -> size ids = size vs
    -> Some m'  = foldr (fun xv m => obind (upd xv) m) (Some m) (zip ids vs)
    -> sem (g, m) (SAssign ids e) (g, m')

| EIfTrue g g' m m' c s1 s2 :
      esem m c = Some [:: VBool true]
    -> sem (g, m) s1 (g', m')
    -> sem (g, m) (SIf c s1 s2) (g', m')

| EIfFalse g g' m m' c s1 s2 :
      esem m c = Some [:: VBool false]
    -> sem (g, m) s2 (g', m')
    -> sem (g, m) (SIf c s1 s2) (g', m')

| EFor g g' m m' x e1 e2 i1 i2 s :
    (* FIXME: `x` decl. should be added to the memory *)

    let ids := [seq x%:R | x <- iota (w2n i1) (w2n i2 - w2n i1)] in
      esem m e1 = Some [:: VU64 i1]
    -> esem m e2 = Some [:: VU64 i2]
    -> sem_for x ids (g, m) s (g', m')
    -> sem (g, m) (SFor x (e1, e2) s) (g', m')

| ELoad (g : gmem) (m m' : lmem) x e i :
      esem m e = Some [:: VU64 i]
    -> Some m' = upd (x, VU64 (g i)) m
    -> sem (g, m) (SLoad x e) (g, m')

| EStore (g : gmem) (m : lmem) (s d : sexpr) si di :
     esem m s = Some [:: VU64 si]
   -> esem m d = Some [:: VU64 di]
   -> sem (g, m) (SStore s d) (gupd (si, di) g, m)

with sem_for : ident -> seq word -> mem -> stmt -> mem -> Prop :=
| EForDone g m s x :
   sem_for x [::] (g, m) s (g, m)

| EForOne m1 m2 m3 s x i r :
     let xs := SSeq (SAssign [:: x] (ECtt (CU64 i))) s in

     sem m1 s m2
   -> sem_for x r m2 xs m3
   -> sem_for x (i::r) m1 s m3
.

(* -------------------------------------------------------------------- *)
Fixpoint csem_n (n : nat) (s : stmt) {struct n} :=
  let fix csem_r (s : stmt) {struct s} := fun (gm : mem) =>
    match s return option mem with
    | SSkip =>
        Some gm
  
    | SSeq s1 s2 =>
        obind (csem_r s2) (csem_r s1 gm)
  
    | SAssign ids e =>
        if esem gm.2 e is Some vs then
          if size ids == size vs then
            obind2 (upds (zip ids vs)) (Some gm)
          else None
        else None
  
    | SIf e s1 s2 =>
        obind
          (fun b => csem_r (if b then s1 else s2) gm)
          (obind asbool (esem gm.2 e))
  
    | SLoad x e =>
        obind
          (fun i => obind2 (upd (x, VU64 (gm.1 i))) (Some gm))
          (obind asword (esem gm.2 e))
  
    | SStore s d =>
        let s := obind asword (esem gm.2 s) in
        let d := obind asword (esem gm.2 d) in
  
        omap
          (fun sd => (gupd sd gm.1, gm.2))
          (if (s, d) is (Some s, Some d) then Some (s, d) else None)
  
    | SFor x (e1, e2) s =>
        (* FIXME: push `x` into the memory first *)
        let fix fsem (r : seq word) gm :=
          if r is i :: r then
            let gm := obind2 (upd (x, VU64 i)) (Some gm) in
            let gm := obind  (csem_r s) gm in
            let gm := obind  (fsem r) gm in
            gm
          else Some gm in
  
        match esem gm.2 e1, esem gm.2 e2 with
        | Some [:: VU64 i1], Some [:: VU64 i2] =>
            let: (i1, i2) := (w2n i1, w2n i2) in
            let: rg := [seq x%:R | x <- iota i1 (i2 - i1)] in
            fsem rg gm
        | _, _ => None
        end
  
    | (SCall ids f args) as s =>
        if n is p.+1 then csem_n p s gm else None
    end

  in csem_r s.

(* -------------------------------------------------------------------- *)
Definition csem (gm : mem) (s : stmt) (gm' : mem) :=
  exists n, csem_n n s gm = Some gm'.
