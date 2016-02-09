(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
Require Import choice fintype eqtype div seq finmap strings zmodp.
Require Import dmasm_utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope fset.
Local Open Scope fmap.

Section Sem.

(* ** Types for idents and values
 * -------------------------------------------------------------------- *)

Definition wsize : nat := nosimpl 64.

Definition word := 'Z_(2^wsize).
Definition w2n (w : word) : nat := w.
Definition n2w (n : nat) : word :=  n%:R.

Lemma codeK_word : cancel w2n n2w. Proof. rewrite /cancel /w2n /n2w => x. by rewrite natr_Zp. Qed.
Definition word_eqMixin     := comparableClass (@LEM word).
Canonical  word_eqType      := Eval hnf in EqType word word_eqMixin.
Definition word_choiceMixin := CanChoiceMixin codeK_word.
Canonical  word_choiceType  := ChoiceType word word_choiceMixin.

Inductive ident := Id of string.
Definition iname i := match i with Id s => s end.
Lemma codeK_ident : cancel iname Id. Proof. by rewrite /cancel; case => //. Qed.
Definition ident_eqMixin     := comparableClass (@LEM ident).
Canonical  ident_eqType      := Eval hnf in EqType ident ident_eqMixin.
Definition ident_choiceMixin := CanChoiceMixin codeK_ident.
Canonical  ident_choiceType  := ChoiceType ident ident_choiceMixin.

(* ** Syntax
 * -------------------------------------------------------------------- *)

(* more expressive than required, but leads to simpler definitions *)
Inductive stype : Set :=
| sword : stype
| sbool : stype
| sprod : stype -> stype -> stype
| sarr  : forall (n : nat), stype -> stype.

Inductive var (st : stype) : Type :=
| Var : ident -> var st.

Inductive sop : stype -> stype -> Set :=
| Move : forall st, sop st st
| Fst  : forall st1 st2, sop (sprod st1 st2) st1
| Snd  : forall st1 st2, sop (sprod st1 st2) st2
| Add  : sop (sprod sword sword)               (sprod sbool sword)
| Addc : sop (sprod sword (sprod sword sbool)) (sprod sbool sword).

Fixpoint st2ty (t : stype) : Type :=
  match t with
  | sword         => word
  | sbool         => bool
  | sprod st1 st2 => ((st2ty st1) * (st2ty st2))%type
  | sarr n st     => (n.+1).-tuple (st2ty st) (* do not allow zero-dim arrays *)
  end.

Inductive pexpr (st : stype) :=
| Pvar   : var st -> pexpr st
| Pconst : st2ty st -> pexpr st
| Papp   : forall starg : stype, sop starg st -> pexpr starg -> pexpr st.

Inductive loc (st : stype) :=
| Lvar : var st -> loc st
| Aget : forall n : nat, var (sarr n st) -> pexpr sword -> loc st.

Inductive src (st : stype) : Type :=
| Imm : pexpr st -> src st
| Loc : loc   st -> src st.

Inductive bcmd :=
| Assgn : forall starg stres, loc stres -> sop starg stres -> src starg -> bcmd
| Load  : loc sword -> pexpr sword -> bcmd
| Store : pexpr sword -> src sword -> bcmd.

Inductive dir := UpTo | DownTo.

Definition range := (dir * pexpr sword * pexpr sword)%type.

Inductive cmd :=
| Sskip  : cmd
| Sbcmd  : bcmd -> cmd
| Sseq   : cmd -> cmd -> cmd
| Sif    : pexpr sbool -> cmd -> cmd -> cmd
| Sfor   : var sword -> range -> cmd -> cmd
| Scall  : forall starg stres,
             var starg -> src stres -> cmd (* function def: (args, ret, body) *)
             -> var stres
             -> src starg
             -> cmd.

(* ** Check if we really need this
 * -------------------------------------------------------------------- *)

(*
Definition stype_eqMixin := comparableClass (@LEM stype).
Canonical  stype_eqType  := Eval hnf in EqType stype stype_eqMixin.
*)

(* ** Variables and typed finite maps
 * -------------------------------------------------------------------- *)

Definition vname st (v : var st) :=
  let: Var s := v in s.

Definition vmap := forall (st : stype), {fmap ident -> st2ty st}.
Definition vmap_set st (tm : vmap) k (v : st2ty st) :=
  fun st' =>
     match LEM st st' with
     | left p_eq =>
         eq_rect st
           (fun st => {fmap ident -> st2ty st})
           (tm st).[k <- v]
           st'
           p_eq
     | right _ => tm st'
     end.
Definition vmap0 : vmap := fun st => fmap0.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition sem_pexpr st (vm : vmap) (pe : pexpr st) : result (st2ty st) :=
  admit.

(* ** Reading local variables
 * -------------------------------------------------------------------- *)

Definition read_loc st (vm : vmap) (l : loc st) : result (st2ty st) :=
  match l with
  | Lvar (Var vid) =>
      o2r "IdUndef" ((vm st).[? vid])
  | Aget n (Var vid) pe =>
      o2r "IdUndef" ((vm (sarr n st)).[? vid]) >>= fun (a : (n.+1).-tuple (st2ty st)) =>
      sem_pexpr vm pe >>= fun w =>
      let nw := w2n w in
      if nw > n
      then Error "OutOfBounds"
      else Ok (tnth a (@inZp n nw))
  end.

Definition read_src st (vm : vmap) (s : src st) : result (st2ty st) :=
  match s with
  | Imm pe => sem_pexpr vm pe >>= fun w => Ok w
  | Loc d  => read_loc vm d
  end.

(* ** Writing local variables
 * -------------------------------------------------------------------- *)

Definition write_loc st (vm : vmap) (l : loc st) (v : st2ty st)
    : result vmap :=
  match l with
  | Lvar (Var vid) => Ok (vmap_set vm vid v)
  | Aget n (Var vid) pe =>
      sem_pexpr vm pe >>= fun w =>
      o2r "IdUndef" (vm (sarr n st)).[? vid] >>= fun a =>
      let nw := w2n w in
      if nw > n
      then Error "OutOfBounds"
      else (
        let a' := [tuple (if i == inZp nw then v else tnth a i) | i < n.+1] in
        Ok (@vmap_set (sarr n st) vm vid a')
      )
  end.

(* ** Memory
 * -------------------------------------------------------------------- *)

Definition mem := {fmap word -> word}.

Variable valid_addr : word -> bool.

Definition read_mem (m : mem) (p : word) : result word :=
  if valid_addr p then (
    o2r "read_mem: address undefined" (m.[? p])
  ) else (
    Error "read_mem: invalid address"
  ).

Definition write_mem (m : mem) (p w : word) : result mem :=
  if valid_addr p then (
    Ok (m.[p <- w])
  ) else (
    Error "read_mem: invalid address"
  ).

(* ** Instructions
 * -------------------------------------------------------------------- *)

Definition sem_sop (sarg sret : stype) : st2ty sarg -> st2ty sret := admit.

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition sem_bcmd (es : estate) (bc : bcmd) : result estate :=
  match bc with
  | Assgn starg stres d op s =>
      read_src es.(evm) s >>= fun args =>
      let: res := sem_sop stres args in
      write_loc es.(evm) d res >>= fun vm =>
      Ok (Estate es.(emem) vm)

  | Load loc pe_addr =>
      sem_pexpr es.(evm) pe_addr >>= fun p =>
      read_mem es.(emem) p >>= fun w =>
      write_loc es.(evm) loc w >>= fun vm =>
      Ok (Estate es.(emem) vm)

  | Store pe_addr src =>
      sem_pexpr es.(evm) pe_addr >>= fun p =>
      read_src es.(evm) src >>= fun w =>
      write_mem es.(emem) p w >>= fun m =>
      Ok (Estate m es.(evm))
  end.

Definition wrange d n1 n2 :=
  let idxs := iota n1 (n2 - n1) in
  match d with
  | UpTo   => idxs
  | DownTo => [seq (n1 + (n2 - n - 1))%nat | n <- idxs ]
  end.

Definition sem_range (vm : vmap) (r : range) :=
  let: (d,pe1,pe2) := r in
  sem_pexpr vm pe1 >>= fun w1 =>
  sem_pexpr vm pe2 >>= fun w2 =>
  let n1 := w2n w1 in
  let n2 := w2n w2 in
  Ok [seq n2w n | n <- wrange d n1 n2].

Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
    sem s Sskip s

| Eseq s1 s2 s3 c1 c2 :
    sem s1 c1 s2 -> sem s2 c2 s3 -> sem s1 (Sseq c1 c2) s3

| Ebcmd s1 s2 c:
    sem_bcmd s1 c = Ok s2 -> sem s1 (Sbcmd c) s2

| EifTrue s1 s2 (pe : pexpr sbool) c1 c2 :
    sem_pexpr s1.(evm) pe = Ok true ->
    sem s1 c1 s2 ->
    sem s1 (Sif pe c1 c2) s2

| EifFalse s1 s2 (pe : pexpr sbool) c1 c2 :
    sem_pexpr s1.(evm) pe = Ok false ->
    sem s1 c2 s2 ->
    sem s1 (Sif pe c1 c2) s2

| Ecall m1 m2 vm1 vmc1 vmc2 vm2 starg stres farg fres fbody dres sarg arg res :
    read_src vmc1 sarg = Ok arg -> (* FIXME: we should also enforce that vmc1 *)
    sem (Estate m1 vmc1) fbody (Estate m2 vmc2) ->  (* defined on occ fbody   *)
    read_src vmc2 fres = Ok res ->
    write_loc vm1 (Lvar dres) res = Ok vm2 ->
    sem (Estate m1 vm1)
        (@Scall starg stres farg fres fbody dres sarg)
        (Estate m2 vm2)

| EforDone s1 s2 iv rng c ws :
    sem_range s1.(evm) rng = Ok ws ->
    sem_for iv ws s1 c s2 ->
    sem s1 (Sfor iv rng c) s2

with sem_for : var sword -> seq word -> estate -> cmd -> estate -> Prop :=

| EForDone s c iv :
    sem_for iv [::] s c s

| EForOne s1 s2 s3 c w ws iv :
    let ac := Sseq (Sbcmd (Assgn (Lvar iv) (Move sword) (Imm (Pconst w)))) c in
    sem                s1 ac s2 ->
    sem_for iv (ws)    s2 c  s3 ->
    sem_for iv (w::ws) s1 c  s3.

End Sem.