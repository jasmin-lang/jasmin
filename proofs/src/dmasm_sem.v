(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
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

Variable word : Set.
Variable w2n : word -> nat.
Variable n2w : nat -> word.

Lemma codeK_word : cancel w2n n2w. Admitted.
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

(* ** Source language types
 * -------------------------------------------------------------------- *)

(* more expressive than required, but leads to simpler definitions *)
Inductive stype : Set :=
| sword : stype
| sbool : stype
| sprod : stype -> stype -> stype
| sarr  : stype -> stype.

Definition stype_eqMixin := comparableClass (@LEM stype).
Canonical  stype_eqType  := Eval hnf in EqType stype stype_eqMixin.

Fixpoint type_of_stype (t : stype) : Type :=
  match t with
  | sword         => word
  | sbool         => bool
  | sprod st1 st2 => ((type_of_stype st1) * (type_of_stype st2))%type
  | sarr st       => {fmap word -> (type_of_stype st)}
  end.

(* ** Typed finite maps
 * -------------------------------------------------------------------- *)

Definition amap (st : stype) := {fmap word -> type_of_stype st}.
Definition amap0 (st : stype) : amap st := fmap0.

Definition vmap := forall (st : stype), {fmap ident -> type_of_stype st}.
Definition vmap_set st (tm : vmap) k (v : type_of_stype st) :=
  fun st' =>
     match LEM st st' with
     | left p_eq =>
         eq_rect st
           (fun st => {fmap ident -> type_of_stype st})
           (tm st).[k <- v]
           st'
           p_eq
     | right _ => tm st'
     end.
Definition vmap0 : vmap := fun st => fmap0.

(* ** Variables
 * -------------------------------------------------------------------- *)

Inductive var (st : stype) : Type :=
| Var : ident -> var st.

Definition vname st (v : var st) :=
  let: Var s := v in s.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Variable pexpr : stype -> Set.

Definition pconst st (v : type_of_stype st) : pexpr st := admit.
Definition sem_pexpr st (vm : vmap) (pe : pexpr st) : result (type_of_stype st) :=
  admit.

(* ** Locations and sources
 * -------------------------------------------------------------------- *)

Inductive loc (st : stype) :=
| Lvar : var st -> loc st
| Aget : var (sarr st) -> pexpr sword -> loc st.

Inductive src (st : stype) : Type :=
| Imm : pexpr st -> src st
| Loc : loc st   -> src st.

(* ** Reading local variables
 * -------------------------------------------------------------------- *)

Definition read_loc st (vm : vmap) (l : loc st) : result (type_of_stype st) :=
  match l with
  | Lvar (Var vid) =>
      o2r "IdUndef" ((vm st).[? vid])
  | Aget (Var vid) pe =>
      o2r "IdUndef" ((vm (sarr st)).[? vid]) >>= fun (a : amap st) =>
      sem_pexpr vm pe >>= fun w =>
      o2r "IdxUndef" (a.[? w])
  end.

Definition read_src st (vm : vmap) (s : src st) : result (type_of_stype st) :=
  match s with
  | Imm pe => sem_pexpr vm pe >>= fun w => Ok w
  | Loc d  => read_loc vm d
  end.

(* ** Writing local variables
 * -------------------------------------------------------------------- *)

Definition write_loc st (vm : vmap) (l : loc st) (v : type_of_stype st)
    : result vmap :=
  match l with
  | Lvar (Var vid) => Ok (vmap_set vm vid v)
  | Aget (Var vid) pe =>
      sem_pexpr vm pe >>= fun w =>
      let a := odflt (amap0 st) ((vm (sarr st)).[? vid]) in
      Ok (@vmap_set (sarr st) vm vid (a.[w <- v]))
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

Definition sop st_in st_out := type_of_stype st_in -> type_of_stype st_out.

Inductive dir := UpTo | DownTo.

Inductive bcmd :=
| Assgn : forall starg stres, loc stres -> sop starg stres -> src starg -> bcmd
| Load  : loc sword -> pexpr sword -> bcmd
| Store : pexpr sword -> src sword -> bcmd.

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition sem_bcmd (es : estate) (bc : bcmd) : result estate :=
  match bc with
  | Assgn sto sti d op s =>
      read_src es.(evm) s >>= fun args =>
      let: res := op args in
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

Definition range := (dir * pexpr sword * pexpr sword)%type.

Definition sem_range (vm : vmap) (r : range) :=
  let: (d,pe1,pe2) := r in
  Ok (map n2w (iota 0 10)). (* FIXME *)

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
    let ac := Sseq (Sbcmd (Assgn (Lvar iv) id (Imm (pconst w)))) c in
    sem                s1 ac s2 ->
    sem_for iv (ws)    s2 c  s3 ->
    sem_for iv (w::ws) s1 c  s3.

End Sem.