(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import finmap strings dmasm_utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.
Local Open Scope fset.
Local Open Scope fmap.

(* ** Types for idents and values
 * -------------------------------------------------------------------- *)

Definition wsize : nat := nosimpl 64.

Definition word := 'Z_(2^wsize).
Definition w2n (w : word) : nat := w.
Definition n2w (n : nat) : word :=  n%:R.

Lemma codeK_word : cancel w2n n2w.
Proof. rewrite /cancel /w2n /n2w => x. by rewrite natr_Zp. Qed.
Definition word_eqMixin     := comparableClass (@LEM word).
Canonical  word_eqType      := Eval hnf in EqType word word_eqMixin.
Definition word_choiceMixin := CanChoiceMixin codeK_word.
Canonical  word_choiceType  := ChoiceType word word_choiceMixin.

Inductive ident := Id of string.
Definition iname i := let: Id s := i in s.
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

Notation "st1 ** st2" := (sprod st1 st2) (at level 40, left associativity).

Inductive sop : stype -> stype -> Set :=
(* bools *)
| Oand  : sop (sbool ** sbool) sbool
| Onot  : sop sbool sbool
(* pairs *)
| Ofst  : forall st1 st2, sop (st1 ** st2) st1
| Osnd  : forall st1 st2, sop (st1 ** st2) st2
(* words *)
| Oadd  : sop (sword ** sword)          (sbool ** sword)
| Oaddc : sop (sword ** sword ** sbool) (sbool ** sword)
| Oeq   : sop (sword ** sword) sbool
| Olt   : sop (sword ** sword) sbool
(* arrays *)
| Oset  : forall n, sop (sarr n sword ** sword ** sword) (sarr n sword)
| Oget  : forall n, sop (sarr n sword ** sword)          sword.

Fixpoint st2ty (t : stype) : Type :=
  match t with
  | sword         => word
  | sbool         => bool
  | sprod st1 st2 => ((st2ty st1) * (st2ty st2))%type
  | sarr n st     => (n.+1).-tuple (st2ty st) (* do not allow zero-dim arrays *)
  end.

Inductive var : stype -> Set :=
| Var (st : stype) of ident : var st.

Inductive pexpr : stype -> Type :=
| Pvar   : forall st, var st -> pexpr st
| Pconst : st2ty sword -> pexpr sword
| Ppair  : forall st1 st2, pexpr st1 -> pexpr st2 -> pexpr (st1 ** st2)
| Papp   : forall starg stres: stype, sop starg stres -> pexpr starg -> pexpr stres.

Inductive rval : stype -> Set :=
| Rvar  : forall st, var st -> rval st
| Rpair : forall st1 st2, rval st1 -> rval st2 -> rval (st1 ** st2).

Inductive bcmd :=
| Assgn : forall st, rval st -> pexpr st -> bcmd
| Load  : rval sword -> pexpr sword -> bcmd
| Store : pexpr sword -> pexpr sword -> bcmd.

Inductive dir := UpTo | DownTo.

Definition range := (dir * pexpr sword * pexpr sword)%type.

Inductive cmd :=
| Cskip  : cmd
| Cbcmd  : bcmd -> cmd
| Cseq   : cmd -> cmd -> cmd
| Cif    : pexpr sbool -> cmd -> cmd -> cmd
| Cfor   : var sword -> range -> cmd -> cmd
| Ccall  : forall starg stres,
             rval starg -> pexpr stres -> cmd (* function def: (args, ret, body) *)
             -> rval  stres
             -> pexpr starg
             -> cmd.

Definition assgn st (rv : rval st) pe := Cbcmd (Assgn rv pe).
Definition load rv pe := Cbcmd (Load rv pe).
Definition store pe1 pe2 := Cbcmd (Store pe1 pe2).

(* ** Equality and choice
 * -------------------------------------------------------------------- *)

Definition eq_stype (st1 st2 : stype) : {st1 = st2} + {st1<>st2}.
Proof. do! (decide equality). Qed.

Parameter st2n : stype -> nat.
Parameter n2st : nat -> stype.
Lemma codeK_stype : cancel st2n n2st. Admitted.
Definition stype_eqMixin     := comparableClass (@LEM stype).
Canonical  stype_eqType      := Eval hnf in EqType stype stype_eqMixin.
Definition stype_choiceMixin := CanChoiceMixin codeK_stype.
Canonical  stype_choiceType  := ChoiceType stype stype_choiceMixin.

(* ** Default values
 * -------------------------------------------------------------------- *)

Fixpoint dflt (st : stype) : st2ty st :=
  match st with
  | sword         => n2w 0
  | sbool         => false
  | sprod st1 st2 => (dflt st1, dflt st2)
  | sarr n    st  => [tuple (dflt st) | i < n.+1]
  end.

Definition rdflt_ (st : stype) e (r : result e (st2ty st)) : st2ty st :=
  rdflt (dflt st) r.

(* ** More on variables 
 * -------------------------------------------------------------------- *)

Definition vname st (v : var st) :=
  let: Var _ s := v in s.

Record tvar := Tvar { tv_stype : stype; tv_ident : ident }.

Definition tvar2pair tv := (tv.(tv_stype), tv.(tv_ident)).
Definition pair2tvar p := Tvar (fst p) (snd p).
Lemma codeK_tvar : cancel tvar2pair pair2tvar. Proof. by rewrite /cancel; case => //. Qed.
Definition tvar_eqMixin     := comparableClass (@LEM tvar).
Canonical  tvar_eqType      := Eval hnf in EqType tvar tvar_eqMixin.
Definition tvar_choiceMixin := CanChoiceMixin codeK_tvar.
Canonical  tvar_choiceType  := ChoiceType tvar tvar_choiceMixin.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Definition g_vmap (to:stype -> Type) := forall (st : stype), {fmap ident -> to st}.

Definition g_vmap_set (to:stype -> Type) st (vm : g_vmap to) k (v : to st) : g_vmap to :=
  fun st' =>
     match eq_stype st st' with
     | left p_eq =>
         eq_rect st
           (fun st => {fmap ident -> to st})
           (vm st).[k <- v]
           st'
           p_eq
     | right _ => vm st'
     end.

Definition g_vmap0 to : g_vmap to:= fun st => fmap0.

Notation vmap     := (g_vmap st2ty).
Notation vmap_set := (@g_vmap_set st2ty _).
Notation vmap0    := (@g_vmap0 st2ty).

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Inductive error := ErrOob | ErrVarUndef | ErrAddrUndef | ErrAddrInvalid.

Definition exec t := result error t.
Definition ok := Ok error. 

Definition sem_sop st1 st2 (sop : sop st1 st2) : st2ty st1 -> exec (st2ty st2) :=
  match sop with
  | Oand       => fun (xy : bool * bool) => let (x,y) := xy in ok (x && y)
  | Onot       => fun b => ok (~~ b)
  | Ofst t1 t2 => fun (xy : (st2ty t1 * st2ty t2)) => ok (fst xy)
  | Osnd t1 t2 => fun (xy : (st2ty t1 * st2ty t2)) => ok (snd xy)
  | Oadd       => fun (xy : word * word) =>
                    let n := (fst xy + snd xy)%N in
                    ok (n >= 2^wsize,n%:R)
  | Oaddc      => fun (xy : word * word * bool) =>
                    let: (x,y,b) := xy in
                    let n := (x + y + b%N)%N in
                    ok (n >= 2^wsize,(w2n x + w2n y)%:R)
  | Oeq        => fun (xy : word * word) => let (x,y) := xy in ok (x == y)
  | Olt        => fun (xy : word * word) => let (x,y) := xy in ok (x < y)
  | Oget n     => fun (ai : (n.+1).-tuple word * word) =>
                    let (a,wi) := ai in
                    let i := w2n wi in
                    if i > n
                    then Error ErrOob
                    else ok (tnth a (@inZp n i))
  | Oset n     => fun (ai : (n.+1).-tuple word * word * word) =>
                    let: (a,wi,v) := ai in
                    let i := w2n wi in
                    if i > n
                    then Error ErrOob
                    else
                      ok [tuple (if j == inZp i then v else tnth a j) | j < n.+1]
  end.

Fixpoint sem_pexpr st (vm : vmap) (pe : pexpr st) : exec (st2ty st) :=
  match pe with
  | Pvar st v => o2r ErrVarUndef ((vm st).[? vname v])
  | Pconst c => ok c
  | Papp sta str so pe =>
      sem_pexpr vm pe >>= fun v =>
      (sem_sop so) v
  | Ppair st1 st2 pe1 pe2 =>
      sem_pexpr vm pe1 >>= fun v1 =>
      sem_pexpr vm pe2 >>= fun v2 =>
      ok (v1,v2)
  end.

(* ** Writing local variables
 * -------------------------------------------------------------------- *)

Section WRITE.

  Variable to : stype -> Type.
 
  Record g_tosubst  := ToSubst {
    ts_t  : stype;
    ts_id : ident;
    ts_to : to ts_t;
  }.

  Variable fst : forall {t1 t2:stype}, to (t1 ** t2) -> to t1.
  Variable snd : forall {t1 t2:stype}, to (t1 ** t2) -> to t2.

  Fixpoint g_write_subst {st} (l:rval st) : to st -> list g_tosubst -> list g_tosubst := 
    match l in rval st_ return to st_ -> list g_tosubst -> list g_tosubst with
    | Rvar st (Var _ vid) => fun v s =>  
      (ToSubst vid v) :: s
    | Rpair t1 t2 rv1 rv2 => fun v s => 
      g_write_subst rv2 (snd v) (g_write_subst rv1 (fst v) s)
    end.

End WRITE.

Definition write_subst := @g_write_subst st2ty (fun t1 t2 => fst) (fun t1 t2 => snd).

Definition write_vmap := 
  foldr (fun (ts:g_tosubst st2ty) vm => 
           let (t,id,v) := ts in
           vmap_set vm id v).

Definition write_rval {st} (vm:vmap) (l:rval st) (v:st2ty st) :=
   write_vmap vm (write_subst l v [::]).
  
(* ** Memory
 * -------------------------------------------------------------------- *)

Definition mem := {fmap word -> word}.

Variable valid_addr : word -> bool.

Definition read_mem (m : mem) (p : word) : exec word :=
  if valid_addr p
  then o2r ErrAddrUndef (m.[? p])
  else Error ErrAddrInvalid.

Definition write_mem (m : mem) (p w : word) : exec mem :=
  if valid_addr p
  then ok (m.[p <- w])
  else Error ErrAddrInvalid.

(* ** Variable occurences
 * -------------------------------------------------------------------- *)

Fixpoint vars_pexpr st (pe : pexpr st) :=
  match pe with
  | Pvar   _ (Var st vn)  => [fset (Tvar st vn)]
  | Pconst _           => fset0
  | Papp sta ste _ pe     => vars_pexpr pe
  | Ppair st1 st2 pe1 pe2 => vars_pexpr pe1 `|` vars_pexpr pe2
  end.

Fixpoint vars_rval st (rv : rval st) :=
  match rv with
  | Rvar  st (Var _ vn)   => [fset (Tvar st vn)]
  | Rpair st1 st2 rv1 rv2 => vars_rval rv1 `|` vars_rval rv2
  end.

Definition vars_bcmd (bc : bcmd) :=
  match bc with
  | Assgn st rv pe       => vars_rval  rv      `|` vars_pexpr pe
  | Load rv pe_addr      => vars_rval  rv      `|` vars_pexpr pe_addr
  | Store pe_addr pe_val => vars_pexpr pe_addr `|` vars_pexpr pe_val
  end.

Definition vars_range (r : range) :=
  let: (_,pe1,pe2) := r in
  vars_pexpr pe1 `|` vars_pexpr pe2.

Inductive recurse := Recurse | NoRecurse.

Fixpoint vars_cmd (rec : recurse) (c : cmd) :=
  match c with
  | Cskip => fset0
  | Cbcmd bc =>
      vars_bcmd bc
  | Cseq c1 c2 =>
      vars_cmd rec c1 `|` vars_cmd rec c2
  | Cif pe c1 c2 =>
      vars_pexpr pe `|` vars_cmd rec c1 `|` vars_cmd rec c2
  | Cfor (Var st vn) rng c =>
      (Tvar st vn) |` vars_range rng `|` vars_cmd rec c
  | Ccall starg stres rv_farg pe_ret c_body rv_res pe_arg =>
      (if rec is Recurse
       then vars_rval rv_farg `|` vars_pexpr pe_ret `|` vars_cmd rec c_body
       else fset0)
      `|` vars_rval rv_res `|` vars_pexpr pe_arg
  end.

Definition vars_fdef starg stres (rv : rval starg) (pe : pexpr stres) (c : cmd) :=
  vars_rval rv `|` vars_pexpr pe `|` vars_cmd NoRecurse c.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Definition sem_bcmd (es : estate) (bc : bcmd) : exec estate :=
  match bc with
  | Assgn st rv pe =>
      sem_pexpr es.(evm) pe >>= fun v =>
      let vm := write_rval es.(evm) rv v in
      ok (Estate es.(emem) vm)
  | Load rv pe_addr =>
      sem_pexpr es.(evm) pe_addr >>= fun p =>
      read_mem es.(emem) p >>= fun w =>
      let vm := write_rval es.(evm) rv w in
      ok (Estate es.(emem) vm)

  | Store pe_addr pe_val =>
      sem_pexpr es.(evm) pe_addr >>= fun p =>
      sem_pexpr es.(evm) pe_val  >>= fun w =>
      write_mem es.(emem) p w >>= fun m =>
      ok (Estate m es.(evm))
  end.

Definition wrange d n1 n2 :=
  let idxs := iota n1 (n2 - n1) in
  match d with
  | UpTo   => idxs
  | DownTo => rev idxs (* [seq (n1 + (n2 - n - 1))%nat | n <- idxs ] *)
  end.

Definition sem_range (vm : vmap) (r : range) :=
  let: (d,pe1,pe2) := r in
  sem_pexpr vm pe1 >>= fun w1 =>
  sem_pexpr vm pe2 >>= fun w2 =>
  let n1 := w2n w1 in
  let n2 := w2n w2 in
  ok [seq n2w n | n <- wrange d n1 n2].

Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
    sem s Cskip s

| Eseq s1 s2 s3 c1 c2 :
    sem s1 c1 s2 -> sem s2 c2 s3 -> sem s1 (Cseq c1 c2) s3

| Ebcmd s1 s2 c:
    sem_bcmd s1 c = ok s2 -> sem s1 (Cbcmd c) s2

| EifTrue s1 s2 (pe : pexpr sbool) c1 c2 :
    sem_pexpr s1.(evm) pe = ok true ->
    sem s1 c1 s2 ->
    sem s1 (Cif pe c1 c2) s2

| EifFalse s1 s2 (pe : pexpr sbool) c1 c2 :
    sem_pexpr s1.(evm) pe = ok false ->
    sem s1 c2 s2 ->
    sem s1 (Cif pe c1 c2) s2

| Ecall {m1 m2 vm1} vmc1 {vmc2 starg stres farg fres fbody rv_res pe_arg} :
    isOk (@sem_pexpr starg vm1 pe_arg) ->
    let arg := rdflt_ (@sem_pexpr starg vm1 pe_arg) in
    (* forall st vn, Tvar st vn \in vars_fdef farg fres fbody -> vn \in domf (vm1 st)) ->  *)
    let vmc1 := @write_rval starg vmc1 farg arg in
    sem (Estate m1 vmc1) fbody (Estate m2 vmc2) ->
    isOk (@sem_pexpr stres vmc2 fres) ->
    let res := rdflt_ (@sem_pexpr stres vmc2 fres) in
    let vm2 := @write_rval stres vm1 rv_res res in
    sem (Estate m1 vm1)
        (@Ccall starg stres farg fres fbody rv_res pe_arg)
        (Estate m2 vm2)

| EforDone s1 s2 iv rng c ws :
    sem_range s1.(evm) rng = ok ws ->
    sem_for iv ws s1 c s2 ->
    sem s1 (Cfor iv rng c) s2

with sem_for : var sword -> seq word -> estate -> cmd -> estate -> Prop :=

| EForDone s c iv :
    sem_for iv [::] s c s

| EForOne s1 s2 s3 c w ws iv :
    let ac := Cseq (Cbcmd (Assgn (Rvar iv) (Pconst w))) c in
    sem                s1 ac s2 ->
    sem_for iv (ws)    s2 c  s3 ->
    sem_for iv (w::ws) s1 c  s3.
