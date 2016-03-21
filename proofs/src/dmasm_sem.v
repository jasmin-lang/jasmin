(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import finmap strings word dmasm_utils dmasm_type dmasm_var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.

(* ** Syntax
 * -------------------------------------------------------------------- *)

Inductive sop1 : stype -> stype -> Set := 
(* bools *)
| Onot  : sop1 sbool sbool
(* words *)
(*| Olnot : sop1 sword sword *)
(* pairs *)
| Ofst  : forall st1 st2, sop1 (st1 ** st2) st1
| Osnd  : forall st1 st2, sop1 (st1 ** st2) st2.

Inductive sop2 : stype -> stype -> stype -> Set :=
(* bools *)
| Oand  : sop2 sbool sbool sbool
| Oor   : sop2 sbool sbool sbool
(* words *)
| Oadd  : sop2 sword sword (sbool ** sword)
(*| Oxor  : sop2 sword sword sword
| Oland : sop2 sword sword sword
| Olor  : sop2 sword sword sword *)
| Oeq   : sop2 sword sword sbool
| Olt   : sop2 sword sword sbool
(* arrays *)
| Oget  : forall n, sop2 (sarr n sword) sword sword
(* pairs *)
| Opair : forall st1 st2, sop2 st1 st2 (st1 ** st2).

Inductive sop3 : stype -> stype -> stype -> stype -> Set :=
(* words *)
| Oaddc : sop3 sword sword sbool (sbool ** sword)
(* arrays *)
| Oset  : forall n, sop3 (sarr n sword) sword sword (sarr n sword).

Inductive pexpr : stype -> Type :=
| Pvar   :> forall x:var, pexpr x.(vtype)
| Pconst :> N -> pexpr sword
| Papp1  : forall st1 stres: stype, 
  sop1 st1 stres -> pexpr st1 -> pexpr stres
| Papp2  : forall st1 st2 stres: stype, 
  sop2 st1 st2 stres -> pexpr st1 -> pexpr st2 -> pexpr stres
| Papp3  : forall st1 st2 st3 stres: stype, 
  sop3 st1 st2 st3 stres -> pexpr st1 -> pexpr st2 -> pexpr st3 -> pexpr stres.

Inductive bcmd :=
| Assgn : forall st, rval st -> pexpr st -> bcmd
| Load  : rval sword -> pexpr sword -> bcmd
| Store : pexpr sword -> pexpr sword -> bcmd.

Inductive dir := UpTo | DownTo.

Definition range := (dir * pexpr sword * pexpr sword)%type.

Inductive instr := 
| Cbcmd  : bcmd -> instr
| Cif    : pexpr sbool -> seq instr -> seq instr -> instr
| Cfor   : rval sword -> range -> seq instr -> instr
| Ccall  : forall starg stres, 
             rval  stres ->
             fundef starg stres ->
             pexpr starg ->
             instr

with fundef : stype -> stype -> Type := 
| FunDef : forall starg stres, rval starg -> seq instr -> rval stres -> fundef starg stres.

Notation cmd := (seq instr).

Definition fd_arg sta str (fd : fundef sta str) : rval sta :=
  match fd with FunDef _ _ fa _ _ => fa end.

Definition fd_body sta str (fd : fundef sta str) : cmd :=
  match fd with FunDef _ _ _ fb _ => fb end.

Definition fd_res sta str (fd : fundef sta str) : rval str :=
  match fd with FunDef _ _ _ _ fr => fr end.

Section IND.
  Variable Pi : instr -> Type.
  Variable Pc : cmd -> Type.
  Variable Pf : forall ta tr, fundef ta tr -> Type.

  Hypothesis Hskip : Pc [::].
  Hypothesis Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Hypothesis Hbcmd : forall bc,  Pi (Cbcmd bc).
  Hypothesis Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Hypothesis Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Hypothesis Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Hypothesis Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).

  Fixpoint instr_rect' (i:instr) : Pi i := 
    match i return Pi i with
    | Cbcmd bc => Hbcmd bc
    | Cif b c1 c2 =>
      Hif b
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c1)
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c2)
    | Cfor i rn c =>
      Hfor i rn 
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c)
    | Ccall ta tr x f a =>
      Hcall x a (func_rect f)
    end
  with func_rect {ta tr} (f:fundef ta tr) : Pf f := 
    match f with
    | FunDef ta tr x c re => 
      Hfunc x re
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c)
    end.

  Definition cmd_rect c := 
    list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c.

End IND.

Definition cmd_ind (P:cmd -> Prop) (Pf:forall ta tr, fundef ta tr -> Prop) := 
  @cmd_rect (fun i => P [::i]) P Pf.

Definition func_ind (P:cmd -> Prop) (Pf:forall ta tr, fundef ta tr -> Prop) := 
  @func_rect (fun i => P [::i]) P Pf.

Definition assgn st (rv : rval st) pe := Cbcmd (Assgn rv pe).
Definition load rv pe := Cbcmd (Load rv pe).
Definition store pe1 pe2 := Cbcmd (Store pe1 pe2).

(* ** Interpretation of types
 * -------------------------------------------------------------------- *)

Fixpoint st2ty (t : stype) : Type :=
  match t with
  | sword         => word
  | sbool         => bool
  | sprod st1 st2 => ((st2ty st1) * (st2ty st2))%type
  | sarr n st     => (n.+1).-tuple (st2ty st) (* do not allow zero-dim arrays *)
  end.

(* ** Default values
 * -------------------------------------------------------------------- *)

Fixpoint dflt_val (st : stype) : st2ty st :=
  match st with
  | sword         => n2w 0
  | sbool         => false
  | sprod st1 st2 => (dflt_val st1, dflt_val st2)
  | sarr n    st  => [tuple (dflt_val st) | i < n.+1]
  end.

Definition rdflt_ (st : stype) e (r : result e (st2ty st)) : st2ty st :=
  rdflt (dflt_val st) r.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Notation vmap     := (Fv.t st2ty).
Notation vmap0    := (@Fv.empty st2ty (fun x => dflt_val x.(vtype))).

Fixpoint write_rval (s:vmap) {t} (l:rval t) : st2ty t -> vmap :=
  match l in rval t_ return st2ty t_ -> vmap with
  | Rvar x => fun v => s.[x <- v]%vmap
  | Rpair t1 t2 rv1 rv2 => fun v => 
    write_rval (write_rval s rv2 (snd v)) rv1 (fst v) 
  end.

Fixpoint sem_rval (s:vmap) t (rv:rval t) : st2ty t := 
  match rv in rval t_ return st2ty t_ with
  | Rvar x            => s.[x]%vmap
  | Rpair _ _ rv1 rv2 => (sem_rval s rv1, sem_rval s rv2)
  end.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Inductive error := ErrOob | ErrAddrUndef | ErrAddrInvalid.

Definition exec t := result error t.
Definition ok := Ok error. 

Definition sem_sop1 st1 str (sop : sop1 st1 str) : st2ty st1 -> exec (st2ty str) :=
  match sop in sop1 st1 str return st2ty st1 -> exec (st2ty str) with
  | Onot       => fun b => ok(~~ b)
  | Ofst t1 t2 => fun (xy : (st2ty t1 * st2ty t2)) => ok xy.1
  | Osnd t1 t2 => fun (xy : (st2ty t1 * st2ty t2)) => ok xy.2
  end.

Definition sem_sop2 st1 st2 str (sop : sop2 st1 st2 str) :=
  match sop in sop2 st1 st2 str return 
        st2ty st1 -> st2ty st2 -> exec (st2ty str) with
  | Oand       => fun x y => ok (x && y)
  | Oor        => fun x y => ok (x || y)
  | Oadd       => fun x y => ok (wadd x y)
  | Oeq        => fun (x y : word) => ok (x == y)
  | Olt        => fun (x y : word) => ok (x < y)
  | Oget n     => fun (a : (n.+1).-tuple word) (i:word) =>
                    if i > n
                    then Error ErrOob
                    else ok (tnth a (@inZp n i))
  | Opair t1 t2 => fun x y => ok (x,y)
  end.

Definition sem_sop3 st1 st2 st3 str (sop : sop3 st1 st2 st3 str) :=
  match sop in sop3 st1 st2 st3 str return 
        st2ty st1 -> st2ty st2 -> st2ty st3 -> exec (st2ty str) with
  | Oset n => fun (a: (n.+1).-tuple word) (i v: word) =>
                if i > n
                then Error ErrOob
                else ok [tuple (if j == inZp i then v else tnth a j) | j < n.+1]
  | Oaddc  => fun x y c => ok (waddc x y c)
  end.

Fixpoint sem_pexpr st (vm : vmap) (pe : pexpr st) : exec (st2ty st) :=
  match pe with
  | Pvar v => ok (vm.[ v ]%vmap)
  | Pconst c => ok (n2w c)
  | Papp1 st1 str o pe1 =>
      sem_pexpr vm pe1 >>= fun v1 =>
      sem_sop1 o v1
  | Papp2 st1 st2 str o pe1 pe2 =>
      sem_pexpr vm pe1 >>= fun v1 =>
      sem_pexpr vm pe2 >>= fun v2 =>
      sem_sop2 o v1 v2
  | Papp3 st1 st2 st3 str o pe1 pe2 pe3 =>
      sem_pexpr vm pe1 >>= fun v1 =>
      sem_pexpr vm pe2 >>= fun v2 =>
      sem_pexpr vm pe3 >>= fun v3 =>
      sem_sop3 o v1 v2 v3
  end.

(* ** Memory
 * -------------------------------------------------------------------- *)

Definition mem := {fmap word -> word}.

Variable valid_addr : word -> bool.

Definition read_mem (m : mem) (p : word) : exec word :=
  if valid_addr p
  then o2r ErrAddrUndef (m.[? p]%fmap)
  else Error ErrAddrInvalid.

Definition write_mem (m : mem) (p w : word) : exec mem :=
  if valid_addr p
  then ok (m.[p <- w]%fmap)
  else Error ErrAddrInvalid.

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
  | DownTo => rev idxs
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
    sem s [::] s

| Eseq s1 s2 s3 i c :
    sem_i s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

with sem_i : estate -> instr -> estate -> Prop :=

| Ebcmd s1 s2 c:
    sem_bcmd s1 c = ok s2 -> sem_i s1 (Cbcmd c) s2

| Eif s1 s2 (pe : pexpr sbool) cond c1 c2 :
    sem_pexpr s1.(evm) pe = ok cond ->
    sem s1 (if cond then c1 else c2) s2 ->
    sem_i s1 (Cif pe c1 c2) s2

| Ecall sta str m1 vm1 m2 (rv_res : rval str) (fd : fundef sta str) (pe_arg : pexpr sta)
      (res : st2ty str):
    let rarg := sem_pexpr vm1 pe_arg in
    isOk rarg ->
    sem_call m1 fd (rdflt_ rarg) m2 res ->
    sem_i (Estate m1 vm1)
          (Ccall rv_res fd pe_arg)
          (Estate m2 (write_rval vm1 rv_res res))

| EFor s1 s2 iv rng c ws :
    sem_range s1.(evm) rng = ok ws ->
    sem_for iv ws s1 c s2 ->
    sem_i s1 (Cfor iv rng c) s2

with sem_for : rval sword -> seq word -> estate -> cmd -> estate -> Prop :=

| EForDone s c iv :
    sem_for iv [::] s c s

| EForOne s1 s3 c w ws iv :
    let vm2 := write_rval s1.(evm) iv w in
    sem_for iv (ws)    (Estate s1.(emem) vm2) c  s3 ->
    sem_for iv (w::ws) s1 c  s3

with sem_call : 
  forall sta str, mem -> fundef sta str -> st2ty sta -> mem -> st2ty str -> Prop :=

| EcallRun sta str m1 m2 vm0 vm2 (f:fundef sta str) (varg : st2ty sta):
    (* semantics defined for all vm0 *)
    (forall vm0, exists m2 vm2,
       let vm1 := write_rval vm0 f.(fd_arg) varg in
       sem (Estate m1 vm1) f.(fd_body) (Estate m2 vm2)) ->
    (* yields given memory m2 and result res *)
    let vm1 := write_rval vm0 f.(fd_arg) varg in
    sem (Estate m1 vm1) f.(fd_body) (Estate m2 vm2) ->
    let rres := sem_rval vm2 f.(fd_res) in
    sem_call m1 f varg m2 rres.

Scheme sem_Ind := Minimality for sem Sort Prop
with sem_i_Ind := Minimality for sem_i Sort Prop
with sem_for_Ind := Minimality for sem_for Sort Prop
with sem_call_Ind := Minimality for sem_call Sort Prop.

Lemma sem_inv_app l1 l2 s1 s2:
  sem s1 (l1 ++ l2) s2 ->
  exists s3,
    sem s1 l1 s3 /\ sem s3 l2 s2.
Proof.
  generalize s1. elim l1.
  + move=> s1_; rewrite /= => H.
    by exists s1_; split; first by constructor.
  + move=> inst c Hi s1_ Hs.
    rewrite cat_cons in Hs.
    inversion Hs => {Hs}.
    move: (Hi _ H4); elim => s5; case => Hs1 Hs2.
    exists s5; split => //.
    by apply (Eseq (s2:=s3)).
Qed.

Definition sem_fail (s1 : estate) (c : cmd) : Prop :=
  forall s2, not (sem s1 c s2).

Definition sem_i_fail (s1 : estate) (i : instr) : Prop :=
  forall s2, not (sem_i s1 i s2).
