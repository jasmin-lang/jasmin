(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import finmap strings word dmasm_utils dmasm_type dmasm_var.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.

(* ** Operators
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
| Oadd   : sop2 sword sword sword
| Oaddc  : sop2 sword sword (sbool ** sword)

| Osub  : sop2 sword sword sword
| Osubc  : sop2 sword sword (sbool ** sword)

(*| Oxor  : sop2 sword sword sword
| Oland : sop2 sword sword sword
| Olor  : sop2 sword sword sword *)
| Oeq   : sop2 sword sword sbool
| Olt   : sop2 sword sword sbool
| Ole   : sop2 sword sword sbool
(* arrays *)
| Oget  : forall n, sop2 (sarr n sword) sword sword
(* pairs *)
| Opair : forall st1 st2, sop2 st1 st2 (st1 ** st2).

Inductive sop3 : stype -> stype -> stype -> stype -> Set :=
(* words *)
| Oaddcarry : sop3 sword sword sbool (sbool ** sword)
| Osubcarry : sop3 sword sword sbool (sbool ** sword)
(* arrays *)
| Oset  : forall n, sop3 (sarr n sword) sword sword (sarr n sword).

Definition eqb_sop1 {t1 tr t1' tr'} (o:sop1 t1 tr) (o':sop1 t1' tr') := 
  match o, o' with
  | Onot    , Onot     => true
  | Ofst _ _, Ofst _ _ => true
  | Osnd _ _, Osnd _ _ => true
  | _       , _        => false
  end.

Definition eqb_sop2 {t1 t2 tr t1' t2' tr'} (o:sop2 t1 t2 tr) (o':sop2 t1' t2' tr') := 
  match o, o' with
| Oand     , Oand      => true
| Oor      , Oor       => true
| Oadd     , Oadd      => true
| Oaddc    , Oaddc     => true
| Osub     , Osub      => true
| Osubc    , Osubc     => true
| Oeq      , Oeq       => true
| Olt      , Olt       => true
| Ole      , Ole       => true
| Oget _   , Oget _    => true
| Opair _ _, Opair _ _ => true
| _        , _         => false
end.

Definition eqb_sop3 {t1 t2 t3 tr t1' t2' t3' tr'} 
           (o:sop3 t1 t2 t3 tr) (o':sop3 t1' t2' t3' tr') := 
  match o, o' with
 | Oaddcarry , Oaddcarry  => true
 | Osubcarry , Osubcarry  => true
 | Oset _    , Oset _     => true
 | _         , _          => false
 end.

Lemma eqb_sop1P t1 t1' tr tr' (o:sop1 t1 tr) (o':sop1 t1' tr'):
  t1 = t1' -> eqb_sop1 o o' ->  tr = tr' /\ JMeq o o'.
Proof. by move: o o' => [|??|??] [|??|??] //= [] ->->. Qed. 

Lemma eqb_sop2P t1 t1' t2 t2' tr tr' (o:sop2 t1 t2 tr) (o':sop2 t1' t2' tr'):
  t1 = t1' -> t2 = t2' -> eqb_sop2 o o' -> tr = tr' /\ JMeq o o'.
Proof. by move: o o'=> [|||||||||?|??] [|||||||||?|??] //= => [ []->| ->->]. Qed.

Lemma eqb_sop3P t1 t1' t2 t2' t3 t3' tr tr' (o:sop3 t1 t2 t3 tr) (o':sop3 t1' t2' t3' tr'):
  t1 = t1' -> t2 = t2' -> t3 = t3' -> eqb_sop3 o o' ->  tr = tr' /\ JMeq o o'.
Proof. by move: o o'=> [||?] [||?] // [] ->. Qed.


(* ** Expressions
 * -------------------------------------------------------------------- *)



Inductive pexpr : stype -> Type :=
| Pvar   :> forall x:var, pexpr x.(vtype)
| Pconst :> N -> pexpr sword
| Papp1  : forall st1 stres: stype, 
  sop1 st1 stres -> pexpr st1 -> pexpr stres
| Papp2  : forall st1 st2 stres: stype, 
  sop2 st1 st2 stres -> pexpr st1 -> pexpr st2 -> pexpr stres
| Papp3  : forall st1 st2 st3 stres: stype, 
  sop3 st1 st2 st3 stres -> pexpr st1 -> pexpr st2 -> pexpr st3 -> pexpr stres.


(* ** Instructions 
 * -------------------------------------------------------------------- *)

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

Definition cmd_Ind (P : cmd -> Prop) := 
  @cmd_ind P (fun _ _ _ => True).

(* ** Memory
 * -------------------------------------------------------------------- *)

Inductive error := ErrOob | ErrAddrUndef | ErrAddrInvalid.

Definition exec t := result error t.
Definition ok := Ok error. 

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

