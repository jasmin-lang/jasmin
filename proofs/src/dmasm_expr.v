(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith Setoid Morphisms.
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
| Pbool  :> bool -> pexpr sbool
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

Inductive for_info :=
| Unroll_for
| Keep_for.

Inductive instr := 
| Cbcmd  : bcmd -> instr
| Cif    : pexpr sbool -> seq instr -> seq instr -> instr
| Cfor   : for_info -> rval sword -> range -> seq instr -> instr
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
  Hypothesis Hfor  : forall fi i rn c, Pc c -> Pi (Cfor fi i rn c).
  Hypothesis Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Hypothesis Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).

  Fixpoint instr_rect' (i:instr) : Pi i := 
    match i return Pi i with
    | Cbcmd bc => Hbcmd bc
    | Cif b c1 c2 =>
      Hif b
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c1)
        (list_rect Pc Hskip (fun i c Hc => Hseq (instr_rect' i) Hc) c2)
    | Cfor fi i rn c =>
      Hfor fi i rn 
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



(* -------------------------------------------------------------------------- *)
(* Compute the set of writen variables of a program                           *)
(* -------------------------------------------------------------------------- *)

Fixpoint vrv_rec {t} (s:Sv.t) (rv : rval t)  :=
  match rv with
  | Rvar  x               => Sv.add x s
  | Rpair st1 st2 rv1 rv2 => vrv_rec (vrv_rec s rv1) rv2 
  end.

Definition vrv {t} (rv : rval t) := vrv_rec Sv.empty rv.

Definition write_bcmd_rec (s:Sv.t) bc  := 
  match bc with
  | Assgn _ rv _  => vrv_rec s rv
  | Load rv _     => vrv_rec s rv
  | Store _ _     => s
  end.

Definition write_bcmd := write_bcmd_rec Sv.empty.

Fixpoint write_i_rec s i := 
  match i with
  | Cbcmd bc        => write_bcmd_rec s bc
  | Cif   _ c1 c2   => foldl write_i_rec (foldl write_i_rec s c2) c1
  | Cfor  _ x _ c     => foldl write_i_rec (vrv_rec s x) c
  | Ccall _ _ x _ _ => vrv_rec s x
  end.

Definition write_i i := write_i_rec Sv.empty i.

Definition write_c_rec s c := foldl write_i_rec s c.

Definition write_c c := write_c_rec Sv.empty c.

Instance vrv_rec_m {t} : Proper (Sv.Equal ==> (@eq (rval t)) ==> Sv.Equal) vrv_rec.
Proof.
  move=> s1 s2 Hs ? r ->.
  elim:r s1 s2 Hs => //= [??? -> // | ?? r1 Hr1 r2 Hr2 ???];auto.
Qed.

Lemma vrv_var (x:var) : Sv.Equal (vrv x) (Sv.singleton x). 
Proof. rewrite /vrv /=;SvD.fsetdec. Qed.

Lemma vrv_recE t (r:rval t) s : Sv.Equal (vrv_rec s r) (Sv.union s (vrv r)).
Proof.
  elim: r s => //= [x | ?? r1 Hr1 r2 Hr2] s.
  + by rewrite vrv_var;SvD.fsetdec.
  rewrite /vrv /= !(Hr1,Hr2);SvD.fsetdec.
Qed.

Lemma vrv_pair t1 t2 (r1:rval t1) (r2:rval t2):
  Sv.Equal (vrv (Rpair r1 r2)) (Sv.union (vrv r1) (vrv r2)).
Proof. rewrite {1}/vrv /= !vrv_recE;SvD.fsetdec. Qed.

Lemma write_bcmdE s bc : Sv.Equal (write_bcmd_rec s bc) (Sv.union s (write_bcmd bc)).
Proof. case: bc=> [? r _ | r _ | _ _] /=;rewrite ?vrv_recE;SvD.fsetdec. Qed.

Lemma write_c_recE s c : Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)).
Proof.
  apply (@cmd_rect
           (fun i => forall s, Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)))
           (fun c => forall s, Sv.Equal (write_c_rec s c) (Sv.union s (write_c c)))
           (fun _ _ _ => True)) => /= {c s}
    [ |i c1 Hi Hc1|bc|e c1 c2 Hc1 Hc2|? x rn c1 Hc1| ?? x f a _|//] s;
    rewrite /write_i /write_c /=.
  + by SvD.fsetdec. 
  + by rewrite !Hc1 !Hi; SvD.fsetdec.  
  + by rewrite !write_bcmdE; SvD.fsetdec.
  + by rewrite -!/(write_c_rec _ c1) -!/(write_c_rec _ c2) !Hc1 !Hc2; SvD.fsetdec.
  + by rewrite -!/(write_c_rec _ c1) !Hc1 vrv_recE; SvD.fsetdec.
  by rewrite !vrv_recE; SvD.fsetdec.
Qed.

Lemma write_i_recE s i : Sv.Equal (write_i_rec s i) (Sv.union s (write_i i)).
Proof. by apply (write_c_recE s [:: i]). Qed.

Lemma write_c_nil : write_c [::] = Sv.empty.
Proof. done. Qed.

Lemma write_c_cons i c: Sv.Equal (write_c (i::c)) (Sv.union (write_i i) (write_c c)).
Proof. by rewrite {1}/write_c /= write_c_recE write_i_recE;SvD.fsetdec. Qed.

Lemma write_i_bcmd bc : write_i (Cbcmd bc) = write_bcmd bc.
Proof. done. Qed.

Lemma write_i_if e c1 c2 :
   Sv.Equal (write_i (Cif e c1 c2)) (Sv.union (write_c c1) (write_c c2)).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c1) -/(write_c_rec _ c2) !write_c_recE;SvD.fsetdec.
Qed.

Lemma write_i_for fi x rn c :
   Sv.Equal (write_i (Cfor fi x rn c)) (Sv.union (vrv x) (write_c c)).
Proof.
  rewrite /write_i /= -/(write_c_rec _ c) write_c_recE vrv_recE;SvD.fsetdec.
Qed.

Lemma write_i_call t1 t2 (f:fundef t1 t2) x a :
  write_i (Ccall x f a) = vrv x.
Proof. done. Qed.


(* -------------------------------------------------------------------------- *)
(* Some smart constructors                                                    *)
(* -------------------------------------------------------------------------- *)

Definition destr_pair t1 t2 (p:pexpr (t1 ** t2)) : option (pexpr t1 * pexpr t2).
case H: _ / p => [ ? | ? | ? | ???? | ??? o e1 e2| ???????? ].
+ exact None. + exact None. + exact None. + exact None. 
+ (case:o H e1 e2 => [||||||||||??[]<-<- e1 e2];last by exact (Some (e1,e2)))=> *; 
  exact None.
exact None. 
Defined.

Definition efst t1 t2 (p:pexpr (t1 ** t2)) : pexpr t1 :=
  match destr_pair p with
  | Some (p1,p2) => p1
  | _            => Papp1 (Ofst _ _) p
  end.

Definition esnd t1 t2 (p:pexpr (t1 ** t2)) : pexpr t2 :=
  match destr_pair p with
  | Some (p1,p2) => p2
  | _            => Papp1 (Osnd _ _) p
  end.
Print cmd.

Fixpoint rval2pe t (rv:rval t) := 
  match rv in rval t_ return pexpr t_ with
  | Rvar x              => x
  | Rpair t1 t2 rv1 rv2 => Papp2 (Opair t1 t2) (rval2pe rv1) (rval2pe rv2)
  end. 
