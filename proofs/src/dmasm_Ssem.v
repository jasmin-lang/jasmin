(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import ZArith.

Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.
Require Import memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope string_scope.

(* ** Type interpretation
 * -------------------------------------------------------------------- *)

Fixpoint sst2ty (t : stype) : Type :=
  match t with
  | sword         => word
  | sbool         => bool
  | sprod st1 st2 => ((sst2ty st1) * (sst2ty st2))%type
  | sarr n        => FArray.array word
  end.

Fixpoint sdflt_val st :  sst2ty st :=
  match st with
  | sword         => n2w 0
  | sbool         => true
  | sprod st1 st2 => (sdflt_val st1, sdflt_val st2)
  | sarr n        => FArray.cnst (n2w 0)
  end.

(* ** Variable map
 * -------------------------------------------------------------------- *)


Notation svmap    := (Fv.t sst2ty).
Notation svmap0   := (@Fv.empty sst2ty (fun x => sdflt_val x.(vtype))).

Fixpoint swrite_rval (s:svmap) {t} (l:rval t) : sst2ty t -> svmap :=
  match l in rval t_ return sst2ty t_ -> svmap with
  | Rvar x => fun v => s.[x <- v]%vmap
  | Rpair t1 t2 rv1 rv2 => fun v => 
    swrite_rval (swrite_rval s rv2 (snd v)) rv1 (fst v) 
  end.

Fixpoint ssem_rval (s:svmap) t (rv:rval t) : sst2ty t := 
  match rv in rval t_ return sst2ty t_ with
  | Rvar x            => s.[x]%vmap
  | Rpair _ _ rv1 rv2 => (ssem_rval s rv1, ssem_rval s rv2)
  end.

(* ** Operators 
 * -------------------------------------------------------------------- *)

Definition ssem_sop1 st1 str (sop : sop1 st1 str) : sst2ty st1 -> sst2ty str :=
  match sop in sop1 st1 str return sst2ty st1 -> sst2ty str with
  | Onot       => negb
  | Ofst t1 t2 => fst 
  | Osnd t1 t2 => snd 
  end.

Definition ssem_sop2 st1 st2 str (sop : sop2 st1 st2 str) :=
  match sop in sop2 st1 st2 str return 
        sst2ty st1 -> sst2ty st2 -> sst2ty str with
  | Oand       => andb
  | Oor        => orb
  | Oadd       => wadd 
  | Oaddc      => waddc 
  | Osub       => wsub 
  | Osubc      => wsubc 
  | Oeq        => fun (x y : word) => x == y
  | Olt        => wlt 
  | Ole        => wle
  | Oget n     => @FArray.get word
  | Opair t1 t2 => fun x y => (x,y)
  end.

Definition ssem_sop3 st1 st2 st3 str (sop : sop3 st1 st2 st3 str) :=
  match sop in sop3 st1 st2 st3 str return 
        sst2ty st1 -> sst2ty st2 -> sst2ty st3 -> sst2ty str with
  | Oset n     => @FArray.set word
  | Oaddcarry  => waddcarry 
  | Osubcarry  => wsubcarry 
  end.

(* ** Operators 
 * -------------------------------------------------------------------- *)

Fixpoint ssem_pexpr st (vm : svmap) (pe : pexpr st) : sst2ty st :=
  match pe with
  | Pvar v => vm.[ v ]%vmap
  | Pconst c => I64.repr c
  | Pbool  b => b
  | Papp1 st1 str o pe1 =>
      let v1 := ssem_pexpr vm pe1 in
      ssem_sop1 o v1
  | Papp2 st1 st2 str o pe1 pe2 =>
      let v1 := ssem_pexpr vm pe1 in 
      let v2 := ssem_pexpr vm pe2 in
      ssem_sop2 o v1 v2
  | Papp3 st1 st2 st3 str o pe1 pe2 pe3 =>
      let v1 := ssem_pexpr vm pe1 in
      let v2 := ssem_pexpr vm pe2 in
      let v3 := ssem_pexpr vm pe3 in
      ssem_sop3 o v1 v2 v3
  end.

(* ** Instructions
 * -------------------------------------------------------------------- *)

Record sestate := SEstate {
  semem : mem;
  sevm  : svmap
}.

Section SEM.

Definition ssem_bcmd (es : sestate) (bc : bcmd) : exec sestate :=
  match bc with
  | Assgn st rv pe =>
      let v := ssem_pexpr es.(sevm) pe in
      let vm := swrite_rval es.(sevm) rv v in
      ok (SEstate es.(semem) vm)
  | Load rv pe_addr =>
      let p := ssem_pexpr es.(sevm) pe_addr in
      read_mem es.(semem) p >>= fun w =>
      let vm := swrite_rval es.(sevm) rv w in
      ok (SEstate es.(semem) vm)

  | Store pe_addr pe_val =>
      let p := ssem_pexpr es.(sevm) pe_addr in
      let w := ssem_pexpr es.(sevm) pe_val in
      write_mem es.(semem) p w >>= fun m =>
      ok (SEstate m es.(sevm))
  end.

Definition ssem_range (vm : svmap) (r : range) :=
  let: (d,pe1,pe2) := r in
  let w1 := ssem_pexpr vm pe1 in
  let w2 := ssem_pexpr vm pe2 in
  [seq n2w n | n <- wrange d w1 w2].

Inductive ssem : sestate -> cmd -> sestate -> Prop :=
| SEskip s :
    ssem s [::] s

| SEseq s1 s2 s3 i c :
    ssem_i s1 i s2 -> ssem s2 c s3 -> ssem s1 (i::c) s3

with ssem_i : sestate -> instr -> sestate -> Prop :=
| SEbcmd s1 s2 c:
    ssem_bcmd s1 c = ok s2 -> ssem_i s1 (Cbcmd c) s2

| SEifTrue s1 s2 (pe : pexpr sbool) c1 c2 :
    ssem_pexpr s1.(sevm) pe ->
    ssem s1 c1 s2 ->
    ssem_i s1 (Cif pe c1 c2) s2

| SEifFalse s1 s2 (pe : pexpr sbool) c1 c2 :
    ~~ssem_pexpr s1.(sevm) pe ->
    ssem s1 c2 s2 ->
    ssem_i s1 (Cif pe c1 c2) s2

| SEcall es m ta tr x (f:fundef ta tr) a vr:
    let va := ssem_pexpr es.(sevm) a in
    ssem_fun f es.(semem) va m vr ->
    let vm2 := swrite_rval es.(sevm) x vr in 
    ssem_i es (Ccall x f a) (SEstate m vm2)

| SEfor s1 s2 i dir (e1 e2:pexpr sword) c:
    let w1 := ssem_pexpr s1.(sevm) e1 in
    let w2 := ssem_pexpr s1.(sevm) e2 in
    ssem_for i (map n2w (wrange dir w1 w2)) s1 c s2 ->
    ssem_i s1 (Cfor i (dir, e1, e2) c) s2

| SEwhile s1 s2 e c :
   ssem_while s1 e c s2 ->
   ssem_i s1 (Cwhile e c) s2

with ssem_fun : forall ta tr (f:fundef ta tr) (m:mem) (va:sst2ty ta), mem -> sst2ty tr -> Prop :=
| SEfun : forall ta tr (f:fundef ta tr) (m:mem) (va:sst2ty ta) vm es',
    let es := {| semem := m; sevm := swrite_rval vm f.(fd_arg) va |} in
    ssem es f.(fd_body) es' ->
    let rv := ssem_rval es'.(sevm) f.(fd_res) in
    ssem_fun f m va es'.(semem) rv

with ssem_for : rval sword -> seq word -> sestate -> cmd -> sestate -> Prop :=
| SEForDone i c s :
    ssem_for i [::] s c s

| SEForOne (i:rval sword) w ws c s1 s2 s3:
    ssem (SEstate s1.(semem) (swrite_rval s1.(sevm) i w)) c s2 ->
    ssem_for i ws s2 c s3 ->
    ssem_for i (w :: ws) s1 c s3

with ssem_while : sestate -> pexpr sbool -> cmd -> sestate -> Prop := 
| SEWhileDone s (e:pexpr sbool) c :
    ssem_pexpr s.(sevm) e = false ->
    ssem_while s e c s
| SEWhileOne s1 s2 s3 (e:pexpr sbool) c :  
    ssem_pexpr s1.(sevm) e = true ->
    ssem s1 c s2 ->
    ssem_while s2 e c s3 ->
    ssem_while s1 e c s3.

Lemma ssem_iV s i s' : ssem s [::i] s' -> ssem_i s i s'.
Proof.
  move=> H;inversion H;subst.
  by inversion H5;subst.
Qed.

Lemma ssem_cV c1 c2 s s' : ssem s (c1 ++ c2) s' ->
  exists s'', ssem s c1 s'' /\ ssem s'' c2 s'.
Proof.
  elim: c1 s s' => /=[ | i c Hc] s s'. 
  + by exists s;split => //;constructor.
  set c_ := _ :: _ => H;case: _ {-1}_ _ / H (erefl c_) => //= ? s2 ? ?? Hi Hcat [] ??;subst.
  elim: (Hc _ _ Hcat)=> s1 [H1 H2];exists s1;split=>//;econstructor;eauto.
Qed.

End SEM.