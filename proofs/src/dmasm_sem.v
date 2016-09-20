(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)
Require Import JMeq ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import finmap strings word dmasm_utils dmasm_type dmasm_var dmasm_expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Open Scope string_scope.
Local Open Scope ring_scope.

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
  | Oaddc      => fun x y => ok (waddc x y)
  | Osub       => fun x y => ok (wsub x y)
  | Osubc      => fun x y => ok (wsubc x y)
  | Oeq        => fun (x y : word) => ok (x == y)
  | Olt        => fun (x y : word) => ok (x < y)
  | Ole        => fun (x y : word) => ok (x <= y)  
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
  | Oaddcarry  => fun x y c => ok (waddcarry x y c)
  | Osubcarry  => fun x y c => ok (wsubcarry x y c)
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

Definition wrange d (n1 n2:nat) :=
  if n1 <= n2 then 
    let idxs := iota n1 (S (n2 - n1)) in
    match d with
    | UpTo   => idxs
    | DownTo => rev idxs
    end
  else [::].

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

| Ecall sta str m1 vm1 m2
        (rv_res : rval str) (fd : fundef sta str)
        (pe_arg : pexpr sta) (res : st2ty str)
  :
    let rarg := sem_pexpr vm1 pe_arg in
    isOk rarg ->
    sem_call m1 fd (rdflt_ rarg) m2 res ->
    sem_i (Estate m1 vm1)
          (Ccall rv_res fd pe_arg)
          (Estate m2 (write_rval vm1 rv_res res))

| EFor s1 s2 fi iv dir (low hi : pexpr sword) c vlow vhi :
    sem_pexpr s1.(evm) low = ok vlow ->
    sem_pexpr s1.(evm) hi  = ok vhi  ->
    sem_for iv dir vlow vhi s1 c s2 ->
    sem_i s1 (Cfor fi iv (dir, low, hi) c) s2

with sem_for : rval sword -> dir -> word -> word -> estate -> cmd -> estate -> Prop :=
| EForDone s1 s2 iv dir w c :
    sem (Estate s1.(emem) (write_rval s1.(evm) iv w)) c s2 ->
    sem_for iv dir w w s1 c s2

| EForOne s1 s2 s3 (iv : rval sword) dir (w1 w2 : word) c : w1 < w2 ->
    let w := if dir is UpTo then w1 else w2 in
    sem (Estate s1.(emem) (write_rval s1.(evm) iv w)) c s2 ->
    let w1' := if dir is UpTo then w1+1 else w1   in
    let w2' := if dir is UpTo then w2   else w2-1 in
    sem_for iv dir w1' w2' s2 c s3 ->
    sem_for iv dir w1  w2  s1 c s3

with sem_call : 
  forall sta str, mem -> fundef sta str -> st2ty sta -> mem -> st2ty str -> Prop :=

| EcallRun sta str m1 m2 rres (f:fundef sta str) (varg : st2ty sta):
    (* semantics defined for all vm0 *)
    (forall vm0, exists vm2,
       let vm1 := write_rval vm0 f.(fd_arg) varg in
       sem (Estate m1 vm1) f.(fd_body) (Estate m2 vm2) /\
       rres = sem_rval vm2 f.(fd_res)) ->
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
