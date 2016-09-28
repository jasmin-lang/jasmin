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
  | Pbool b  => ok b
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

Definition wrange d (n1 n2 : nat) :=
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
    sem_for iv (map n2w (wrange dir vlow vhi)) s1 c s2 ->
    sem_i s1 (Cfor fi iv (dir, low, hi) c) s2

with sem_for : rval sword -> seq word -> estate -> cmd -> estate -> Prop :=
| EForDone s iv c :
    sem_for iv [::] s c s

| EForOne s1 s2 s3 (iv : rval sword) w ws c :
    sem (Estate s1.(emem) (write_rval s1.(evm) iv w)) c s2 ->
    sem_for iv ws s2 c s3 ->
    sem_for iv (w :: ws) s1 c s3

with sem_call : 
  forall sta str, mem -> fundef sta str -> st2ty sta -> mem -> st2ty str -> Prop :=

| EcallRun sta str m1 m2 rres (f:fundef sta str) (varg : st2ty sta):
    (* semantics defined for all vm0 *)
    (forall vm0, exists vm2,
       let vm1 := write_rval vm0 f.(fd_arg) varg in
       sem (Estate m1 vm1) f.(fd_body) (Estate m2 vm2) /\
       rres = sem_rval vm2 f.(fd_res)) ->
    sem_call m1 f varg m2 rres.

(* -------------------------------------------------------------------- *)
Scheme sem_Ind := Minimality for sem Sort Prop
with   sem_i_Ind := Minimality for sem_i Sort Prop
with   sem_for_Ind := Minimality for sem_for Sort Prop
with   sem_call_Ind := Minimality for sem_call Sort Prop.

(* -------------------------------------------------------------------- *)
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

Lemma sem_app l1 l2 s1 s2 s3:
  sem s1 l1 s2 -> sem s2 l2 s3 ->
  sem s1 (l1 ++ l2) s3.
Proof.
  elim: l1 s1.
  + by move=> s1 H1;inversion H1.
  move=> a l Hrec s1 H1;inversion H1;subst;clear H1 => /= Hl2.
  by apply (Eseq H3);apply Hrec.
Qed.

Lemma sem_seq1 i s1 s2:
  sem_i s1 i s2 -> sem s1 [::i] s2.
Proof.
  move=> Hi; apply (Eseq Hi);constructor.
Qed.

Definition sem_fail (s1 : estate) (c : cmd) : Prop :=
  forall s2, not (sem s1 c s2).

Definition sem_i_fail (s1 : estate) (i : instr) : Prop :=
  forall s2, not (sem_i s1 i s2).


Definition vmap_eq_except (s : Sv.t) (vm1 vm2 : vmap) :=
  forall x, ~Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vrvP t (r:rval t) v s : s = write_rval s r v [\ vrv r].
Proof.
  elim: r v s=> [x | ?? r1 Hr1 r2 Hr2] v s /= z; rewrite ?vrv_var ?vrv_pair=> ?.
  + rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
  rewrite -Hr1 -?Hr2//; SvD.fsetdec.
Qed.

Lemma writeP c s1 s2 : 
   sem s1 c s2 -> s1.(evm) = s2.(evm) [\ write_c c].
Proof.
  apply (@cmd_rect
           (fun i => forall s1 s2, sem_i s1 i s2 -> s1.(evm) = s2.(evm) [\ write_i i])
           (fun c => forall s1 s2, sem   s1 c s2 -> s1.(evm) = s2.(evm) [\ write_c c])
           (fun _ _ _ => True)) => /= {c s1 s2}
    [ |i c1 Hi Hc1|bc|e c1 c2 Hc1 Hc2|? x rn c1 Hc1| ?? x f a _|//] s1 s2 Hsem;
    inversion Hsem=>{Hsem};subst=> // z.
  + rewrite write_c_cons => Hz;rewrite (Hi _ _ H2) ?(Hc1 _ _ H4) //; SvD.fsetdec. 
  + rewrite write_i_bcmd;case: bc H1 => //= [? r p | r p | p1 p2].
    + by case sem_pexpr => //= s [] <- /=;apply vrvP.
    + by case sem_pexpr=> //= s; case read_mem => //= w [] <-;apply vrvP.
    case (sem_pexpr _ p1) => //= s_1;case (sem_pexpr _ p2) => //= s_2.
    by case write_mem => //= ? [] <-.
  + by rewrite write_i_if=> ?; case:cond H4 H5=> H4 H5;[apply Hc1 | apply Hc2] => //;
     SvD.fsetdec. 
  + rewrite write_i_for. 
    elim: H7 Hc1=> {H5 H6 dir s1 s2} //=.
    move => s1 s2 s3 iv w1 w2 c Hsem Hfor Hrec Hc Hin.
    rewrite -Hrec // -(Hc _ _ Hsem) /= -?vrvP //; SvD.fsetdec. 
  by rewrite write_i_call=> Hin; move: H3 H4=> [] ?;subst=> -[] [] ?;subst;apply vrvP.  
Qed.

Lemma write_iP i s1 s2 : 
   sem_i s1 i s2 -> s1.(evm) = s2.(evm) [\ write_i i].
Proof.
  move=> /sem_seq1 /writeP.
  have := write_c_cons i [::].
  move=> Heq H x Hx;apply H; SvD.fsetdec. 
Qed.

Definition eq_on (s : Sv.t) (vm1 vm2 : vmap) :=
  forall x, Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").

Lemma eq_onT s vm1 vm2 vm3:
  vm1 =[s] vm2 -> vm2 =[s] vm3 -> vm1 =[s] vm3.
Proof. by move=> H1 H2 x Hin;rewrite H1 ?H2. Qed.

Lemma eq_onI s1 s2 vm1 vm2 : Sv.Subset s1 s2 -> vm1 =[s2] vm2 -> vm1 =[s1] vm2.
Proof. move=> Hs Heq x Hin;apply Heq;SvD.fsetdec. Qed.

Lemma eq_onS vm1 s vm2 : vm1 =[s] vm2 -> vm2 =[s] vm1.
Proof. by move=> Heq x Hin;rewrite Heq. Qed.

Lemma disjoint_eq_on s t (r:rval t) vm v: 
  disjoint s (vrv r) ->
  write_rval vm r v =[s] vm.
Proof.
  rewrite /disjoint /is_true Sv.is_empty_spec=> H z Hin.
  elim: r vm v H => [x | ?? rv1 Hrv1 rv2 Hrv2] vm v.
  + rewrite vrv_var /= => ?;rewrite Fv.setP_neq //;apply /eqP;SvD.fsetdec. 
  rewrite vrv_pair /==> Hd;rewrite Hrv1 ?Hrv2 //;SvD.fsetdec. 
Qed.

Lemma read_e_eq_on t (e:pexpr t) s vm vm':
  vm =[read_e_rec e s]  vm' ->
  sem_pexpr vm e = sem_pexpr vm' e.
Proof.
  elim:e s => //=.
  + by move=> x s H;rewrite H //;SvD.fsetdec. 
  + by move=> ?? o e1 He1 s Heq;rewrite (He1 s Heq).
  + move=> ??? o e1 He1 e2 He2 s Heq;rewrite (He1 _ Heq) (He2 s) //. 
    by apply: eq_onI Heq;rewrite (read_eE e1);SvD.fsetdec.
  move=> ???? o e1 He1 e2 He2 e3 He3 s Heq.    
  rewrite (He1 _ Heq); have Heq2 : vm =[read_e_rec e2 (read_e_rec e3 s)]  vm'.
  + by apply: eq_onI Heq;rewrite (read_eE e1);SvD.fsetdec.   
  rewrite (He2 _ Heq2) (He3 s) //.     
  by apply: eq_onI Heq2;rewrite (read_eE e2);SvD.fsetdec.
Qed.

Lemma write_rval_eq_on vm vm' s t (r:rval t) v:
  vm =[Sv.diff s (vrv r)]  vm' ->
  write_rval vm r v =[s]  write_rval vm' r v.
Proof.
  elim: r v vm vm' s => [x|?? rv1 H1 rv2 H2] v vm vm' s /=.
  + move=> Heq z Hz.
    case: (x =P z) => [ <- | /eqP H];first by rewrite !Fv.setP_eq. 
    rewrite !Fv.setP_neq //;apply Heq.   
    by move: H=> /eqP H;rewrite vrv_var;SvD.fsetdec.
  by move=> Heq;apply H1;apply H2=> z Hz;apply Heq;rewrite vrv_pair;SvD.fsetdec.
Qed.

Lemma sem_rval2pe t (x:rval t) vm: 
  sem_pexpr vm (rval2pe x) = Ok error (sem_rval vm x).
Proof. by elim: x => /= [//| ?? x1 -> x2 /= ->]. Qed.
  
Lemma sem_efst vm t1 t2 (e:pexpr (t1 ** t2)) v: 
  sem_pexpr vm e = Ok error v ->
  sem_pexpr vm (efst e) = Ok error v.1.
Proof.
  rewrite /efst.
  case: destr_pair (@destr_pairP _ _ e) => /= [[e1 e2] /(_ _ _ (erefl _)) ->| _ ->] //=.
  by case: (sem_pexpr vm e1)=> // v1;case: sem_pexpr => //= v2 [] <-.   
Qed.

Lemma sem_esnd vm t1 t2 (e:pexpr (t1 ** t2)) v: 
  sem_pexpr vm e = Ok error v ->
  sem_pexpr vm (esnd e) = Ok error v.2.
Proof.
  rewrite /esnd.
  case: destr_pair (@destr_pairP _ _ e) => /= [[e1 e2] /(_ _ _ (erefl _)) ->| _ ->] //=.
  by case: (sem_pexpr vm e1)=> // v1;case: sem_pexpr => //= v2 [] <-.   
Qed.
