(* * Syntax and semantics of the dmasm source language *)

(* ** Imports and settings *)

From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg tuple.
From mathcomp Require Import choice fintype eqtype div seq zmodp.
Require Import JMeq ZArith.

Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ** Interpretation of types
 * -------------------------------------------------------------------- *)

Module FArray.

  Definition array (T:Type) := word -> T.

  Definition cnst {T} (t:T) : array T := fun i => t.

  Definition get {T} (a:array T) (i:word) := a i.

  Definition set {T} (a:array T) (i:word) (v:T) :=
    fun j => if i == j  then v else a j.
  
  Lemma setP {T} (a:array T) (w1 w2:word) (t:T):
    get (set a w1 t) w2 = if w1 == w2 then t else get a w2.
  Proof. done. Qed.

  Lemma setP_eq {T} (a:array T) (w:word) (t:T):
    get (set a w t) w = t.
  Proof. by rewrite setP eq_refl. Qed.

  Lemma setP_neq {T} (a:array T) (w1 w2:word) (t:T): 
    w1 != w2 -> get (set a w1 t) w2 = get a w2.
  Proof. by rewrite setP=> /negPf ->. Qed.

End FArray.

Module Array.

  Definition array (s:positive) T := FArray.array (exec T).

  Definition empty {T:Type} (s:positive) : array s T := FArray.cnst (Error ErrAddrUndef).

  Definition make {T:Type} (s:positive) (t:T) : array s T :=  FArray.cnst (ok t). 

  Definition get {T} {s} (a:array s T) (w:word) : result error T := 
    if ((0 <=? w) && (w <? Zpos s))%Z then FArray.get a w
    else Error ErrOob.

  Definition set {T} s (a:array s T) (x:word) (v:T) : result error (array s T):=
    if ((0 <=? x) && (x <? Zpos s))%Z then ok (FArray.set a x (ok v))
    else Error ErrOob.

  Lemma getP_inv T s (a:array s T) x t: 
    get a x = ok t -> ((0 <=? x) && (x <? Zpos s))%Z.
  Proof. by rewrite /get;case: ifP. Qed.

  Lemma getP_empty T s x w: get (@empty T s) x <> ok w.
  Proof. by rewrite /get/empty;case:ifP. Qed.

  (* FIXME *)
  Axiom eq_ext : forall T s (t1 t2:array s T), (forall x, get t1 x = get t2 x) -> t1 = t2.

End Array.
  
Fixpoint st2ty (t : stype) : Type :=
  match t with
  | sword         => word
  | sbool         => bool
  | sprod st1 st2 => ((st2ty st1) * (st2ty st2))%type
  | sarr n        => Array.array n word
  end.

(* ** Default values
 * -------------------------------------------------------------------- *)

Fixpoint dflt_val (st : stype) : st2ty st :=
  match st with
  | sword         => I64.repr Z0
  | sbool         => false
  | sprod st1 st2 => (dflt_val st1, dflt_val st2)
  | sarr n        => @Array.empty word n
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

(* Initial map *)

Fixpoint is_empty_array (t:stype) : st2ty t -> Prop := 
  match t as t0 return st2ty t0 -> Prop with
  | sword => fun _ => True
  | sbool => fun _ => True
  | sprod t1 t2 => fun v => @is_empty_array t1 v.1 /\ @is_empty_array t2 v.2
  | sarr n => fun v => v =  Array.empty n
  end.

Definition all_empty_arr (vm:vmap) := forall x, is_empty_array (vm.[x])%vmap.

Fixpoint is_full_array (t:stype) : st2ty t -> Prop := 
  match t as t0 return st2ty t0 -> Prop with
  | sword => fun _ => True
  | sbool => fun _ => True
  | sprod t1 t2 => fun v => @is_full_array t1 v.1 /\ @is_full_array t2 v.2
  | sarr n => fun (v:Array.array n word) => 
    forall (p:word), (0 <= p < Zpos n)%Z -> 
       exists w, Array.get v p = ok w
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
  | Olt        => fun (x y : word) => ok (wlt x y)
  | Ole        => fun (x y : word) => ok (wle x y)  
  | Oget n     => @Array.get word n
  | Opair t1 t2 => fun x y => ok (x,y)
  end.

Definition sem_sop3 st1 st2 st3 str (sop : sop3 st1 st2 st3 str) :=
  match sop in sop3 st1 st2 st3 str return 
        st2ty st1 -> st2ty st2 -> st2ty st3 -> exec (st2ty str) with
  | Oset n => @Array.set word n
  | Oaddcarry  => fun x y c => ok (waddcarry x y c)
  | Osubcarry  => fun x y c => ok (wsubcarry x y c)
  end.

Fixpoint sem_pexpr st (vm : vmap) (pe : pexpr st) : exec (st2ty st) :=
  match pe with
  | Pvar v => ok (vm.[ v ]%vmap)
  | Pconst c => ok (I64.repr c)
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

Section SEM. 

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

Definition wrange d (n1 n2 : word) :=
  if (n1 <=? n2)%Z then 
    let idxs := iota (w2n n1) (S (w2n n2 - w2n n1)) in
    match d with
    | UpTo   => idxs
    | DownTo => rev idxs
    end
  else [::].

Definition sem_range (vm : vmap) (r : range) :=
  let: (d,pe1,pe2) := r in
  sem_pexpr vm pe1 >>= fun w1 =>
  sem_pexpr vm pe2 >>= fun w2 =>
  ok [seq n2w n | n <- wrange d w1 w2].

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
        (pe_arg : pexpr sta) (res : st2ty str) :
    let rarg := sem_pexpr vm1 pe_arg in
    isOk rarg ->
    sem_call m1 fd (rdflt_ rarg) m2 res ->
    sem_i (Estate m1 vm1)
          (Ccall rv_res fd pe_arg)
          (Estate m2 (write_rval vm1 rv_res res))
    
| EFor s1 s2 iv dir (low hi : pexpr sword) c vlow vhi :
    sem_pexpr s1.(evm) low = ok vlow ->
    sem_pexpr s1.(evm) hi  = ok vhi  ->
    sem_for iv (map n2w (wrange dir vlow vhi)) s1 c s2 ->
    sem_i s1 (Cfor iv (dir, low, hi) c) s2

| Ewhile s1 s2 e c :
   sem_while s1 e c s2 ->
   sem_i s1 (Cwhile e c) s2

with sem_while : estate -> pexpr sbool -> cmd -> estate -> Prop := 
| EWhileDone s (e:pexpr sbool) c :
    sem_pexpr s.(evm) e = ok false ->
    sem_while s e c s
| EWhileOne s1 s2 s3 (e:pexpr sbool) c :  
    sem_pexpr s1.(evm) e = ok true ->
    sem s1 c s2 ->
    sem_while s2 e c s3 ->
    sem_while s1 e c s3
    
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
    (forall vm0, all_empty_arr vm0 -> exists vm2,
       let vm1 := write_rval vm0 f.(fd_arg) varg in
       sem (Estate m1 vm1) f.(fd_body) (Estate m2 vm2) /\
       rres = sem_rval vm2 f.(fd_res)) ->
    is_full_array rres ->
    sem_call m1 f varg m2 rres.

(* -------------------------------------------------------------------- *)
Scheme sem_Ind := Minimality for sem Sort Prop
with   sem_i_Ind := Minimality for sem_i Sort Prop
with   sem_for_Ind := Minimality for sem_for Sort Prop
with   sem_while_Ind := Minimality for sem_while Sort Prop
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
    [ |i c1 Hi Hc1|bc|e c1 c2 Hc1 Hc2|x rn c Hc|e c Hc|?? x f a _|//] s1 s2 Hsem;
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
    elim: H6 Hc=> //= {H3 H5 dir s1 s2 c} //=.
    move => s1 s2 s3 iv w1 w2 c Hsem Hfor Hrec Hc Hin.
    by rewrite -Hrec // -(Hc _ _ Hsem) /= -?vrvP //; SvD.fsetdec. 
  + rewrite write_i_while;elim: H3 Hc => //= {s1 s2 e c}.
    move => s1 s2 s3 e c He Hsem Hw Hrec Hc Hin.
    by rewrite -Hrec // -(Hc _ _ Hsem) /= -?vrvP //; SvD.fsetdec. 
  by rewrite write_i_call=> Hin; move: H3 H4 => -[] ?;subst=> -[] [] ?;subst;apply vrvP.  
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

End SEM.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Notation "vm1 '=[' s ']' vm2" := (eq_on s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  =[ s ]  '/'  vm2 ']'").



Fixpoint val_uincl (t:stype) : st2ty t -> st2ty t -> Prop := 
  match t as t0 return st2ty t0 -> st2ty t0 -> Prop with
  | sword => fun w1 w2 => w1 = w2
  | sbool => fun b1 b2 => b1 = b2
  | sprod t1 t2 => fun v1 v2 => @val_uincl t1 v1.1 v2.1 /\ @val_uincl t2 v1.2 v2.2
  | sarr n => fun (t1 t2:Array.array n word) => 
      (forall i v, Array.get t1 i = ok v -> Array.get t2 i = ok v)
  end.

Definition vm_uincl (vm1 vm2:vmap) :=
  forall x, val_uincl (vm1.[x])%vmap (vm2.[x])%vmap.

Lemma val_uincl_refl t v: @val_uincl t v v.
Proof. by elim: t v => //=. Qed.

Hint Resolve val_uincl_refl.    

Lemma sem_sop1_uincl t1 tr (o:sop1 t1 tr) v1 v1' v:
   val_uincl v1 v1' ->
   sem_sop1 o v1 = ok v ->
   exists v', sem_sop1 o v1' = ok v' /\ val_uincl v v'.
Proof.
  case:o v1 v1' v.
  + by move=> v1 v1' v <- Heq;exists v.
  + by move=> ?? v1 v1' v [] H1 H2 [] <- /=;eauto.
  by move=> ?? v1 v1' v [] H1 H2 [] <- /=;eauto.
Qed.

Lemma sem_sop2_uincl t1 t2 tr (o:sop2 t1 t2 tr) v1 v1' v2 v2' v:
   val_uincl v1 v1' ->
   val_uincl v2 v2' ->
   sem_sop2 o v1 v2 = ok v ->
   exists v', sem_sop2 o v1' v2' = ok v' /\ val_uincl v v'.
Proof.
  case:o v1 v1' v2 v2' v;try by move=> v1 v1' v2 v2' v /= <- <- [] <-;eauto.
  + by move=> n v1 v1' v2 v2' v /= H <- /H;eauto.
  by move=> ?? v1 v1' v2 v2' v H1 H2 [] <- /=;eauto.
Qed.

Lemma sem_sop3_uincl t1 t2 t3 tr (o:sop3 t1 t2 t3 tr) v1 v1' v2 v2' v3 v3' v:
   val_uincl v1 v1' ->
   val_uincl v2 v2' ->
   val_uincl v3 v3' ->
   sem_sop3 o v1 v2 v3 = ok v ->
   exists v', sem_sop3 o v1' v2' v3'= ok v' /\ val_uincl v v'.
Proof.
  case:o v1 v1' v2 v2' v3 v3' v;try by move=> v1 v1' v2 v2' v3 v3' v /= <- <- [] <-;eauto.
  move=> n v1 v1' v2 v2' v3 v3' v /= H <- <-.
  rewrite /Array.set;case:ifP => //= ? [] <-.
  exists (FArray.set v1' v2 (ok v3));split=>// i w.
  have := H i w;rewrite /Array.get;case:ifP=>// ?.
  by rewrite !FArray.setP;case:ifP=>//.
Qed.

Lemma sem_expr_uincl vm1 vm2 t (e:pexpr t) v1:
  vm_uincl vm1 vm2 ->
  sem_pexpr vm1 e = ok v1 ->
  exists v2, sem_pexpr vm2 e = ok v2 /\ val_uincl v1 v2.
Proof.
  move=> Hu; elim: e v1=>//=
     [x|z|b|?? o e1 He1|??? o e1 He1 e2 He2|???? o e1 He1 e2 He2 e3 He3] v1.
  + by move=> [] <-;exists (vm2.[x])%vmap.
  + by move=>[] <-;exists (I64.repr z);split=>//;constructor.
  + by move=>[] <-;exists b;split=>//;constructor.
  + case Heq:sem_pexpr=> [v1'|]//=;move:Heq=> /He1 [v2][->] Hu1 /= {He1 e1}.
    by apply sem_sop1_uincl.
  + case Heq:(sem_pexpr vm1 e1)=> [v1'|]//=;move:Heq=> /He1 [v1''][->] Hu1 /= {He1 e1}.
    case Heq:(sem_pexpr vm1 e2)=> [v2'|]//=;move:Heq=> /He2 [v2''][->] Hu2 /= {He2 e2}.
    by apply sem_sop2_uincl.
  case Heq:(sem_pexpr vm1 e1)=> [v1'|]//=;move:Heq=> /He1 [v1''][->] Hu1 /= {He1 e1}.
  case Heq:(sem_pexpr vm1 e2)=> [v2'|]//=;move:Heq=> /He2 [v2''][->] Hu2 /= {He2 e2}.
  case Heq:(sem_pexpr vm1 e3)=> [v3'|]//=;move:Heq=> /He3 [v3''][->] Hu3 /= {He3 e3}.
  by apply sem_sop3_uincl.
Qed.

Lemma write_uincl vm1 vm2 t (r:rval t) v1 v2:
  vm_uincl vm1 vm2 ->
  val_uincl v1 v2 ->
  vm_uincl (write_rval vm1 r v1) (write_rval vm2 r v2).
Proof.
  elim: r v1 v2 vm1 vm2.
  + move=> /= x v1 v2 vm1 vm2 Hvm Hv z.
    case:(x =P z)=> [<-|/eqP ?];first by rewrite !Fv.setP_eq.
    by rewrite !Fv.setP_neq.
  by move=> t1 t2 r1 Hr1 r2 Hr2 v1 v2 vm1 vm2 Hvm [] ??;apply Hr1=>//;apply Hr2. 
Qed.

Section UNDEFINCL.

Let Pi (i:instr) := 
  forall s1 vm1 s2, 
    vm_uincl (evm s1) vm1 ->
    sem_i s1 i s2 ->
    exists vm2, 
       sem_i {|emem := emem s1; evm := vm1|} i {|emem := emem s2; evm := vm2|} /\ 
       vm_uincl (evm s2) vm2.

Let Pc (c:cmd) := 
  forall s1 vm1 s2, 
    vm_uincl (evm s1) vm1 ->
    sem s1 c s2 ->
    exists vm2, 
       sem {|emem := emem s1; evm := vm1|} c {|emem := emem s2; evm := vm2|} /\ 
       vm_uincl (evm s2) vm2.

Let Pf ta tr (fd:fundef ta tr) := 
  forall m1 va va' m2 vr,
    val_uincl va va' ->
    sem_call m1 fd va m2 vr ->
    exists vr', sem_call m1 fd va' m2 vr' /\ val_uincl vr vr'.

Let Hskip : Pc [::].
Proof. 
  by move=> s1 vm1 s2 Hu H;sinversion H;exists vm1;split=>//;constructor.
Qed.

Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
Proof.
  move=> i c Hi Hc s1 vm1 s3 Hu H;sinversion H.
  move=> /Hi in H3;case (H3 _ Hu) => {H3} vm2 [Hi'] /Hc /(_ H5) [vm3] [Hc' Hvm3].
  by exists vm3;split=>//;econstructor;eauto.
Qed.

Let Hbcmd : forall bc,  Pi (Cbcmd bc).
Proof.
  move=> i s1 vm1 s2 Hu H;sinversion H.
  case: i H2 => /=.
  + move=> ? r e. 
    case Heq1: (sem_pexpr _ e)=> [v1|] //= [] <-.
    case: (sem_expr_uincl Hu Heq1)=> v1' [He1 Hincl] /=.
    exists (write_rval vm1 r v1');split;first by constructor=> /=;rewrite He1.
    by apply write_uincl.
  + move=> r e.
    case Heq1: (sem_pexpr _ e)=> [v1|] //=.
    case Heq2: read_mem => [v2|] //= [] <-.
    case: (sem_expr_uincl Hu Heq1)=> v1' [He1 /= Hincl] /=;subst.
    subst;exists (write_rval vm1 r v2);split.
    + by constructor=> /=;rewrite He1 /= Heq2.
    by apply write_uincl.

  move=> e1 e2.
  case Heq1: (sem_pexpr _ e1)=> [v1|] //=.
  case Heq2: (sem_pexpr _ e2)=> [v2|] //=.
  case Heq3: write_mem => [v3|] //= [] <-.
  case: (sem_expr_uincl Hu Heq1)=> v1' [He1 /= Hincl1].
  case: (sem_expr_uincl Hu Heq2)=> v2' [He2 /= Hincl2];subst.
  by exists vm1;split=>//;constructor=>/=;rewrite He1 He2 /= Heq3.
Qed.

Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
Proof.
  move=> e c1 c2 Hc1 Hc2 s1 vm1 s2 Hu H;sinversion H.
  case: (sem_expr_uincl Hu H5)=> cond' [He' /= H];subst.
  case: cond' He' {H5} H6 => He' Hs. 
  + have [vm2 [Hs' Hu2]]:= (Hc1 _ _ _ Hu Hs).
    exists vm2;split=> //;econstructor;eauto.
  have [vm2 [Hs' Hu2]]:= (Hc2 _ _ _ Hu Hs).
  exists vm2;split=> //;econstructor;eauto.
Qed.

Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
Proof.
  move=> i [[dir hi] low] c Hc s1 vm1 s2 Hu H;sinversion H.
  case: (sem_expr_uincl Hu H7)=> vlow' [Hlow' /= H] {H7};subst.
  case: (sem_expr_uincl Hu H8)=> vhi' [Hhi' /= H] {H8};subst.
  have : exists vm2,  
     sem_for i [seq n2w i | i <- wrange dir vlow' vhi']
     {| emem := emem s1; evm := vm1 |} c {| emem := emem s2; evm := vm2 |} /\
     vm_uincl (evm s2) vm2.
  + move=> {Hlow' Hhi'}.
    elim: wrange s1 vm1 Hu H9 => /= [|w ws Hrec] s1 vm1 Hu H;sinversion H.
    + by exists vm1;split=>//;constructor.
    have H := write_uincl i Hu (@val_uincl_refl sword (n2w w)).
    have /(_ _ H) [vm2 /= [H1 /Hrec [//|vm3 [??]]]]:= (Hc _ _ _ _ H3).
    by exists vm3;split=>//;econstructor;eauto.
  move=> [vm2 [Hfor Hu2]];exists vm2;split=>//.
  by econstructor;eauto.
Qed.

Let Hwhile  : forall e c, Pc c -> Pi (Cwhile e c).
Proof.
  move=> e c Hc s1 vm1 s2 Hu H;sinversion H.
  have : exists vm2, 
     sem_while {| emem := emem s1; evm := vm1 |} e c 
               {| emem := emem s2; evm := vm2 |} /\
     vm_uincl (evm s2) vm2.
  elim: H4 vm1 Hu Hc => {e c s1 s2}
    [s e c He| s1 s2 s3 e c He Hs _ Hrec] vm1 Hu Hc.
  + exists vm1;split=>//;constructor.
    by case: (sem_expr_uincl Hu He) => ? [-> <-].
    case: (sem_expr_uincl Hu He) => /= ? [] ??;subst.
    case: (Hc _ _ _ Hu Hs) => vm2 [Hc' Hu2].
    case: (Hrec _ Hu2 Hc) => vm3 [Hw Hu3].
    by exists vm3;split=>//;econstructor;eauto.
  by move=> [vm2 [Hw Hu2]];exists vm2;split=>//;constructor.
Qed.

Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
Proof.
  move=> ta tr x fd a Hf s1 vm1 s2 Hu H;sinversion H.
  sinversion H4;sinversion H5;sinversion H0;sinversion H6.
  case He : sem_pexpr @rarg H7 H8 => [va|]//= _.
  case: (sem_expr_uincl Hu He) => /= va' [] H1 H2 Hs.
  have [vr' [Hs' Hu']]:= Hf _ _ _ _ _ H2 Hs.
  exists (write_rval vm1 x vr');split;first by constructor;rewrite H1.
  by apply write_uincl.
Qed.

Lemma empty_dflt t: is_empty_array (dflt_val t).
Proof. elim: t => //=. Qed.

Lemma empty_vmap0 : all_empty_arr vmap0.
Proof. by move=> x;rewrite Fv.get0; apply empty_dflt. Qed.

Lemma is_full_array_uincl t (v v':st2ty t): 
  is_full_array v -> val_uincl v v' -> v = v'.
Proof.
  elim: t v v' => // [t1 Ht1 t2 Ht2 | s] /=.
  + by move=> [v1 v2] [v1' v2'] /= [] ?? [] /Ht1 <- // /Ht2 <-.
  move=> v v' Hf Hu; apply Array.eq_ext=> w;have := Hu w; have := Hf w.
  rewrite /Array.get;case:ifP => // /andP [] /Z.leb_le ?  /Z.ltb_lt ?.
  by move=> [] // x Hx Hv; rewrite Hx -(Hv _ Hx). 
Qed.

Let Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).
Proof.
  move=> ta tr x c re Hc m1 va va' m2 vr Hu Hs;sinversion Hs.
  sinversion H.
  have [vm2 /= [H1 H2]]:= H5 _ empty_vmap0.
  have := sem_rval2pe re vm2. rewrite -H2.
  have Hu0 : vm_uincl vmap0 vmap0.
  + by move=> z.
  have Hu1 := write_uincl x Hu0 Hu.
  have /= /(_ _ Hu1) [vm3 [? Hu3]]:= Hc _ _ _ _ H1.
  move=> Hre;have [vr' [? Hu2]]:= sem_expr_uincl Hu3 Hre.
  have ?:=  is_full_array_uincl H7 Hu2;subst vr'.
  exists vr;split=>//;constructor=>//.
  move=> vm0 Hall;case (H5 _ Hall) => vm1 /= [Hs1 Heq1].
  have := sem_rval2pe re vm1. rewrite -Heq1.
  have Huvm : vm_uincl vm0 vm0.
  + by move=> z.
  have Hu1' := write_uincl x Huvm Hu.
  have /(_ _ Hu1') [vm4 /= [? Hu4]] := Hc _ _ _ _ Hs1.
  move=> Hre';have [vr' [Heq2 Hu5]]:= sem_expr_uincl Hu4 Hre'.
  have ?:=  is_full_array_uincl H7 Hu5;subst vr'.
  exists vm4;split=>//.
  by have := sem_rval2pe re vm4;rewrite Heq2=>-[].
Qed.

Lemma sem_i_uincl i : Pi i.
Proof.
  apply (@instr_rect2 Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
Qed.

Lemma sem_uincl c : Pc c.
Proof.
  apply (@cmd_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
Qed.

Lemma sem_call_uincl ta tr (fd:fundef ta tr): Pf fd.
Proof.
  apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
Qed.

End UNDEFINCL.