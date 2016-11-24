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
  | Omul       => fun x y => ok (snd (wumul x y))
  | Osub       => fun x y => ok (wsub x y)
  | Omulu      => fun x y => ok (wumul x y)

  | Oeq        => fun (x y : word) => ok (x == y)
  | Oneq       => fun (x y : word) => ok (x != y)
  | Olt        => fun (x y : word) => ok (wlt x y)
  | Ole        => fun (x y : word) => ok (wle x y)
  | Ogt        => fun (x y : word) => ok (wlt y x)
  | Oge        => fun (x y : word) => ok (wle y x)
 
  | Oxor       => fun (x y : word) => ok (I64.xor  x y)  
  | Oland      => fun (x y : word) => ok (I64.and  x y)  
  | Olor       => fun (x y : word) => ok (I64.or   x y)  
  | Olsr       => fun (x y : word) => ok (I64.shru x y)  
  | Olsl       => fun (x y : word) => ok (I64.shl  x y)  

  | Oget n     => @Array.get word n
  | Opair t1 t2 => fun x y => ok (x,y)
  end.

Definition sem_sop3 st1 st2 st3 str (sop : sop3 st1 st2 st3 str) :=
  match sop in sop3 st1 st2 st3 str return 
        st2ty st1 -> st2ty st2 -> st2ty st3 -> exec (st2ty str) with
  | Oset n => @Array.set word n
  | Oaddcarry  => fun x y c => ok (waddcarry x y c)
  | Oaddc      => fun x y c => ok (snd (waddcarry x y c))
  | Osubcarry  => fun x y c => ok (wsubcarry x y c)
  | Osubc      => fun x y c => ok (snd (wsubcarry x y c))
  | Oif t      => fun c x y => ok (if c then x else y)
  end.

Record estate := Estate {
  emem : mem;
  evm  : vmap
}.

Fixpoint sem_pexpr st (s:estate) (pe : pexpr st) : exec (st2ty st) :=
  match pe with
  | Pvar _ v => ok (s.(evm).[ v ]%vmap)
  | Pload pe => 
    sem_pexpr s pe >>= read_mem s.(emem)
  | Pconst c => ok (I64.repr c)
  | Pbool b  => ok b
  | Papp1 st1 str o pe1 =>
      sem_pexpr s pe1 >>= fun v1 =>
      sem_sop1 o v1
  | Papp2 st1 st2 str o pe1 pe2 =>
      sem_pexpr s pe1 >>= fun v1 =>
      sem_pexpr s pe2 >>= fun v2 =>
      sem_sop2 o v1 v2
  | Papp3 st1 st2 st3 str o pe1 pe2 pe3 =>
      sem_pexpr s pe1 >>= fun v1 =>
      sem_pexpr s pe2 >>= fun v2 =>
      sem_pexpr s pe3 >>= fun v3 =>
      sem_sop3 o v1 v2 v3
  end.

Inductive vval : stype -> Type :=
  | Vvar  : forall x : var, vval (vtype x)
  | Vmem  : word -> vval sword
  | Vaset : forall p, Ident.ident -> Array.array p word -> word -> vval sword
  | Vpair : forall st1 st2 : stype, vval st1 -> vval st2 -> vval (st1 ** st2).

Fixpoint rval2vval (s:estate) {t} (r:rval t) : exec (vval t) := 
  match r in rval t return exec (vval t) with
  | Rvar _ x => ok (Vvar x)
  | Rmem e => sem_pexpr s e >>= (fun v => ok (Vmem v))
  | Raset _ p id e =>  
    let x := {| vname := id; vtype := sarr p |} in
    sem_pexpr s e >>= (fun v => ok (@Vaset p id (s.(evm).[ x ]%vmap) v))
  | Rpair _ _ r1 r2 => 
    rval2vval s r1 >>= (fun v1 =>
    rval2vval s r2 >>= (fun v2 =>
    ok (Vpair v1 v2)))
  end.

Fixpoint write_vval (s:estate) {t} (l:vval t) : st2ty t -> exec estate :=
  match l in vval t_ return st2ty t_ -> exec estate with
  | Vvar x => fun v => ok {|emem := s.(emem); evm := s.(evm).[x <- v]%vmap|}
  | Vmem p => fun v => 
     write_mem s.(emem) p v >>= (fun m =>
      ok {|emem := m;  evm := s.(evm) |})
  | Vaset p id t w => fun v =>
     let x := {| vname := id; vtype := sarr p |} in                   
      Array.set t w v >>= (fun t =>
       ok {|emem := s.(emem); evm := s.(evm).[x <- t]%vmap|})
  | Vpair _ _ l1 l2 => fun v =>
     write_vval s l2 v.2 >>= (fun s =>
      write_vval s l1 v.1)
  end.

Definition write_rval (s:estate) {t} (l:rval t) (v:st2ty t): exec estate :=
  rval2vval s l >>= (fun l => write_vval s l v).

(* Initial map *)

(* ** Instructions
 * -------------------------------------------------------------------- *)

Section SEM. 

Definition wrange d (n1 n2 : word) :=
  if (n1 <=? n2)%Z then 
    let idxs := iota (w2n n1) (S (w2n n2 - w2n n1)) in
    match d with
    | UpTo   => idxs
    | DownTo => rev idxs
    end
  else [::].

Definition sem_range (s : estate) (r : range) :=
  let: (d,pe1,pe2) := r in
  sem_pexpr s pe1 >>= fun w1 =>
  sem_pexpr s pe2 >>= fun w2 =>
  ok [seq n2w n | n <- wrange d w1 w2].

Inductive sem : estate -> cmd -> estate -> Prop :=
| Eskip s :
    sem s [::] s

| Eseq s1 s2 s3 i c :
    sem_I s1 i s2 -> sem s2 c s3 -> sem s1 (i::c) s3

with sem_I : estate -> instr -> estate -> Prop :=
| EmkI info i s1 s2: 
    sem_i s1 i s2 ->
    sem_I s1 (MkI info i) s2

with sem_i : estate -> instr_r -> estate -> Prop :=

| Eassgn s1 s2 t (x:rval t) tag e:
    sem_pexpr s1 e >>= (write_rval s1 x) = ok s2 -> 
    sem_i s1 (Cassgn x tag e) s2

| Eif s1 s2 (pe : pexpr sbool) cond c1 c2 :
    sem_pexpr s1 pe = ok cond ->
    sem s1 (if cond then c1 else c2) s2 ->
    sem_i s1 (Cif pe c1 c2) s2

| Ecall sta str s1 m2 s2
        (rv_res : rval str) (fd : fundef sta str)
        (pe_arg : pexpr sta) (res : st2ty str) :
    let rarg := sem_pexpr s1 pe_arg in
    isOk rarg ->
    sem_call s1.(emem) fd (rdflt_ rarg) m2 res ->
    write_rval {|emem:= m2; evm := s1.(evm) |} rv_res res = ok s2 ->
    sem_i s1
          (Ccall rv_res fd pe_arg)
          s2
    
| EFor s1 s2 iv dir (low hi : pexpr sword) c vlow vhi :
    sem_pexpr s1 low = ok vlow ->
    sem_pexpr s1 hi  = ok vhi  ->
    sem_for iv (map n2w (wrange dir vlow vhi)) s1 c s2 ->
    sem_i s1 (Cfor iv (dir, low, hi) c) s2

| Ewhile s1 s2 e c :
   sem_while s1 e c s2 ->
   sem_i s1 (Cwhile e c) s2

with sem_while : estate -> pexpr sbool -> cmd -> estate -> Prop := 
| EWhileDone s (e:pexpr sbool) c :
    sem_pexpr s e = ok false ->
    sem_while s e c s
| EWhileOne s1 s2 s3 (e:pexpr sbool) c :  
    sem_pexpr s1 e = ok true ->
    sem s1 c s2 ->
    sem_while s2 e c s3 ->
    sem_while s1 e c s3
    
with sem_for : rval sword -> seq word -> estate -> cmd -> estate -> Prop :=
| EForDone s iv c :
    sem_for iv [::] s c s

| EForOne s1 s1' s2 s3 (iv : rval sword) w ws c :
    write_rval s1 iv w = ok s1' ->
    sem s1' c s2 ->
    sem_for iv ws s2 c s3 ->
    sem_for iv (w :: ws) s1 c s3

with sem_call : 
  forall sta str, mem -> fundef sta str -> st2ty sta -> mem -> st2ty str -> Prop :=

| EcallRun sta str m1 m2 rres (f:fundef sta str) (varg : st2ty sta):
    (* semantics defined for all vm0 *)
    (forall vm0, all_empty_arr vm0 -> exists s1 vm2,
       [/\ 
        write_rval (Estate m1 vm0) f.(fd_arg) varg = ok s1, 
       sem s1 f.(fd_body) (Estate m2 vm2) &
       sem_pexpr (Estate m2 vm2) f.(fd_res) = ok rres]) ->
    is_full_array rres ->
    sem_call m1 f varg m2 rres.

(* -------------------------------------------------------------------- *)
Scheme sem_Ind := Minimality for sem Sort Prop
with   sem_i_Ind := Minimality for sem_i Sort Prop
with   sem_I_Ind := Minimality for sem_I Sort Prop
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
  sem_I s1 i s2 -> sem s1 [::i] s2.
Proof.
  move=> Hi; apply (Eseq Hi);constructor.
Qed.

Definition sem_fail (s1 : estate) (c : cmd) : Prop :=
  forall s2, not (sem s1 c s2).

Definition sem_i_fail (s1 : estate) (i : instr) : Prop :=
  forall s2, not (sem_I s1 i s2).

Definition vmap_eq_except (s : Sv.t) (vm1 vm2 : vmap) :=
  forall x, ~Sv.In x s -> vm1.[x]%vmap = vm2.[x]%vmap.

Notation "vm1 = vm2 [\ s ]" := (vmap_eq_except s vm1 vm2) (at level 70, vm2 at next level,
  format "'[hv ' vm1  '/' =  vm2  '/' [\ s ] ']'").

Lemma vrvP_aux s t (r:rval t) rv v s1 s2 : 
  rval2vval s r = ok rv ->
  write_vval s1 rv v = ok s2 -> 
  s1.(evm) = s2.(evm) [\ vrv r].
Proof.
(*
  elim: r rv v s1 s2 => [x | e | ?? r1 Hr1 r2 Hr2] r v s1 s2/=.
  + move=> [] <- [] <- z;rewrite vrv_var => ?. 
    by rewrite Fv.setP_neq //;apply /eqP; SvD.fsetdec.
  + by case Heq:sem_pexpr => [p|] //= [] <- /=; case: write_mem => [m2|] //= [] <-.
  case Heq1: (rval2vval s r1) => [v1|] //=.
  case Heq2: (rval2vval s r2) => [v2|] //= [] <- /=.
  case Heq2' : write_vval => [s2'|] //=.
  move=> /Hr2 in Heq2';move=> /Heq2' in Heq2.
  move=> /Hr1 -/(_ Heq1) H1 z;rewrite vrv_pair=> ?.
  rewrite Heq2;first apply H1;SvD.fsetdec.
Qed.
*)
Admitted.

Lemma vrvP t (r:rval t) v s1 s2 : write_rval s1 r v = ok s2 -> 
           s1.(evm) = s2.(evm) [\ vrv r].
Proof.
  rewrite /write_rval.
  case Heq : rval2vval => [rv|] //=;apply: vrvP_aux Heq.                                 
Qed.

Lemma writeP c s1 s2 : 
   sem s1 c s2 -> s1.(evm) = s2.(evm) [\ write_c c].
Proof.
(*
  apply (@cmd_rect
           (fun i => forall s1 s2, sem_i s1 i s2 -> s1.(evm) = s2.(evm) [\ write_i i])
           (fun c => forall s1 s2, sem   s1 c s2 -> s1.(evm) = s2.(evm) [\ write_c c])
           (fun _ _ _ => True)) => /= {c s1 s2}
    [ |i c1 Hi Hc1|t x e|e c1 c2 Hc1 Hc2|x rn c Hc|e c Hc|?? x f a _|//] s1 s2 Hsem;
    inversion Hsem=>{Hsem};subst=> // z.
  + rewrite write_c_cons => Hz;rewrite (Hi _ _ H2) ?(Hc1 _ _ H4) //; SvD.fsetdec. 
  + rewrite write_i_assgn=> Hin;sinversion H2;sinversion H3.
    case: sem_pexpr H4 => [v|] //= Hw.
    apply: vrvP Hw z Hin.
  + by rewrite write_i_if=> ?; case:cond H4 H5=> H4 H5;[apply Hc1 | apply Hc2] => //;
     SvD.fsetdec. 
  + rewrite write_i_for. 
    elim: H6 Hc=> //= {H3 H5 dir s1 s2 c} //=.
    move => s1 s1' s2 s3 iv w1 w2 c Hw Hsem Hfor Hrec Hc Hin.
    rewrite -Hrec // -(Hc _ _ Hsem);last by SvD.fsetdec. 
    by apply: (vrvP Hw);SvD.fsetdec.
  + rewrite write_i_while;elim: H3 Hc => //= {s1 s2 e c}.
    move => s1 s2 s3 e c He Hsem Hw Hrec Hc Hin.
    by rewrite -Hrec // -(Hc _ _ Hsem) /= -?vrvP //; SvD.fsetdec. 
  rewrite write_i_call=> Hin;sinversion H1;sinversion H4;sinversion H0; by apply: (vrvP H8). 
Qed.
*)
Admitted.

Lemma write_iP i s1 s2 : 
   sem_i s1 i s2 -> s1.(evm) = s2.(evm) [\ write_i i].
Proof.
(*
  move=> /sem_seq1 /writeP.
  have := write_c_cons i [::].
  move=> Heq H x Hx;apply H; SvD.fsetdec. 
Qed.
*)
Admitted.

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

Lemma disjoint_eq_on s t (r:rval t) s1 s2 v: 
  disjoint s (vrv r) ->
  write_rval s1 r v = ok s2 ->
  s1.(evm) =[s] s2.(evm).
Proof.
(*
  rewrite /disjoint /is_true Sv.is_empty_spec /write_rval.
  case Heq:rval2vval=> [rv|] //= => H Hw z Hin.
  move: {1} s1 Heq => s0 Heq.
  elim: r rv v s1 s2 Heq H Hw => [x | e | ?? rv1 Hrv1 rv2 Hrv2] rv v s1 s2 /=.
  + by move=> [] <- /=;rewrite vrv_var=> ? [] <- /=;rewrite Fv.setP_neq //;apply /eqP;SvD.fsetdec. 
  + case Heq: sem_pexpr => [p|] //= [] <-;rewrite vrv_mem => /= ?.
    by case write_mem => [m'|] //= [] <-. 
  case Heq1 : (rval2vval s0 rv1) => [vr1|]//=.
  case Heq2 : (rval2vval s0 rv2) => [vr2|]//= [] <- /=.
  rewrite vrv_pair /= => Hd.
  case Heq2' : write_vval => [s1'|]//=.
  move=> /Hrv2 in Heq2';move=> /Heq2' in Heq2;rewrite Heq2;last by SvD.fsetdec.
  move=> /Hrv1 -/(_ Heq1) -> //;SvD.fsetdec. 
Qed. *)
Admitted.

Lemma read_e_eq_on t (e:pexpr t) s m vm vm':
  vm =[read_e_rec e s] vm'->
  sem_pexpr (Estate m vm) e = sem_pexpr (Estate m vm') e.
Proof.
(*
  elim:e s => //=.
  + by move=> x s H;rewrite H //;SvD.fsetdec. 
  + by move=> e He ? /He ->.
  + by move=> ?? o e1 He1 s Heq;rewrite (He1 s Heq).
  + move=> ??? o e1 He1 e2 He2 s Heq;rewrite (He1 _ Heq) (He2 s) //. 
    by apply: eq_onI Heq;rewrite (read_eE e1);SvD.fsetdec.
  move=> ???? o e1 He1 e2 He2 e3 He3 s Heq.    
  rewrite (He1 _ Heq); have Heq2 : vm =[read_e_rec e2 (read_e_rec e3 s)]  vm'.
  + by apply: eq_onI Heq;rewrite (read_eE e1);SvD.fsetdec.   
  rewrite (He2 _ Heq2) (He3 s) //.     
  by apply: eq_onI Heq2;rewrite (read_eE e2);SvD.fsetdec.
Qed.
*)
Admitted.

Lemma write_vval_eq_on s0 t s (x:rval t) (rv:vval t) v m1 m2 vm1 vm2 vm1': 
  rval2vval s0 x = Ok error rv ->
  write_vval {| emem := m1; evm := vm1 |} rv v = ok {|emem := m2; evm := vm2 |} ->
  vm1 =[Sv.diff s (vrv x)] vm1' ->
  exists vm2' : vmap,
   vm2 =[s]  vm2' /\
   write_vval {|emem:= m1; evm := vm1'|} rv v = ok {|emem:= m2; evm := vm2'|}.
Proof.
(*
  elim: x rv v s m1 m2 vm1 vm2 vm1' => [x | e | ?? x1 Hx1 x2 Hx2] /= rv v s m1 m2 vm1 vm2 vm1'.
  + move=> [] <- [] <- <- Hvm;exists (vm1'.[x <-v])%vmap;split=> //=.
    move=> z Hz;case: (x =P z) => [<-|/eqP Heq];first by rewrite !Fv.setP_eq.
    rewrite !Fv.setP_neq //;apply Hvm. 
    by move /eqP: Heq;rewrite vrv_var;SvD.fsetdec.
  + case Heq: sem_pexpr => [ve|] //= [] <- /=.
    case Heq': write_mem => [m2'|] //= [] -> <- Hvm;exists vm1';split=>//.
    by apply: eq_onI Hvm;rewrite vrv_mem;SvD.fsetdec.
  case Heq1: (rval2vval _ x1) => [v1|] //=.
  case Heq2: (rval2vval _ x2) => [v2|] //= [] <- /=.
  case Heq2': write_vval => [[m vm]|] //= Heq1' Hvm.
  have [|vm3 [Hvm3 Hw3]]:= Hx2 _ _ (Sv.diff s (vrv x1)) _ _ _ _ vm1' Heq2 Heq2'.
  + by apply: eq_onI Hvm;rewrite vrv_pair;SvD.fsetdec.
  have [vm4 [Hvm4 Hw4]]:= Hx1 _ _ s _ _ _ _ vm3 Heq1 Heq1' Hvm3.
  by exists vm4;split=>//;rewrite Hw3.
Qed.
*)
Admitted.

Lemma read_rv_eq_on (t : stype) (x : rval t) (s : Sv.t) (m : mem) (vm vm' : vmap):
  vm =[read_rv_rec x s]  vm' ->
  rval2vval {| emem := m; evm := vm |} x =
  rval2vval {| emem := m; evm := vm' |} x.
Proof.
(*
  elim: x s => [x | e | ?? x1 Hx1 x2 Hx2] s //=.
  + by move=> /read_e_eq_on ->.
  move=> Hvm;rewrite (Hx1 (read_rv_rec x2 s)).
  + case: (rval2vval _ x1) => [rv1|] //=.
    rewrite (Hx2 s) //.
    by apply: eq_onI Hvm; rewrite (read_rvE _ x1);SvD.fsetdec.
  by apply: eq_onI Hvm; rewrite (read_rvE _ x1);SvD.fsetdec.  
Qed.
*)
Admitted.

Lemma write_rval_eq_on t s (x:rval t) v m1 m2 vm1 vm2 vm1': 
  write_rval {| emem := m1; evm := vm1 |} x v = ok {|emem := m2; evm := vm2 |} ->
  vm1 =[ read_rv_rec x (Sv.diff s (vrv x))] vm1' ->
  exists vm2' : vmap,
   vm2 =[s]  vm2' /\
   write_rval {|emem:= m1; evm := vm1'|} x v = ok {|emem:= m2; evm := vm2'|}.
Proof.
  rewrite /write_rval=> Hw Heq;move: Hw.
  have -> := @read_rv_eq_on _ x (Sv.diff s (vrv x)) m1 vm1 vm1' Heq.
  case Heq': rval2vval=> [rv|] //= Hw.
  apply: (write_vval_eq_on Heq' Hw);apply: eq_onI Heq;rewrite read_rvE;SvD.fsetdec.
Qed.

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
(*
  case:o v1 v1' v2 v2' v3 v3' v;try by move=> v1 v1' v2 v2' v3 v3' v /= <- <- [] <-;eauto.
  move=> n v1 v1' v2 v2' v3 v3' v /= H <- <-.
  rewrite /Array.set;case:ifP => //= ? [] <-.
  exists (FArray.set v1' v2 (ok v3));split=>// i w.
  have := H i w;rewrite /Array.get;case:ifP=>// ?.
  by rewrite !FArray.setP;case:ifP=>//.
Qed.
*)
Admitted.


Lemma sem_expr_uincl s1 vm2 t (e:pexpr t) v1:
  vm_uincl s1.(evm) vm2 ->
  sem_pexpr s1 e = ok v1 ->
  exists v2, sem_pexpr (Estate s1.(emem) vm2) e = ok v2 /\ val_uincl v1 v2.
Proof.
(*
  move=> Hu; elim: e v1=>//=
     [x|e He|z|b|?? o e1 He1|??? o e1 He1 e2 He2|???? o e1 He1 e2 He2 e3 He3] v1.
  + by move=> [] <-;exists (vm2.[x])%vmap.
  + case Heq:sem_pexpr => [v|] //=;case (He _ Heq) => p [Hsem Hp Hr];exists v1.
    by rewrite Hsem -Hp.
  + by move=>[] <-;exists (I64.repr z);split=>//;constructor.
  + by move=>[] <-;exists b;split=>//;constructor.
  + case Heq:sem_pexpr=> [v1'|]//=;move:Heq=> /He1 [v2][->] Hu1 /= {He1 e1}.
    by apply sem_sop1_uincl.
  + case Heq:(sem_pexpr _ e1)=> [v1'|]//=;move:Heq=> /He1 [v1''][->] Hu1 /= {He1 e1}.
    case Heq:(sem_pexpr _ e2)=> [v2'|]//=;move:Heq=> /He2 [v2''][->] Hu2 /= {He2 e2}.
    by apply sem_sop2_uincl.
  case Heq:(sem_pexpr _ e1)=> [v1'|]//=;move:Heq=> /He1 [v1''][->] Hu1 /= {He1 e1}.
  case Heq:(sem_pexpr _ e2)=> [v2'|]//=;move:Heq=> /He2 [v2''][->] Hu2 /= {He2 e2}.
  case Heq:(sem_pexpr _ e3)=> [v3'|]//=;move:Heq=> /He3 [v3''][->] Hu3 /= {He3 e3}.
  by apply sem_sop3_uincl.
Qed.
*)
Admitted.

Lemma rval2vval_uincl s1 vm1 t rv (r:rval t):
  vm_uincl (evm s1) vm1 ->
  rval2vval s1 r = ok rv -> 
  rval2vval (Estate (emem s1) vm1) r = ok rv.
Proof.
(*
  move=> Hs; elim: r rv => [x | e | ?? x1 Hx1 x2 Hx2] rv //=.
  + case Heq: sem_pexpr=> [p|] //= [] <-.
    by case (sem_expr_uincl Hs Heq) => ? /= [-> <-].    
  case Heq1:(rval2vval _ x1) => [v1|]//=;move=> /Hx1 in Heq1.
  case Heq2:(rval2vval _ x2) => [v2|]//=;move=> /Hx2 in Heq2 => -[] <-.
  by rewrite Heq1 Heq2.
Qed.
*)
Admitted.

Lemma write_uincl s1 s2 vm1 t (r:rval t) v1 v2:
  vm_uincl s1.(evm) vm1 ->
  val_uincl v1 v2 ->
  write_rval s1 r v1 = ok s2 ->
  exists vm2, write_rval (Estate (emem s1) vm1) r v2 = ok (Estate (emem s2) vm2) /\ 
              vm_uincl s2.(evm) vm2.
Proof.
(*
  rewrite /write_rval;case Heq: rval2vval => [rv|] //=.
  move=> Hvm Hv;move=> /(rval2vval_uincl Hvm) in Heq;rewrite Heq /= => {Heq}.
  elim: rv s1 s2 vm1 v1 v2 Hvm Hv => [x | p | ?? x1 Hx1 x2 Hx2] s1 s2 vm1 v1 v2 /= Hvm.
  + move=> Hv [] <- /=;exists (vm1.[x <- v2])%vmap;split=>// z.
    case:(x =P z)=> [<-|/eqP ?];first by rewrite !Fv.setP_eq.
    by rewrite !Fv.setP_neq.
  + by move=> <-;case Heq: write_mem => [m|]//= [] <- /=;exists vm1.
  move=> []Hv1 Hv2;case Heq2:write_vval => [s1'|] //= Heq1.
  have [vm2 [Heq2' Hvm2]]:= Hx2 _ _ _ _ _ Hvm Hv2 Heq2. 
  have [vm3 [Heq1' Hvm3]] := Hx1 _ _ _ _ _ Hvm2 Hv1 Heq1. 
  by exists vm3;split=> //;rewrite Heq2'.
Qed.
*)
Admitted.

Section UNDEFINCL.
(*
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

Let Hbcmd : forall t (x:rval t) e,  Pi (Cassgn x e).
Proof.
  move=> t x e s1 vm1 s2 Hu H;sinversion H.
  sinversion H3;sinversion H4;case Heq1:sem_pexpr H5 => [v1|] //=.
  case: (sem_expr_uincl Hu Heq1)=> v1' [He1 Hincl] /= Hw.  
  have [vm2 [Hw2 Hu2]]:= write_uincl Hu Hincl Hw.
  by exists vm2;split=>//;constructor;rewrite He1.
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
    have [vm2 /= [Hw Hu2]] := write_uincl Hu (@val_uincl_refl sword (n2w w)) H2.
    have [vm2' /= [H1 /Hrec [//|vm3 [??]]]]:= Hc _ _ _ Hu2 H4.
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
  sinversion H6;sinversion H5;sinversion H2;sinversion H0.
  case He : sem_pexpr @rarg H7 H8 => [va|]//= _.
  case: (sem_expr_uincl Hu He) => /= va' [] H1 H2 Hs.
  have [vr' [Hs' Hu']]:= Hf _ _ _ _ _ H2 Hs.
  have /(_ _ Hu) [vm2 [Hw2 Hu2]]:= write_uincl _ Hu' H9.
  by exists vm2;split=>//;econstructor;eauto;rewrite H1.
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

Let Hfunc : forall ta tr (x:rval ta) c (re:pexpr tr), Pc c -> Pf (FunDef x c re).
Proof.
  move=> ta tr x c re Hc m1 va va' m2 vr Hu Hs;sinversion Hs.
  sinversion H.
  have [s2 /= [vm [Hw Hsc Hsr]]]:= H5 _ empty_vmap0.
  have Hu0 : vm_uincl vmap0 vmap0 by move=> z.
  have /(_ _ Hu0) [vm1/= [Hw1 Hu1]]:= write_uincl _ Hu Hw.
  have [vm2 /= [Hsc' Hu2]] := Hc _ _ _ Hu1 Hsc.
  have /(_ _ Hu2)[vr' [Hvr' Hu']]:= sem_expr_uincl _ Hsr.
  exists vr';split=>//;econstructor;last by have <- := is_full_array_uincl H7 Hu'.
  move=> {vm Hw Hsc Hsr vm1 Hw1 Hu1 vm2 Hsc' Hu2 Hvr'}.
  move=> vm0 Hall;case (H5 _ Hall) => s1 /= [vm [Hw Hsc Hsr]].
  have Huvm : vm_uincl vm0 vm0 by move=> z.
  have /(_ _ Huvm) [vm1/= [Hw1 Hu1]]:= write_uincl _ Hu Hw.
  have [vm2 /= [Hsc' Hu2]] := Hc _ _ _ Hu1 Hsc.
  have /(_ _ Hu2)[vr'' [Hvr' Hu'']]:= sem_expr_uincl _ Hsr.
  have ?:=  is_full_array_uincl H7 Hu';subst vr'.
  have ?:=  is_full_array_uincl H7 Hu'';subst vr''.
  by exists {| emem := emem s1; evm := vm1 |}, vm2;split.
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
*)
End UNDEFINCL.