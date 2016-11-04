(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr memory dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
  
Section CMD.

  Variable dead_code_i : instr ->  Sv.t -> result unit (Sv.t * cmd).

  Fixpoint dead_code (c:cmd) (s:Sv.t) : result unit (Sv.t * cmd) :=
    match c with
    | [::] => Ok unit (s, [::])
    | i::c =>
      dead_code c s >>= (fun (sc:Sv.t * cmd) => let (s, c) := sc in
      dead_code_i i s >>= (fun (si:Sv.t * cmd) => let (s,ic) := si in
      Ok unit (s, ic ++ c)))
    end.

End CMD.

Section LOOP.

  Variable dead_code_c : Sv.t -> result unit (Sv.t * cmd).

  Fixpoint loop (n:nat) (rx:Sv.t) (wx:Sv.t) (s:Sv.t) : result unit (Sv.t * cmd) :=
    match n with
    | O => Error tt
    | S n =>
      dead_code_c s >>=  (fun (sc:Sv.t * cmd) => let (s', c') := sc in
      let s' := Sv.union rx (Sv.diff s' wx) in
      if Sv.subset s' s then Ok unit (s,c') 
      else loop n rx wx (Sv.union s s'))
    end.

  Fixpoint wloop (n:nat) (s:Sv.t) : result unit (Sv.t * cmd) :=
    match n with
    | O => Error tt
    | S n =>
      dead_code_c s >>=  (fun (sc:Sv.t * cmd) => let (s', c') := sc in
      if Sv.subset s' s then Ok unit (s,c') 
      else wloop n (Sv.union s s'))
    end.

End LOOP.

Fixpoint write_mem t (r:rval t) : bool := 
  match r with 
  | Rvar _ => false
  | Rmem _ => true
  | Rpair _ _ r1 r2 => write_mem r1 || write_mem r2
  end.

Definition nb_loop := 100%coq_nat.

Fixpoint dead_code_i (i:instr) (s:Sv.t) {struct i} : result unit (Sv.t * cmd) := 
  match i with
  | Cassgn t rv e =>
    let w := write_i i in
    if disjoint s w && negb (write_mem rv) then Ok unit (s,[::])
    else Ok unit (read_rv_rec rv (read_e_rec e (Sv.diff s w)), [::i])

  | Cif b c1 c2 => 
    dead_code dead_code_i c1 s >>= (fun (sc:Sv.t * cmd) => let (s1,c1) := sc in
    dead_code dead_code_i c2 s >>= (fun (sc:Sv.t * cmd) => let (s2,c2) := sc in
    Ok unit (read_e_rec b (Sv.union s1 s2), [:: Cif b c1 c2])))
  | Cfor x (dir, e1, e2) c =>
    loop (dead_code dead_code_i c) nb_loop (read_rv x) (vrv x) s >>= 
    (fun (sc:Sv.t * cmd) => let (s, c) := sc in
    Ok unit (read_e_rec e1 (read_e_rec e2 s),[::Cfor x (dir,e1,e2) c]))
  | Cwhile e c =>
    wloop (dead_code dead_code_i c) nb_loop (read_e_rec e s) >>= 
    (fun (sc:Sv.t * cmd) => let (s, c) := sc in
    Ok unit (s,[::Cwhile e c]))
  | Ccall ta tr x fd arg =>
    dead_code_call fd >>= (fun fd => 
    Ok unit (read_e_rec arg (read_rv_rec x (Sv.diff s (vrv x))), [::Ccall x fd arg]))
  end

with dead_code_call ta tr (fd:fundef ta tr) := 
  match fd with
  | FunDef ta tr p c r =>
    dead_code dead_code_i c (read_e r) >>= (fun (sc:Sv.t * cmd) => let (_, c) := sc in
    Ok unit (FunDef p c r))
  end.

Lemma write_memP t (x:rval t) v m1 m2 vm1 vm2:
  ~~ write_mem x -> 
  write_rval {| emem := m1; evm := vm1 |} x v = ok {| emem := m2; evm := vm2 |} ->
  m1 = m2.
Proof.
  rewrite /write_rval; case Heq: rval2vval=> [vr|]//=.
  move: {1}{| emem := m1; evm := vm1 |} Heq => s.
  elim: x vr v m1 m2 vm1 vm2 => //= [x|?? x1 Hx1 x2 Hx2] vr v m1 m2 vm1 vm2.
  + by move=> [] <- _ /= [].
  case Heq1: (rval2vval _ x1) => [vr1|] //=.
  case Heq2: (rval2vval _ x2) => [vr2|] //= [] <-.
  rewrite negb_or=> /andP [H1 H2] /=.
  case Heq2' : write_vval => [[m vm]|] //= /Hx1 <- //.
  by apply: Hx2 Heq2'.
Qed.

Section PROOF.

  Let Pi (i:instr) := 
    forall mem1 mem2 vm1 vm2, sem_i (Estate mem1 vm1) i (Estate mem2 vm2) ->
    forall s2, 
      match dead_code_i i s2 with
      | Ok (s1, c') =>
        forall vm1', vm1 =[s1] vm1' ->
        exists vm2', vm2 =[s2] vm2' /\ 
          sem (Estate mem1 vm1') c' (Estate mem2 vm2')
      | _ => True
      end.

  Let Pc (c:cmd) := 
    forall mem1 mem2 vm1 vm2, sem (Estate mem1 vm1) c (Estate mem2 vm2) ->
    forall s2, 
      match dead_code dead_code_i c s2 with
      | Ok (s1, c') =>
        forall vm1', vm1 =[s1] vm1' ->
        exists vm2', vm2 =[s2] vm2' /\ 
          sem (Estate mem1 vm1') c' (Estate mem2 vm2')
      | _ => True
      end.

  Let Pf ta tr (fd:fundef ta tr) := 
    forall mem mem' va vr, 
      match dead_code_call fd with
      | Ok fd' => 
        sem_call mem fd va mem' vr -> 
        sem_call mem fd' va mem' vr
      | _ => True
      end.

  Let Hskip : Pc [::].
  Proof. 
    move=> m1 m2 vm1 vm2 /= H;inversion H;subst=> s2 st1' Heq;exists st1';split=>//.
    constructor.
  Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc m1 m3 vm1 vm3 H;inversion H;clear H;subst=> /=.
    case: s2 H3 H5  => m2 vm2 H3 H5 s3.
    have := Hc _ _ _ _ H5 s3;case: (dead_code dead_code_i c s3) => /= [[s2 c'] | //] Hc'.
    have := Hi _ _ _ _ H3 s2;case: (dead_code_i i s2) => [[s1 i']|] //=Hi' vm1' /Hi'.
    move=> [vm2' [Heq2 Hsi']];case: (Hc' _ Heq2) => [vm3' [Heq3 Hsc']].
    exists vm3';split=> //.
    by apply: sem_app Hsi' Hsc'.
  Qed.

  Let Hbcmd : forall t (x:rval t) e,  Pi (Cassgn x e).
  Proof. 
    move=> t x e m1 m2 vm1 vm2 H;sinversion H=> /= s2.
    sinversion H3;sinversion H4=> /=.
    case: ifPn.
    + move=> /andP[] Hdisj Hmem vm1' Hvm;exists vm1'. 
      case Heq: sem_pexpr H5 => [v|] //= H5.
      rewrite (write_memP Hmem H5);split;last by constructor.
      by apply: eq_onT Hvm;apply eq_onS;apply (disjoint_eq_on Hdisj H5).
    move=> ?;case Heq: sem_pexpr H5 => [v|] //= Hw vm1' Hvm.
    have /(_ s2 vm1') [|vm2' [Hvm2 Hw2]] := write_rval_eq_on Hw.    
    + by apply: eq_onI Hvm;rewrite !read_rvE read_eE write_i_assgn;SvD.fsetdec.
    exists vm2';split=>//;apply sem_seq1;constructor.
    have <- := @read_e_eq_on _ e Sv.empty m1 vm1 vm1';first by rewrite Heq.
    by apply: eq_onI Hvm;rewrite !read_rvE !read_eE;SvD.fsetdec.
  Qed.

  Let Hif   : forall e c1 c2,  Pc c1 -> Pc c2 -> Pi (Cif e c1 c2).
  Proof.
    move=> e c1 c2 Hc1 Hc2 m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    move=> s3 /=.
    case Heq1 : (dead_code dead_code_i c1 s3) => [[s1 c1']|//].
    case Heq2 : (dead_code dead_code_i c2 s3) => [[s2 c2']|] //= vm1' Hr.
    case: cond H5 H6 => H5 H6.
    + have := Hc1 m1 m2 vm1 vm2 H6 s3; rewrite Heq1=> /(_ vm1') [].
      + by apply: eq_onI Hr;rewrite read_eE;SvD.fsetdec.
      move=> vm2' [Heq' Hsem];exists vm2';split => //.
      by apply sem_seq1;apply Eif with true => //=; rewrite -(read_e_eq_on m1 Hr).
    have := Hc2 m1 m2 vm1 vm2 H6 s3; rewrite Heq2=> /(_ vm1') [].
    + by apply: eq_onI Hr;rewrite read_eE;SvD.fsetdec.
    move=> vm2' [Heq' Hsem];exists vm2';split => //.
    by apply sem_seq1;apply Eif with false => //=; rewrite -(read_e_eq_on m1 Hr).
  Qed.

  Opaque nb_loop.

  Let Hfor  : forall i rn c, Pc c -> Pi (Cfor i rn c).
  Proof.
    move=> i [[dir low] hi] c Hc m1 m2 vm1 vm2 H;sinversion H=> /=.
    elim: nb_loop => //=.
    move=> n Hrec s2.
    case Heq : (dead_code dead_code_i c s2) => [[s1 c']|] //=.
    case : (boolP (Sv.subset (Sv.union (read_rv i) (Sv.diff s1 (vrv i))) s2)) => /=.
    + move=> /Sv.subset_spec Hsub.
      pose st1 := {| emem := m1; evm := vm1 |}; pose st2:= {| emem := m2; evm := vm2 |}.
      rewrite (_:vm1 = evm st1) // (_:vm2 = evm st2) //.
      rewrite (_:m1 = emem st1) // (_:m2 = emem st2) //.
      have: sem_for i [seq n2w i | i <- wrange dir vlow vhi] st1 c st2 ->
            dead_code dead_code_i c s2 = Ok unit (s1, c') -> Pc c -> 
            Sv.Subset (Sv.union (read_rv i) (Sv.diff s1 (vrv i))) s2 ->
            forall vm1',  evm st1 =[s2]  vm1' ->
             exists vm2' : vmap, 
             evm st2 =[s2]  vm2' /\
             sem_for i [seq n2w i | i <- wrange dir vlow vhi]
                {| emem := emem st1; evm := vm1' |} c'
                {| emem := emem st2; evm := vm2' |}.
      + move: st1 st2 => {Hrec H7 H8 H9 Hc Heq Hsub vm1 vm2 m1 m2} st1 st2.
        elim=> {st1 st2 c i} [s i c
                             | [m1 vm1] [m4 vm4] [m2 vm2] [m3 vm3] i w ws c Hw Hsc Hsf Hrec] /=
            Heq Hc Hsub vm1' Hvm1.  
        + by exists vm1';split=> //;constructor.
        have /(_ s1 vm1') [|vm4' [Hvm4 Hw4]] := write_rval_eq_on Hw.
        + by apply: eq_onI Hvm1;rewrite read_rvE;SvD.fsetdec.
        have := Hc _ _ _ _ Hsc s2;rewrite Heq=> /(_ _ Hvm4) [vm2' [Hvm2 Hsem2]].
        elim (Hrec Heq Hc Hsub vm2' Hvm2) => vm3' /= [Hvm3 Hsem3].
        by exists vm3';split=> //;apply: EForOne Hsem3;eauto.
      move=> /(_ H9 Heq Hc Hsub) H vm1' Hvm1;case: (H vm1').
      + by apply: eq_onI Hvm1;rewrite !read_eE;SvD.fsetdec.
      move=> vm2' [Hvm2 Hsem];exists vm2';split => //.
      apply sem_seq1;apply EFor with vlow vhi => //=.
      + by rewrite -(read_e_eq_on m1 Hvm1).
      have Hvm: evm st1 =[read_e_rec hi s2]  vm1'.
      + by apply: eq_onI Hvm1;rewrite (read_eE low);SvD.fsetdec.
      by rewrite -(read_e_eq_on m1 Hvm).
    move=> _;have := Hrec (Sv.union s2 (Sv.union (read_rv i) (Sv.diff s1 (vrv i)))).
    case: loop => [[s c0] |] //= H vm1' /H [vm2' [Hvm Hsem]];exists vm2';split=> //.
    by apply : eq_onI Hvm;SvD.fsetdec.
  Qed.

  Let Hwhile : forall e c, Pc c -> Pi (Cwhile e c).
  Proof.
    move=> e c Hc m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /= s2.
    set s2' := (read_e_rec e s2).
    have : Sv.Subset (read_e_rec e s2) s2'.
    + rewrite /s2' read_eE=> //.
    elim: nb_loop s2' => //= n Hrec s2' Hsub.
    case Heq : (dead_code dead_code_i c s2') => [[s1 c']|] //=.
    case : (boolP (Sv.subset s1 s2')) => /=.
    + move=> /Sv.subset_spec Hsub1.
      pose st1 := {| emem := m1; evm := vm1 |}; pose st2:= {| emem := m2; evm := vm2 |}.
      rewrite (_:vm1 = evm st1) // (_:vm2 = evm st2) //.
      rewrite (_:m1 = emem st1) // (_:m2 = emem st2) //.
      have: sem_while st1 e c st2 ->
            dead_code dead_code_i c s2' = Ok unit (s1, c') -> Pc c -> 
            Sv.Subset (read_e_rec e s2) s2' ->
            forall vm1',  evm st1 =[s2']  vm1' ->
             exists vm2' : vmap, 
             evm st2 =[s2']  vm2' /\
             sem_while {| emem := emem st1; evm := vm1' |} e c'
                       {| emem := emem st2; evm := vm2' |}.
      + move: st1 st2 => {H4 Hrec Hc Heq Hsub vm1 vm2 m1 m2} st1 st2.
        elim=> {st1 st2 e c}
          [ st e c He | [m1 vm1] [m2 vm2] [m3 vm3] e c He Hsc Hsf Hrec] /=
            Heq Hc Hsub vm1' Hvm1.  
        + exists vm1';split=> //;constructor.
          have /read_e_eq_on <-: evm st =[read_e_rec e s2]  vm1';last by case: (st) He.
          + by apply: eq_onI Hvm1.
        have := Hc m1 m2 _ vm2 Hsc s2';rewrite Heq => /(_ vm1') /= [].
        + by apply: eq_onI Hvm1.
        move=> /= vm2' [Hvm2 Hsem2].
        elim (Hrec Heq Hc Hsub vm2' Hvm2) => vm3' /= [Hvm3 Hsem3].
        exists vm3';split=> //;apply: EWhileOne Hsem3=> //.
        rewrite -He /=;symmetry.
        have /read_e_eq_on //: vm1 =[read_e_rec e s2]  vm1'.
        by apply: eq_onI Hvm1.
      move=> /(_ H4 Heq Hc Hsub) H vm1' Hvm1;case: (H vm1')=> //.
      move=> vm2' [Hvm2 Hsem];exists vm2';split => //.
      + by apply: eq_onI Hvm2;move: Hsub;rewrite read_eE;SvD.fsetdec.
      by apply sem_seq1;constructor.
    move=> _; have := Hrec (Sv.union s2' s1).
    case: wloop => [[s c0] |] //=  H vm1' /(H _) [];first by SvD.fsetdec.
    move=> vm2' [Hvm Hsem];exists vm2';split=> //.
  Qed.
     
  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hf m1 m2 vm1 vm2 H;sinversion H.
    unfold rarg in * => {rarg}.
    sinversion H6;sinversion H5;sinversion H2;sinversion H0.
    case Heq: sem_pexpr H7 H8 => [va /=|//] _ Hsem s2.
    case Heq' : dead_code_call H9 => [fd'|] //= Hw vm1' Hvm.
    have := Hf m1 m0 va res;rewrite Heq'=> /(_ Hsem) Hsem'.
    have /(_ s2 vm1') [|vm2' [Hvm2 Hw2]]:= write_rval_eq_on Hw.  
    + by apply: eq_onI Hvm;rewrite read_eE;SvD.fsetdec.
    exists vm2';split=>//.
    by apply sem_seq1;econstructor;eauto;rewrite -(read_e_eq_on m1 Hvm) Heq.
  Qed.

  Let Hfunc : forall ta tr (x:rval ta) c (re:pexpr tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x c re Hc m1 m2 va vr /=.
    case Heq : dead_code => [[s1 c'] | ]//= H;inversion H;clear H;subst.
    inversion H0;clear H0;subst=> /=; constructor=> //= vm0 Hvm0.
    case: (H6 vm0 Hvm0)=> -[m vm] [vm2 /= [Hw Hsem Heqr]]. 
    have /(_ s1 vm0) [//|vm' [Hvm' Hw']]:= write_rval_eq_on Hw.
    have := Hc _ _ _ _ Hsem (read_e re);rewrite Heq.
    move=> /(_ _ Hvm') [] // vm2' [Hvm2 Hsem'].
    exists {| emem := m; evm := vm' |}, vm2';split=>//.
    by rewrite -(read_e_eq_on m2 Hvm2).
  Qed.

  Lemma dead_code_callP ta tr (f : fundef ta tr) mem mem' va vr: 
    match dead_code_call f with 
    | Ok fd' => 
      sem_call mem f va mem' vr -> 
      sem_call mem fd' va mem' vr
    | _      => True
    end.
  Proof.
    apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
  Qed.

End PROOF.