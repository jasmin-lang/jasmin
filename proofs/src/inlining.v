(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import finmap strings  dmasm_utils dmasm_type dmasm_var dmasm_expr dmasm_sem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope fun_scope.
Local Open Scope vmap.
Local Open Scope fset.
Local Open Scope seq_scope.

(* ** inlining
 * -------------------------------------------------------------------- *)

Fixpoint assgn_tuple t (rv:rval t) : pexpr t -> cmd :=
  match rv in rval t0 return pexpr t0 -> cmd with
  | Rvar x              => fun e => [:: assgn (Rvar x) e]
  | Rpair t1 t2 rv1 rv2 => fun e => assgn_tuple rv1 (efst e) ++ assgn_tuple rv2 (esnd e)
  end.

Definition inline_cmd (inline_i: instr -> cmd) (c:cmd) := 
  List.fold_right (fun i c' => inline_i i ++ c') [::] c.

Fixpoint inline_i (i:instr) : cmd := 
  match i with
  | Cbcmd _              => [::i]
  | Cif b c1 c2          => [::Cif b (inline_cmd inline_i c1) (inline_cmd inline_i c2)]
  | Cfor fi i rn c       => [::Cfor fi i rn (inline_cmd inline_i c)]
  | Ccall ta tr x fd arg => 
    match inline_fd fd in fundef sta str return pexpr sta -> rval str -> cmd with
    | FunDef sta str fa fc fr =>
      fun pe_arg rv_res => 
        assgn_tuple fa pe_arg ++ 
        (fc ++ assgn_tuple rv_res (rval2pe fr))
    end arg x
  end

with inline_fd ta tr (fd:fundef ta tr) :=
  match fd with
  | FunDef sta str fa fc fr => FunDef fa (inline_cmd inline_i fc) fr
  end.

Definition used_i i := Sv.union (read_i i) (write_i i).
Definition used c := read_c_rec (write_c c) c.

Fixpoint check_inline_i (s:Sv.t) (i:instr) : bool := 
  match i with
  | Cbcmd _          => true
  | Cif _ c1 c2      => all (check_inline_i s) c1 && all (check_inline_i s) c2
  | Cfor _ _ _ c     => all (check_inline_i s) c
  | Ccall _ _ _ fd _ => check_inline_fd s fd
  end
  
with check_inline_fd (s:Sv.t) ta tr (fd:fundef ta tr) := 
  match fd with
  | FunDef _ _ fa fc fr =>
    let s' := Sv.union (used fc) (Sv.union (vrv fa) (vrv fr)) in
    disjoint s s' && all (check_inline_i (Sv.union s s')) fc
  end.

Lemma used_cons i c: Sv.Equal (used (i::c)) (Sv.union (used_i i) (used c)).
Proof.
  rewrite /used /used_i /= !read_cE !read_iE !write_c_cons;SvD.fsetdec.
Qed.

Section PROOF.

  Let Pi (i:instr) := 
    forall m1 m2 vm1 vm2, sem_i (Estate m1 vm1) i (Estate m2 vm2) ->
    forall s, check_inline_i s i -> Sv.Subset (used_i i) s ->
    forall vm1', vm1 =[s] vm1' -> 
    exists vm2', vm2 =[s] vm2' /\ sem (Estate m1 vm1') (inline_i i) (Estate m2 vm2').

  Let Pc (c:cmd) := 
    forall m1 m2 vm1 vm2, sem (Estate m1 vm1) c (Estate m2 vm2) ->
    forall s, all (check_inline_i s) c -> Sv.Subset (used c) s ->
    forall vm1', vm1 =[s] vm1' -> 
    exists vm2', vm2 =[s] vm2' /\ sem (Estate m1 vm1') (inline_cmd inline_i c) (Estate m2 vm2').

(*  Let Pf ta tr (fd:fundef ta tr) := 
    forall s, check_inline_fd s fd ->
      let fa := fd_arg fd in
      let fc := fd_body fd in 
      let fr := fd_res fd in
      forall m1 m2 vm1 vm2, sem (Estate m1 vm1) fc (Estate m2 vm2) ->
      let s' := Sv.union (used fc) (Sv.union (vrv fa) (vrv fr)) in
      forall vm1', vm1 =[s] vm1' -> 
      exists vm2', vm2 =[s] vm2' /\ 
      sem (Estate m1 vm1') (inline_cmd inline_i fc) (Estate m2 vm2'). *)

  Let Hskip : Pc [::].
  Proof. 
    move=> m1 m2 vm1 vm2 /= H;inversion H;subst=> s _ _ vm1'; exists vm1';split=>//.
    constructor.
  Qed.

  Let Hseq  : forall i c,  Pi i -> Pc c -> Pc (i::c).
  Proof.
    move=> i c Hi Hc m1 m3 vm1 vm3 H;inversion H;clear H;subst=> /= s /andP[Hci Hcc].
    rewrite used_cons=> Hsub vm1' Hvm1.
    case: s2 H3 H5  => m2 vm2 H3 H5.
    case : (Hi _ _ _ _ H3 _ Hci _ _ Hvm1)=> [|vm2' [Hvm2 Hsi]];first by SvD.fsetdec.
    case: (Hc _ _ _ _ H5 _ Hcc _ _ Hvm2)=> [|vm3' [Hvm3 Hsc]];first by SvD.fsetdec.
    exists vm3';split=> //.
    by apply: sem_app Hsi Hsc.
  Qed.

  Let Hbcmd : forall bc,  Pi (Cbcmd bc).
  Proof. 
    move=> i m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /= s _.
    rewrite /used_i read_i_bcmd write_i_bcmd.
    case: i H2=> /=.
    + move=> t r e;case He: (sem_pexpr _ e) => [v|]//= [] <- /=.
      rewrite -/(vrv r) -/(read_e e)=> <- Hsub vm1' Hvm1.
      exists (write_rval vm1' r v);split.
      + by apply write_rval_eq_on;apply: eq_onI Hvm1;SvD.fsetdec.
      apply sem_seq1;constructor => /=.
      rewrite -(@read_e_eq_on _ e Sv.empty vm1 vm1') ?He //.
      by rewrite -/(read_e e);apply: eq_onI Hvm1;SvD.fsetdec.
    + move=> r e;case He: (sem_pexpr _ e) => [v|]//=.
      case Hre : (read_mem m1 v) => [v'|]//= [] <- <- /=.
      rewrite -/(vrv r) -/(read_e e)=> Hsub vm1' Hvm1.
      exists (write_rval vm1' r v');split.
      + by apply write_rval_eq_on;apply: eq_onI Hvm1;SvD.fsetdec.
      apply sem_seq1;constructor=> /=.
      rewrite -(@read_e_eq_on _ e Sv.empty vm1 vm1') ?He /= ?Hre //=.
      by rewrite -/(read_e e);apply: eq_onI Hvm1;SvD.fsetdec.
    move=> e1 e2;case He1: (sem_pexpr _ e1) => [v1|]//=.
    case He2: (sem_pexpr _ e2) => [v2|]//=.
    case Hw: (write_mem m1 v1 v2) => [m|]//= [] <- <-.
    rewrite !read_eE=> Hsub vm1' Hvm1.
    exists vm1';split=> //.
    apply sem_seq1;constructor => /=.
    rewrite -(@read_e_eq_on _ e1 Sv.empty vm1 vm1') ?He1 /=;last first.
    + by rewrite -/(read_e e1);apply: eq_onI Hvm1;SvD.fsetdec.
    rewrite -(@read_e_eq_on _ e2 Sv.empty vm1 vm1') ?He2 /= ?Hw //.
    by rewrite -/(read_e e1);apply: eq_onI Hvm1;SvD.fsetdec.
  Qed.

  Let Hfor  : forall fi i rn c, Pc c -> Pi (Cfor fi i rn c).
  Proof.
    move=> fi i [[dir low] hi] c Hc m1 m2 vm1 vm2 H;inversion H;clear H;subst=> /=.
    move=> s;rewrite /used_i write_i_for read_i_for => Hcc Hsub.
    move:H10;set st1:={|emem:=m1;evm:=vm1|};set st2:= {|emem:=m2;evm:=vm2|}.
    rewrite (_:vm1 = evm st1) // (_:vm2 = evm st2) //.
    rewrite (_:m1 = emem st1) // (_:m2 = emem st2) // => H10.
    have: forall vm1' : vmap,
      evm st1 =[s]  vm1' ->
      exists vm2' : vmap,
      evm st2 =[s]  vm2' /\
       sem_for i [seq word.n2w i | i <- wrange dir vlow vhi]
           {| emem := emem st1; evm := vm1' |}
           (inline_cmd inline_i c)
           {| emem := emem st2; evm := vm2' |}.
    + elim: H10 Hcc Hsub Hc=> {c H8 H9 st1 st2 m1 m2 vm1 vm2} 
        [ s0 iv c |s1 [m2 vm2] s3 iv w ws c Hsc Hsf Hrec] Hall Hsub Hc vm1' Hvm1.
      + by exists vm1';split=>//;constructor.
      case: (Hc _ _ _ _ Hsc _ Hall _ (write_rval vm1' iv w)).
      + by rewrite /used read_cE;SvD.fsetdec.
      + by apply write_rval_eq_on;apply: eq_onI Hvm1;SvD.fsetdec.
      move=> vm2' [Hvm2 Hsc'].
      case: (Hrec Hall Hsub Hc vm2')=> // vm3' [Hvm3 Hsf'].
      by exists vm3';split=>//;apply: EForOne Hsf'.
    rewrite /st1 /st2 /= => {H10 st1 st2} Hf.
    move=> vm1' Hvm1;case: (Hf _ Hvm1) => [vm2' [Hvm2 Hsf]];exists vm2';split=>//.
    apply sem_seq1;apply EFor with vlow vhi => //=.
    + rewrite -(@read_e_eq_on _ low Sv.empty vm1) //.
      by apply: eq_onI Hvm1;rewrite read_eE;SvD.fsetdec.
    rewrite -(@read_e_eq_on _ hi Sv.empty vm1) //.
    by apply: eq_onI Hvm1;rewrite read_eE;SvD.fsetdec.
  Qed.

  Let Hcall1 : forall ta tr x (f:fundef ta tr) a, Pc (fd_body f) -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hfc m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    unfold rarg in * => {rarg}.
    inversion H5;clear H5;subst;inversion H7;clear H7.
    inversion H6;clear H6;subst;inversion H1;clear H1;subst.
    case Heq: sem_pexpr H3 H10 => [va /=|//] _ Hsem s Hcf {fd2}.
    case:Hsem a x Hfc Hcf Heq=> {m1 m2 res va fd ta tr}.
    move=> ta tr m1 m2 vr fd;case:fd vr => {ta tr} ta tr fa fc fr vr va Hfc.
    move=> a x Hcf Hcc Ha /=. 
    rewrite /used_i read_i_call write_i_call => Hsub vm1' Hvm1.
    case: (Hfc vm1) => {Hfc} vm2 /= [Hsem Hvr].
    have := (Hcf _ _ _ _ Hsem).

 (write_rval vm1' fa va)).
    + apply write_rval_eq_on;apply: eq_onI Hvm1;SvD.fsetdec.
    move=> vm2' [Hvm2 Hsem'].
    exists (write_rval vm2' x vr);split.
    + admit.
    apply sem_app with {| emem := m1; evm := write_rval vm1' fa va |}.
    + admit.    
    apply (sem_app Hsem').
    admit.
  Admitted.

   
  Let Hcall : forall ta tr x (f:fundef ta tr) a, Pf f -> Pi (Ccall x f a).
  Proof.
    move=> ta tr x fd a Hf m1 m2 vm1 vm2 H;inversion H;clear H;subst.
    unfold rarg in * => {rarg}.
    inversion H5;clear H5;subst;inversion H7;clear H7.
    inversion H6;clear H6;subst;inversion H1;clear H1;subst.
    case Heq: sem_pexpr H3 H10 => [va /=|//] _ Hsem s Hcf.
    have {Hf fd2}:= Hf s Hcf.
    case:Hsem a x Hcf Heq=> {m1 m2 res va fd ta tr}.
    move=> ta tr m1 m2 vr fd;case:fd vr => {ta tr} ta tr fa fc fr vr va Hfc.
    move=> a x Hcc Ha /= Hrec.
    rewrite /used_i read_i_call write_i_call => Hsub vm1' Hvm1.
    case: (Hfc vm1) => {Hfc} vm2 /= [Hsem Hvr].
    case: (Hrec _ _ _ _ Hsem (write_rval vm1' fa va)).
    + apply write_rval_eq_on;apply: eq_onI Hvm1;SvD.fsetdec.
    move=> vm2' [Hvm2 Hsem'].
    exists (write_rval vm2' x vr);split.
    + admit.
    apply sem_app with {| emem := m1; evm := write_rval vm1' fa va |}.
    + admit.    
    apply (sem_app Hsem').
    admit.
  Admitted.

  Let Hfunc : forall ta tr (x:rval ta) c (re:rval tr), Pc c -> Pf (FunDef x c re).
  Proof.
    move=> ta tr x c re Hc s /= /andP[Hdis Hcc] m1 m2 vm1 vm2 Hsc vm1' Hvm1.
    have := (Hc _ _ _ _ Hsc _ Hcc _ vm1').


 m1 m2 va vr /=.
    case Heq : dead_code => [[s1 c'] | ]//= H;inversion H;clear H;subst.
    inversion H0;clear H0;subst=> /=; constructor=> vm0.
    case: (H7 vm0)=> vm2 /= [Hsem Heqr]. 
    have := Hc m1 m2 (write_rval vm0 x va) vm2 Hsem (vrv re);rewrite Heq.
    move=> /(_ (write_rval vm0 x va)) [] // vm2' [Hvm2 Hsem'].
    exists vm2';split=> // {H7 Heq}.
    elim: re vr Hvm2 Heqr => [z | ?? vr1 Hrec1 vr2 Hrec2] vr Hvm /= ->.
    + by rewrite Hvm // vrv_var;SvD.fsetdec.
    by f_equal;[apply Hrec1 | apply Hrec2]=> //;apply: eq_onI Hvm;
      rewrite vrv_pair;SvD.fsetdec.
  Qed.

  Lemma dead_code_callP ta tr (f : fundef ta tr) mem mem' va vr: 
    match dead_code_call f with 
    | Ok fd' => sem_call mem f va mem' vr -> sem_call mem fd' va mem' vr
    | _      => True
    end.
  Proof.
    apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hcall Hfunc).
  Qed.

End PROOF.
