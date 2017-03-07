(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* * Prove properties about semantics of dmasm input language *)

(* ** Imports and settings *)
Require Import JMeq ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word dmasm_utils dmasm_type dmasm_var dmasm_expr memory dmasm_sem
               compiler_util.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
  

Definition dead_code_c (dead_code_i: instr -> Sv.t -> ciexec (Sv.t * cmd)) 
                       c s :  ciexec (Sv.t * cmd):= 
  foldr (fun i r =>
    Let r := r in
    Let ri := dead_code_i i r.1 in
    ciok (ri.1, ri.2 ++ r.2)) (ciok (s,[::])) c.

Section LOOP.

  Variable dead_code_c : Sv.t -> ciexec (Sv.t * cmd).
  Variable ii : instr_info.

  Fixpoint loop (n:nat) (rx:Sv.t) (wx:Sv.t) (s:Sv.t) : ciexec (Sv.t * cmd) :=
    match n with
    | O => cierror ii (Cerr_Loop "dead_code")
    | S n =>
      Let sc := dead_code_c s in
      let: (s',c') := sc in
      let s' := Sv.union rx (Sv.diff s' wx) in
      if Sv.subset s' s then ciok (s,c') 
      else loop n rx wx (Sv.union s s')
    end.

  Fixpoint wloop (n:nat) (s:Sv.t) : ciexec (Sv.t * cmd) :=
    match n with
    | O =>  cierror ii (Cerr_Loop "dead_code")
    | S n =>
      Let sc := dead_code_c s in
      let: (s',c') := sc in
      if Sv.subset s' s then ciok (s,c') 
      else wloop n (Sv.union s s')
    end.

End LOOP.

Definition write_mem (r:rval) : bool := 
  if r is Rmem _ _ then true else false.

Definition check_nop (rv:rval) (e:pexpr) :=
  match rv, e with
  | Rvar x1, Pvar x2 => x1 == x2
  | _, _ => false
  end.
 
Fixpoint dead_code_i (i:instr) (s:Sv.t) {struct i} : ciexec (Sv.t * cmd) := 
  let (ii,ir) := i in
  match ir with
  | Cassgn x tag e =>
    let w := write_i ir in
    if tag == AT_inline then
      if disjoint s w && negb (write_mem x) then ciok (s, [::])
      else if check_nop x e then ciok (s, [::])
      else ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ])
    else   ciok (read_rv_rec (read_e_rec (Sv.diff s w) e) x, [:: i ])
  
  | Copn xs _ es =>
    ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i])

  | Cif b c1 c2 => 
    Let sc1 := dead_code_c dead_code_i c1 s in
    Let sc2 := dead_code_c dead_code_i c2 s in
    let: (s1,c1) := sc1 in
    let: (s2,c2) := sc2 in
    ciok (read_e_rec (Sv.union s1 s2) b, [:: MkI ii (Cif b c1 c2)])

  | Cfor x (dir, e1, e2) c =>
    Let sc := loop (dead_code_c dead_code_i c) ii Loop.nb 
                   (read_rv (Rvar x)) (vrv (Rvar x)) s in
    let: (s, c) := sc in
    ciok (read_e_rec (read_e_rec s e2) e1,[:: MkI ii (Cfor x (dir,e1,e2) c) ])

  | Cwhile e c =>
    Let sc := wloop (dead_code_c dead_code_i c) ii Loop.nb (read_e_rec s e) in
    let: (s, c) := sc in
    ciok (s, [:: MkI ii (Cwhile e c) ])

  | Ccall _ xs _ es =>
    ciok (read_es_rec (read_rvs_rec (Sv.diff s (vrvs xs)) xs) es, [:: i])
  end.

Definition dead_code_fd (fd: fundef) :=
  match fd with
  | MkFun ii params c res =>
    let s := read_es (map Pvar res) in
    Let c := dead_code_c dead_code_i c s in
    ciok (MkFun ii params c.2 res)
  end.

Definition dead_code_ffd (ffd:funname * fundef) (p:cfexec prog) :=
  Let p := p in
  match ffd with
  | (f, fd) =>
    let fd' := dead_code_fd fd in
    Let c := add_finfo f f fd' in
    cfok ((f, c) :: p)
  end.

Definition dead_code_prog (p:prog) := foldr dead_code_ffd (cfok [::]) p.

Lemma write_memP (x:rval) v m1 m2 vm1 vm2:
  ~~ write_mem x -> 
  write_rval x v {| emem := m1; evm := vm1 |} = ok {| emem := m2; evm := vm2 |} ->
  m1 = m2.
Proof.
  elim: x=> //= [v0|v0|v0 p] _.
  + by move=> [] ->.
  + by apply: rbindP=> z Hz [] ->.
  apply: on_arr_varP=> n t Ht Hval.
  apply: rbindP=> i; apply: rbindP=> x Hx Hi.
  apply: rbindP=> v1 Hv; apply: rbindP=> t0 Ht0.
  by apply: rbindP=> vm Hvm /= [] ->.
Qed.

Section PROOF.

  Variable p : prog.

  Variable p' : prog.

  Parameter dead_code_ok : dead_code_prog p = ok p'.

  Let Pi_r (s:estate) (i:instr_r) (s':estate) :=
    forall ii s2,
      match dead_code_i (MkI ii i) s2 with
      | Ok (s1, c') =>
        forall vm1', s.(evm) =[s1] vm1' ->
        exists vm2', s'.(evm) =[s2] vm2' /\ 
          sem p' (Estate s.(emem) vm1') c' (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pi (s:estate) (i:instr) (s':estate) :=
    forall s2,
      match dead_code_i i s2 with
      | Ok (s1, c') =>
        forall vm1', s.(evm) =[s1] vm1' ->
        exists vm2', s'.(evm) =[s2] vm2' /\ 
          sem p' (Estate s.(emem) vm1') c' (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pc (s:estate) (c:cmd) (s':estate) :=
    forall s2, 
      match dead_code_c dead_code_i c s2 with
      | Ok (s1, c') =>
        forall vm1', s.(evm) =[s1] vm1' ->
        exists vm2', s'.(evm) =[s2] vm2' /\ 
          sem p' (Estate s.(emem) vm1') c' (Estate s'.(emem) vm2')
      | _ => True
      end.

  Let Pfun m1 fn vargs m2 vres :=
    forall fd, get_fundef p fn = Some fd ->
    match dead_code_fd fd with
    | Ok fd' => 
      sem_call p m1 fn vargs m2 vres -> 
      sem_call p' m1 fn vargs m2 vres
    | _ => True
    end.

  Local Lemma Hskip s : Pc s [::] s.
  Proof.
    case: s=> mem vm s2 vm' Hvm.
    exists vm'; split=> //.
    constructor.
  Qed.

  Local Lemma Hcons s1 s2 s3 i c :
    sem_I p s1 i s2 ->
    Pi s1 i s2 -> sem p s2 c s3 -> Pc s2 c s3 -> Pc s1 (i :: c) s3.
  Proof.
    move=> H Hi H' Hc sv3 /=.
    have := Hc sv3.
    case: (dead_code_c dead_code_i c sv3)=> [[sv2 c']|//] Hc' /=.
    have := Hi sv2.
    case: (dead_code_i i sv2)=> [[sv1 i']|] //= Hi' vm1' /Hi'.
    move=> [vm2' [Heq2 Hsi']];case: (Hc' _ Heq2) => [vm3' [Heq3 Hsc']].
    exists vm3';split=> //.
    by apply: sem_app Hsi' Hsc'.
  Qed.

  Local Lemma HmkI ii i s1 s2 :
    sem_i p s1 i s2 -> Pi_r s1 i s2 -> Pi s1 (MkI ii i) s2.
  Proof. move=> _ Hi. exact: Hi. Qed.

  Lemma check_nop_spec (r:rval) (e:pexpr): check_nop r e ->
    exists x, r = (Rvar x) /\ e = (Pvar x).
  Proof. by case: r e => //= x1 [] //= x2 /eqP <-;exists x1. Qed.

  (* TODO: move *)
  Lemma of_val_to_val vt (v: sem_t vt): of_val vt (to_val v) = ok v.
  Proof.
    elim: vt v=> // n v /=.
    have ->: CEDecStype.pos_dec n n = left (erefl n).
      by elim: n {v}=> // p0 /= ->.
    by [].
  Qed.

  Local Lemma Hassgn s1 s2 x tag e ii :
    Let v := sem_pexpr s1 e in write_rval x v s1 = Ok error s2 ->
    Pi s1 (MkI ii (Cassgn x tag e)) s2.
  Proof.
    move: s1 s2=> [m1 vm1] [m2 vm2].
    apply: rbindP=> v Hv Hw s2 /=.
    case: ifPn=> _ /=.
    + case: ifPn=> /=.
      + move=> /andP [Hdisj Hwmem] vm1' Hvm.
        rewrite write_i_assgn in Hdisj.
        exists vm1'; split=> //.
        by apply: eq_onT Hvm; apply: eq_onS; apply: disjoint_eq_on Hdisj Hw.
        rewrite (write_memP Hwmem Hw); exact: Eskip.
      + move=> ?.
        case: ifPn=> Hnop /=.
        + move=> vm1' Hvm.
          have Hs: {| emem := m1; evm := vm1 |} = {| emem := m2; evm := vm2 |}.
            move: (check_nop_spec Hnop)=> {Hnop} [x0 [Hx He]].
            rewrite {}He /= in Hv.
            rewrite {}Hx /= in Hw.
            rewrite /write_var /set_var /= in Hw.
            case: (bindW Hv)=> v' Hv' {Hv} []Hv.
            have Hv'2 := (@of_val_to_val (vtype x0) v').
            rewrite -{}Hv /write_var /set_var /= {} Hv'2 /= -{}Hv' /= in Hw.
            move: Hw=> [] -> /= Hw.
            rewrite -Hw.
            have ->: vm1.[x0 <- vm1.[x0]] = vm1.
              apply: Fv.map_ext=> z.
              case Heq: (z == x0).
              move: Heq=> /eqP ->; by rewrite Fv.setP_eq.
              have := negbT Heq => Heq'.
              rewrite Fv.setP_neq=> //.
              by rewrite eq_sym.
            by [].
          exists vm1'; split.
          apply: eq_onT Hvm.
          by case: Hs=> _ ->.
          case: Hs=> -> _.
          exact: Eskip.
        + move=> vm1' Hvm.
          rewrite write_i_assgn in Hvm.
          move: Hvm; rewrite read_rvE read_eE=> Hvm.
          have [|vm2' [Hvm2 Hw2]] := write_rval_eq_on _ Hw Hvm; first by SvD.fsetdec.
          exists vm2'; split.
          + by apply: eq_onI Hvm2; SvD.fsetdec.
          + apply: sem_seq1; constructor; constructor.
            rewrite (@read_e_eq_on Sv.empty vm1 vm1') ?Hv // read_eE.
            by apply: eq_onS; apply: eq_onI Hvm; SvD.fsetdec.
    + move=> vm1' Hvm.
      rewrite write_i_assgn in Hvm.
      move: Hvm; rewrite read_rvE read_eE=> Hvm.
      have [|vm2' [Hvm2 Hw2]] := write_rval_eq_on _ Hw Hvm; first by SvD.fsetdec.
      exists vm2'; split.
      + by apply: eq_onI Hvm2; SvD.fsetdec.
      + apply: sem_seq1; constructor; constructor.
        rewrite (@read_e_eq_on Sv.empty vm1 vm1') ?Hv // read_eE.
        by apply: eq_onS; apply: eq_onI Hvm; SvD.fsetdec.
  Qed.

  Local Lemma Hopn s1 s2 o xs es :
    Let x := Let x := sem_pexprs s1 es in sem_sopn o x
    in write_rvals s1 xs x = Ok error s2 -> Pi_r s1 (Copn xs o es) s2.
  Proof.
    apply: rbindP=> x; apply: rbindP=> x0 Hexpr Hopn Hw.
    rewrite /Pi_r /==> ii s0 vm1' Hvm.
    move: Hvm; rewrite read_esE read_rvsE=> Hvm.
    have [|vm2 [Hvm2 Hvm2']] := write_rvals_eq_on _ Hw Hvm; first by SvD.fsetdec.
    exists vm2; split.
    by apply: eq_onI Hvm2; SvD.fsetdec.
    econstructor.
    constructor; constructor.
    rewrite (@read_es_eq_on es Sv.empty (emem s1) vm1' (evm s1)).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: s1 Hexpr Hw Hvm Hvm2'.
    rewrite Hexpr /= Hopn /=.
    exact: Hvm2'.
    rewrite read_esE.
    symmetry.
    apply: eq_onI Hvm.
    SvD.fsetdec.
    constructor.
  Qed.

  Local Lemma Hif_true s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error true ->
    sem p s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hval Hp Hc ii sv0 /=.
    case Heq: (dead_code_c dead_code_i c1 sv0)=> [[sv1 sc1] /=|//].
    case: (dead_code_c dead_code_i c2 sv0)=> [[sv2 sc2] /=|//] vm1' Hvm.
    move: (Hc sv0).
    rewrite Heq.
    move=> /(_ vm1') [|vm2' [Hvm2' Hvm2'1]].
    move: Hvm; rewrite read_eE=> Hvm.
    apply: eq_onI Hvm; SvD.fsetdec.
    exists vm2'; split=> //.
    econstructor; constructor.
    constructor=> //.
    symmetry in Hvm.
    rewrite (read_e_eq_on _ Hvm).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: s1 Hval Hp Hc Hvm Hvm2'1.
    by rewrite Hval.
  Qed.    

  Local Lemma Hif_false s1 s2 e c1 c2 :
    Let x := sem_pexpr s1 e in to_bool x = Ok error false ->
    sem p s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof.
    move=> Hval Hp Hc ii sv0 /=.
    case: (dead_code_c dead_code_i c1 sv0)=> [[sv1 sc1] /=|//].
    case Heq: (dead_code_c dead_code_i c2 sv0)=> [[sv2 sc2] /=|//] vm1' Hvm.
    move: (Hc sv0).
    rewrite Heq.
    move=> /(_ vm1') [|vm2' [Hvm2' Hvm2'1]].
    move: Hvm; rewrite read_eE=> Hvm.
    apply: eq_onI Hvm; SvD.fsetdec.
    exists vm2'; split=> //.
    econstructor; constructor.
    apply: Eif_false=> //.
    symmetry in Hvm.
    rewrite (read_e_eq_on _ Hvm).
    have ->: {| emem := emem s1; evm := evm s1 |} = s1 by case: s1 Hval Hp Hc Hvm Hvm2'1.
    by rewrite Hval.
  Qed.

  (*
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
  *)

  Lemma dead_code_callP fn mem mem' va vr:
    sem_call p mem fn va mem' vr ->
    sem_call p' mem fn va mem' vr.
  Proof.
    (*
    apply (@func_rect Pi Pc Pf Hskip Hseq Hbcmd Hif Hfor Hwhile Hcall Hfunc).
    *)
  Admitted.

End PROOF.
