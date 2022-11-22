(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat ssrint ssralg.
From mathcomp Require Import choice fintype eqtype div seq zmodp finset.
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils type var expr low_memory psem stack_alloc.

Import compiler_util.
Import ZArith.
Import Psatz.
Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Module S.
  Notation vstk nstk := {|v_var := {|vtype := sword U64; vname := nstk|}; v_info := xH|}.

  Section Section.
  Context {LO:LeakOp}.
  Section SEM.
  Variable P:sprog.
  Context (gd: glob_decls).

  Inductive sem : estate -> cmd -> leak_c -> estate -> Prop :=
  | Eskip s : sem s [::] [::] s

  | Eseq s1 s2 s3 i c li lc :
    sem_I s1 i li s2 -> sem s2 c lc s3 -> sem s1 (i::c) (li :: lc) s3

  with sem_I : estate -> instr -> leak_i -> estate -> Prop :=
  | EmkI ii i s1 s2 li:
    sem_i s1 i li s2 ->
    sem_I s1 (MkI ii i) li s2

  with sem_i : estate -> instr_r -> leak_i -> estate -> Prop :=
  | Eassgn s1 s2 (x:lval) tag ty e v v' l1 l2:
    sem_pexpr gd s1 e = ok (v, l1) ->
    truncate_val ty v = ok v' ->
    write_lval gd x v' s1 = ok (s2, l2) ->
    sem_i s1 (Cassgn x tag ty e) (Lopn (LSub [:: l1 ; l2])) s2

  | Eopn s1 s2 t o xs es lo:
    sem_sopn gd o s1 xs es = ok (s2, lo) ->
    sem_i s1 (Copn xs t o es) (Lopn lo) s2

  | Eif_true s1 s2 e c1 c2 le lc:
    sem_pexpr gd s1 e = ok (Vbool true, le) ->
    sem s1 c1 lc s2 ->
    sem_i s1 (Cif e c1 c2) (Lcond le true lc) s2

  | Eif_false s1 s2 e c1 c2 le lc:
    sem_pexpr gd s1 e = ok ((Vbool false), le) ->
    sem s1 c2 lc s2 ->
    sem_i s1 (Cif e c1 c2) (Lcond le false lc) s2

  | Ewhile_true s1 s2 s3 s4 a c e c' lc le lc' lw:
    sem s1 c lc s2 ->
    sem_pexpr gd s2 e = ok (Vbool true, le) ->
    sem s2 c' lc' s3 ->
    sem_i s3 (Cwhile a c e c') lw s4 ->
    sem_i s1 (Cwhile a c e c') (Lwhile_true lc le lc' lw) s4

  | Ewhile_false s1 s2 a c e c' le lc:
    sem s1 c lc s2 ->
    sem_pexpr gd s2 e = ok ((Vbool false), le) ->
    sem_i s1 (Cwhile a c e c') (Lwhile_false lc le) s2

  | Ecall s1 m2 s2 ii xs f args vargs vs lf l2:
    sem_pexprs gd s1 args = ok vargs ->
    sem_call s1.(emem) f (unzip1 vargs) lf m2 vs ->
    write_lvals gd {|emem:= m2; evm := s1.(evm) |} xs vs = ok (s2, l2) ->
    sem_i s1 (Ccall ii xs f args) (Lcall (unzip2 vargs) lf l2) s2

  with sem_call : mem -> funname -> seq value -> leak_fun -> mem -> seq value -> Prop :=
  | EcallRun m1 m2 fn sf vargs vargs' s1 s2 m2' vm2 vres vres' m1' lc:
    get_fundef P fn = Some sf ->
    alloc_stack m1 (sf_stk_sz sf) = ok m1' ->
    write_var  (vstk (sf_stk_id sf)) (Vword (top_stack m1')) (Estate m1' vmap0) = ok s1 ->
    mapM2 ErrType truncate_val sf.(sf_tyin) vargs' = ok vargs ->
    write_vars (sf_params sf) vargs s1 = ok s2 ->
    sem s2 (sf_body sf) lc {| emem := m2'; evm := vm2 |} ->
    mapM (fun (x:var_i) => get_var vm2 x) sf.(sf_res) = ok vres ->
    mapM2 ErrType truncate_val sf.(sf_tyout) vres = ok vres' ->
    m2 = free_stack m2' (sf_stk_sz sf) ->
    sem_call m1 fn vargs' (fn, lc) m2 vres'.

  End SEM.

  Lemma semE p gd s c s' lc:
  sem p gd s c lc s' ->
  match c with
  | [::] => s' = s /\ lc = [::]
  | i :: c' => exists si li lc', 
    [/\ sem_I p gd s i li si, sem p gd si c' lc' s' & lc = li :: lc']
  end.
  Proof.
    case. move=> H1; split; auto.
    move=> s1 s2 s3 i li lc0 lc' H1 H2.
    exists s2. exists lc0. exists lc'. split; auto. 
  Qed.


  Lemma sem_app p gd l1 l2 s1 s2 s3 ls1 ls2:
    sem p gd s1 l1 ls1 s2 -> 
    sem p gd s2 l2 ls2 s3 ->
    sem p gd s1 (l1 ++ l2) (ls1 ++ ls2) s3.
  Proof.
    elim: l1 s1 ls1; first by move => s1 ls1 /semE H H1;
    case H => <- ->; auto.
    move=> a l Hrec s1 ls1 /semE [si] [li] [lc'] [h1 hi ->] h /=.
    move: (Hrec si lc' hi h) => H /=.
    apply Eseq with si; auto.
  Qed.

  Lemma sem_seq1 p gd i s1 s2 li:
  sem_I p gd s1 i li s2 -> sem p gd s1 [::i] [::li] s2.
  Proof.
    move=> Hi. apply Eseq with s2. auto.
    constructor.
  Qed.

  Lemma sem_IE p gd s1 i s2 li:
    sem_I p gd s1 i li s2 ->
    let 'MkI _ r := i in
    sem_i p gd s1 r li s2.
  Proof. by case. Qed.

  Lemma sem_iE p gd s1 i s2 li:
    sem_i p gd s1 i li s2 ->
    match i with
    | Cassgn x _ ty e =>
      exists v v' le lw,
      [/\ sem_pexpr gd s1 e = ok (v, le),
       truncate_val ty v = ok v' &
       write_lval gd x v' s1 = ok (s2, lw)]
    | Copn xs _ op es => exists lo, sem_sopn gd op s1 xs es = ok (s2, lo)
    | Cif e c1 c2 =>
      exists b le lc,
      sem_pexpr gd s1 e = ok (Vbool b, le) /\
      sem p gd s1 (if b then c1 else c2) lc s2
    | Cfor _ _ _ => False
    | Cwhile a c1 e c2 =>
      exists si b lc le,
      sem p gd s1 c1 lc si /\
      sem_pexpr gd si e = ok (Vbool b, le) /\
      if b then (exists sj lc' lw, sem p gd si c2 lc' sj /\ sem_i p gd sj (Cwhile a c1 e c2) lw s2) else si = s2
    | Ccall _ xs fn es =>
      exists vs m2 rs lf l2,
      [/\ sem_pexprs gd s1 es = ok vs,
          sem_call p gd (emem s1) fn (unzip1 vs) lf m2 rs &
          write_lvals gd {| emem := m2 ; evm := evm s1 |} xs rs = ok (s2, l2) ]
    end.
  Proof.
  case => {s1 i li s2} //.
  - by move => s s' x _ ty e v v' le lw hv hv' hw; exists v, v', le, lw.
  - by move => s s' e th el le lc he; exists lc; auto.
  - by move => s s' e th el le lc he hel; exists true, le, lc; split; auto.
  - by move => s s' e th el le lc he hel; exists false, le, lc; split; auto.
  - by move =>  s si sj s' a c e c' lc le lc' lw hc he hc' hrec; exists si, true, lc, le; constructor => //;
    split=> //; exists sj, lc', lw; constructor => //.
  - by move => s s' a c e c' lc le hc he; exists s', false, le, lc.
  by move => s m s' _ xs f es vs rs lf l2 hvs h hrs; exists vs, m, rs, lf, l2.
Qed.

Lemma sem_iE' p gd s1 i s2 li:
  sem_i p gd s1 i li s2 ->
  match i with
  | Cassgn lv _ ty e =>
    exists v v' le lw,
    [ /\ sem_pexpr gd s1 e = ok (v, le), truncate_val ty v = ok v', write_lval gd lv v' s1 = ok (s2, lw) 
      & li = Lopn (LSub [:: le ; lw])]
  | Copn lvs _ op es => exists lo, sem_sopn gd op s1 lvs es = ok (s2, lo) /\ li = Lopn lo
  | Cif e th el =>
    exists b le lc, [ /\ sem_pexpr gd s1 e = ok (Vbool b, le), sem p gd s1 (if b then th else el) lc s2
                 & li = Lcond le b lc]
  | Cfor i r c => False
  | Cwhile a c e c' =>
    exists si b lc le,
       sem p gd s1 c lc si /\ sem_pexpr gd si e = ok (Vbool b, le) /\
       if b then exists sj lc' lw, sem p gd si c' lc' sj /\ sem_i p gd sj (Cwhile a c e c') lw s2 
                 /\ li = (Lwhile_true lc le lc' lw)
        else si = s2 /\ li = Lwhile_false lc le
  | Ccall _ xs f es =>
    exists vs m2 rs lf l2,
    [/\ sem_pexprs gd s1 es = ok vs, sem_call p gd s1.(emem) f (unzip1 vs) lf m2 rs, 
       write_lvals gd {|emem:= m2; evm := s1.(evm) |} xs rs = ok (s2, l2) 
     & li = (Lcall (unzip2 vs) lf l2)]
  end.
Proof.
  case => {s1 i li s2} //.
  - by move => s s' x _ ty e v v' le lw hv hv' hw; exists v, v', le, lw.
  - by move => s s' e th el le lc he; exists lc; auto.
  - by move => s s' e th el le lc he hel; exists true, le, lc; split; auto.
  - by move => s s' e th el le lc he hel; exists false, le, lc; split; auto.
  - by move =>  s si sj s' a c e c' lc le lc' lw hc he hc' hrec; exists si, true, lc, le; 
    constructor => //; split=> //; exists sj, lc', lw; constructor => //.
  - by move => s s' a c e c' lc le hc he; exists s', false, le, lc.
  by move => s m s' _ xs f es vs rs lf l2 hvs h hrs; exists vs, m, rs, lf, l2.
Qed.

Lemma sem_callE' fn vargs' m1 m2 lf vres' p gd:
  sem_call p gd m1 fn vargs' lf m2 vres' ->
  exists sf,
    get_fundef p fn = Some sf /\
  exists m1' s1 vargs s2 m2' vm2 vres,
    alloc_stack m1 (sf_stk_sz sf) = ok m1' /\
    write_var  (vstk (sf_stk_id sf)) (Vword (top_stack m1')) (Estate m1' vmap0) = 
    ok s1 /\
    mapM2 ErrType truncate_val sf.(sf_tyin) vargs' = ok vargs /\
    write_vars (sf_params sf) vargs s1 = ok s2 /\
    sem p gd s2 (sf_body sf) lf.2 {| emem := m2'; evm := vm2 |} /\
    mapM (fun (x:var_i) => get_var vm2 x) sf.(sf_res) = ok vres /\
    mapM2 ErrType truncate_val sf.(sf_tyout) vres = ok vres' /\
    m2 = free_stack m2' (sf_stk_sz sf).
Proof.
  case => { m1 fn vargs' lf m2 vres' }.
  move=> m1 m2 fn sf vargs vargs' s1 s2 m2' vm2 vres vres' m1' lc.
  move=> hf hs hw hc hr ht ht' hm2 hm2'.
  exists sf; split=> //.
  by exists m1'; exists s1; exists vargs; exists s2; exists m2'; exists vm2;
  exists vres.
Qed.

End Section.
End S.
