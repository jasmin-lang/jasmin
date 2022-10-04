From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem.

Section test.

Context {asm_op syscall_state} {spp : SemPexprParams asm_op syscall_state}.

(* n is non-positive and increasing *)
Definition clear_loop ws p n :=
  let ir1 :=
    Cassgn (Lmem ws p (Pvar (mk_lvar n))) AT_keep (sword ws) (pword_of_int ws 0) in
  let ir2 :=
    Cassgn (Lvar n) AT_keep (sword Uptr) (Papp2 (Oadd (Op_w Uptr)) (Pvar (mk_lvar n)) (pword_of_int Uptr (wsize_size ws))) in
  let body :=
    map (MkI dummy_instr_info) [:: ir1; ir2] in
  let ir := Cwhile NoAlign [::] (Papp2 (Ole (Cmp_w Signed Uptr)) (Pvar (mk_lvar n)) (pword_of_int Uptr 0)) body in
  let i := MkI dummy_instr_info ir in
  i.

(* n is non-negative and decreasing *)
Definition clear_loop_positive ws p n :=
  let ir1 :=
    Cassgn (Lmem ws p (Pvar (mk_lvar n))) AT_keep (sword ws) (pword_of_int ws 0) in
  let ir2 :=
    Cassgn (Lvar n) AT_keep (sword Uptr) (Papp2 (Osub (Op_w Uptr)) (Pvar (mk_lvar n)) (pword_of_int Uptr (wsize_size ws))) in
  let body :=
    map (MkI dummy_instr_info) [:: ir1; ir2] in
  let ir := Cwhile NoAlign [::] (Papp2 (Ole (Cmp_w Signed Uptr)) (pword_of_int Uptr 0) (Pvar (mk_lvar n))) body in
  let i := MkI dummy_instr_info ir in
  i.

Context {T:eqType} {pT:progT T} {sCP: semCallParams}.

Variable P : prog.
Variable ev : extra_val_t.

Lemma clear_loop_positive_spec : forall ws (p n:var_i) s1 s2 (w wp : word Uptr),
  get_var s1.(evm) n = ok (Vword w) ->
  get_var s1.(evm) p = ok (Vword wp) ->
  sem_I P ev s1 (clear_loop_positive ws p n) s2 ->
  s2.(evm) = s1.(evm) [\ sv_of_list v_var [::n;p] ].
Proof.
  move=> ws p n s1 s2 w hget.
  case (Z.le_gt_cases 0 (wsigned w)) => [hle|hlt]; last first.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hget /= /sem_sop2 /= !truncate_word_u /=.
    rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _).
    case: ssrZ.lezP; first by Lia.lia.
    by move=> _ [<-] /= <-.
  move: {-2}(wsigned w) hle (refl_equal (wsigned w)) hget.
  move=> N hle; move: N hle w.
  apply: natlike_ind => [| N hle ih ] w heq hget.
  + admit.
  move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
  rewrite /get_gvar hget /= /sem_sop2 /= !truncate_word_u /=.
  rewrite wrepr0 -/(wsigned 0) wsigned0 -/(wsigned _) heq.
  case: ssrZ.lezP; last by Lia.lia.
  move=> _ [<-].
  move=> [s1' [hbody hwhile]].
  move: hbody => /semE [s1'' []].
  move=> /sem_IE /sem_iE.
  move=> [v [v' []]].
  rewrite /= /sem_sop1 /= => -[<-].
  rewrite /truncate_val /= truncate_word_u /= => -[<-].
  rewrite 
  
    move: H.
    rewrite -!zify.
    Sear 
    
  Search (_ <= _ \/ _ < _)%Z.
  

Lemma clear_loop_correct : forall ws p (n:var_i) s1 s2 (w : word Uptr),
  get_var s1.(evm) n = ok (Vword w) ->
  sem_I P ev s1 (clear_loop ws p n) s2 ->
  s2.(evm) = s1.(evm) [\ Sv.singleton n ].
Proof.
  move=> ws p n s1 s2 w.
  have [hle _] := wunsigned_range w.
  move: {-2}(wunsigned w) hle (refl_equal (wunsigned w)).
  apply: natlike_ind => [| N hle ih ] heq hget.
  + move=> /sem_IE /= /sem_iE [_ [b []]] /semE -> /=.
    rewrite /get_gvar hget /= /sem_sop2 /= !truncate_word_u /=.
    rewrite -/(wunsigned _) heq word.urepr_ge0 => -[<-].
    move=> [s1' [
  rewrite wunsigned_repr. Search (0 mod _)%Z. rewrite Zmod_0_l /=. Search (?A <= ?A)%R. Order.le_refl
  Search word.urepr wunsigned.
  
  move=> /semE.
    re
    case: (clear_loop ws p n) => [ii ir] /sem_iE.
  - 
  elim/natlike_ind. : N. w .