From mathcomp Require Import all_ssreflect all_algebra.
From CoqWord Require Import ssrZ.
Require Import ZArith
utils
strings wsize
memory_model
gen_map
(* word *)
global
oseq
Utf8
Relation_Operators
sem_type
syscall
arch_decl
label
values
word
arch_sem_no_spec
arch_sct.

Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma Public_only_less_than_Public : forall t, (t <= Public)%CMP -> t = Public.
Proof.
move=> t ht. by case: t ht=> //=.
Qed.

Lemma zero_extend_small_size : forall s sz sz' (w1: word s) (w2: word s),
(sz <= sz')%CMP -> 
zero_extend sz' w1 = zero_extend sz' w2 ->
zero_extend sz  w1 = zero_extend sz  w2.
Proof.
move=> s sz sz' w1 w2 hsz ht.
have hz := zero_extend_idem. move: (hz s sz sz' w1 hsz)=> <-.
move: (hz s sz sz' w2 hsz)=> <-. by rewrite ht /=.
Qed.


Lemma zero_extend_word : forall sz sz' (w1: word sz),
(sz <= sz')%CMP -> 
zero_extend sz w1 = w1.
Proof.
move=> sz sz' w1 hsz.
have hw := word_uincl_zero_extR. move: (hw sz sz' w1 hsz).
rewrite /word_uincl. move=> /andP [] hsz' /eqP hz. 
have hz' := zero_extend_idem. by move: (hz' sz sz sz' w1 hsz')=> <-.
Qed.

Section PROOFS.

Context {reg regx xreg rflag cond asm_op} {asm_d : asm reg regx xreg rflag cond asm_op}. 

Context (wt_cond : constraints -> env_t -> cond_t -> Sl.t -> bool).

Context (fn: funname).

Lemma state_equiv_env_env' : forall c rho s1 s2 env env',
state_equiv rho s1 s2 env ->
valid_valuation c rho ->
le_env c env env' ->
state_equiv rho s1 s2 env'. 
Proof.
move=> c rho [] m1 fn1 code1 ip1 [] m2 fn2 code2 ip2 env env' hequiv hvalid hle.
case: hequiv=> /= hcode hpc hreg hregx hxreg hflag hmem; subst.
constructor; auto; rewrite /=; subst.
+ move=> r l ws hregty hrho.
  rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hr r)=> /= hle. rewrite hregty /= in hle. rewrite /le_ws /= in hle.
  case: hle=> /andP [/= hle hsz]. 
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_reg env r).1 l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_reg env r = ((e_reg env r).1, (e_reg env r).2). + by case: (e_reg env r)=> //=.
  move: (hreg r (e_reg env r).1 (e_reg env r).2 henv hpub)=> htenv. 
  by have := zero_extend_small_size hsz htenv.
+ move=> r l ws hregxty hrho.
  rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hrx r)=> /= hle. rewrite hregxty /= in hle. rewrite /le_ws /= in hle.
  case: hle=> /andP [/= hle hsz]. 
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_regx env r).1 l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_regx env r = ((e_regx env r).1, (e_regx env r).2). + by case: (e_regx env r)=> //=.
  move: (hregx r (e_regx env r).1 (e_regx env r).2 henv hpub)=> htenv. 
  by have := zero_extend_small_size hsz htenv.
+ move=> r l ws hxregty hrho.
  rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hxr r)=> /= hle. rewrite hxregty /= in hle. rewrite /le_ws /= in hle.
  case: hle=> /andP [/= hle hsz]. 
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_xreg env r).1 l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_xreg env r = ((e_xreg env r).1, (e_xreg env r).2). + by case: (e_xreg env r)=> //=.
  move: (hxreg r (e_xreg env r).1 (e_xreg env r).2 henv hpub)=> htenv. 
  by have := zero_extend_small_size hsz htenv.
+ move=> f l hfty hrho. rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
  move: (hf f)=> /= hle. rewrite hfty /= in hle. rewrite /le_ws /= in hle.
  inversion hvalid. case: H0=> hsecret hl. move: (hl (e_flag env f) l hle)=> /= hl'.
  rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
  have henv : e_flag env f = e_flag env f. + by auto. 
  by move: (hflag f (e_flag env f) henv hpub).
move=> pt l adr vp pts hwvp hvp hpty hrho i hi.
rewrite /le_env /= in hle. case: hle=> [] hr hrx hxr hf hm.
move: (hm pt)=> /= hle. rewrite hpty /= in hle. rewrite /le_ws /= in hle.
inversion hvalid. case: H0=> hsecret hl. move: (hl (get_pt env pt) l hle)=> /= hl'.
rewrite hrho /= in hl'. have hpub := Public_only_less_than_Public hl'. 
have henv : get_pt env pt = get_pt env pt. + by auto.
by move: (hmem pt (get_pt env pt) adr vp pts hwvp hvp henv hpub i hi).
Qed.

Lemma foo: forall l S S',
Sl.mem l S ->
Sl.subset S S' ->
Sl.mem l S'.
Proof.
Admitted.

Lemma type_prev_implicit_args : forall c env a S ad pt ty s1 s2 rho v1 leak1 v2 leak2,
wt_arg_in wt_cond c env a S ad pt ty ->
state_equiv rho s1 s2 env ->
valid_valuation c rho ->
eval_arg_in_v s1.(asm_m) a ad ty = ok (v1, leak1) ->
eval_arg_in_v s2.(asm_m) a ad ty = ok (v2, leak2) ->
(forall l, Sl.mem l S -> value_equiv v1 v2 (rho l)) /\ leak1 = leak2.
Proof.
move=> c env a S ad pt ty [] m1 fn' code1 ip1 [] m2 fn'' code2 ip2 rho 
v1 leak1 v2 leak2 hwt hequiv hvalid hstep hstep'.
case: hequiv=> /= hcode hip hreg hregx hxreg hflag hmem; subst.
case: hvalid=> hpub [hsec hle'].
inversion hstep; inversion hstep'; subst; move=> {hstep} {hstep'}.
rewrite /eval_arg_in_v /= in H0 H1. 
case: ad H0 H1 hwt=> //=.
(* implicit *)
+ move=> i H0 H1 hwt. case: i H0 H1 hwt=> //=.
  (* implicit flag *)
  + move=> f. t_xrbindP=> b hset hb hleak b' hset' hb' hleak' hle; subst.
    rewrite /st_get_rflag in hset hset'. split=> //=.
    rewrite /value_equiv. move=> l hl hrho.
    have henv : e_flag env f = e_flag env f. + by case: (e_flag env f)=> //=.
    move: (hflag f (e_flag env f) henv)=> hflag'.
    rewrite /le_all in hle. rewrite /is_le in hle'. have foo' := foo hl hle.
    move: (hle' (e_flag env f) l foo')=> hle1. rewrite hrho /= in hle1. 
    apply Public_only_less_than_Public in hle1.
    move: (hflag f (e_flag env f) henv hle1)=> {hreg} hreg. rewrite hreg in hset hset'.
    case: (asm_flag m2 f) hset hset'=> //=.
    by move=> b'' [] hb'' [] hb'''; subst.
  (* implicit reg *)
  move=> r [] hr hl [] hr' hl'; subst. case: ty=> //=.
  move=> ws hregty. split=> //=. rewrite /value_equiv. move=> l hl hrho. 
  have henv : e_reg env r = ((e_reg env r).1, (e_reg env r).2). + by case: (e_reg env r)=> //=.
  rewrite henv /= in hregty. move: hregty. move=> /andP [] hle hws.
  rewrite /le_all in hle. rewrite /is_le in hle'. have foo' := foo hl hle.
  move: (hle' (e_reg env r).1 l foo')=> hle1. rewrite hrho /= in hle1. 
  apply Public_only_less_than_Public in hle1.
  move: (hreg r (e_reg env r).1 (e_reg env r).2 henv hle1)=> {hreg} hreg. 
  have hz :=  zero_extend_word. (*move: (hz (e_reg env r).2 ws (asm_reg m1 r)).*)
  admit. 
(* explicit *)
move=> ak n o /=. case: (onth a n)=> //=.
move=> asm_arg /=. t_xrbindP=> ut hassert heval ut' hassert' heval' hwt.
rewrite /eval_asm_arg /= in heval heval'. rewrite /wt_asm_arg in hwt.
case: asm_arg hassert heval hassert' heval' hwt=> //=.
(* condt *)
+ move=> condt /= hassert. t_xrbindP=> b heval hb hleak hassert' b' heval' hb' hleak'; subst.
  case: ty=> //=. move=> hwt. rewrite /eval_cond_mem /st_get_rflag in heval heval'. 
  rewrite /value_equiv. split=> //=. move=> l hl hrho.
  admit.
(* Imm *)
+ move=> ws s hassert. case: ty=> //=.
  by move=> w [] hv1 hleak1 hassert' [] hv2 hleak2 hle''; subst.
(* Reg *)
+ move=> r hassert [] hv1 hleak1 hassert' [] hv2 hleak2; subst. case: ty=> //=.
  move=> ws hregty. rewrite /value_equiv. split=> //=.
  move=> l hl hrho. 
  have henv : e_reg env r = ((e_reg env r).1, (e_reg env r).2). + by case: (e_reg env r)=> //=.
  rewrite henv /= in hregty. move: hregty. move=> /andP [] hle hws.
  rewrite /le_all in hle. rewrite /is_le in hle'. have foo' := foo hl hle.
  move: (hle' (e_reg env r).1 l foo')=> hle1. rewrite hrho /= in hle1. 
  apply Public_only_less_than_Public in hle1.
  move: (hreg r (e_reg env r).1 (e_reg env r).2 henv hle1)=> {hreg} hreg. 
  admit.
(* Regx *)
+ move=> r hassert [] hv1 hleak1 hassert' [] hv2 hleak2; subst. case: ty=> //=.
  move=> ws hregxty. rewrite /value_equiv. split=> //=.
  move=> l hl hrho. 
  have henv : e_regx env r = ((e_regx env r).1, (e_regx env r).2). 
  + by case: (e_regx env r)=> //=.
  rewrite henv /= in hregxty. move: hregxty. move=> /andP [] hle hws.
  rewrite /le_all in hle. rewrite /is_le in hle'. have foo' := foo hl hle.
  move: (hle' (e_regx env r).1 l foo')=> hle1. rewrite hrho /= in hle1. 
  apply Public_only_less_than_Public in hle1.
  move: (hregx r (e_regx env r).1 (e_regx env r).2 henv hle1)=> {hregx} hregx. 
  admit.
(* Addr *)
+ move=> adr hassert. case: ty=> //=.
  move=> ws. case: ak=> //=.
  (* AK_compute *)
  + move=> [] hv1 hleak1 hassert' [] hv2 hleak2 hwt; subst. 
    rewrite /value_equiv /decode_addr /decode_reg_addr.
    split=> //=. move=> l hl hrho.
    rewrite /decode_addr. case: adr hassert hassert' hwt=> //=.
    (* reg adr *)
    + move=> r hassert hassert' /andP [] hwt hwt'. rewrite /wt_oreg in hwt hwt'.
      case: (ad_base r) hwt.
      (* some *)   
      + move=> ar /= har. case: (ad_offset r) hwt'=> //=.
        (* some *)
        + move=> ao /= hao. have henv : e_reg env ar = ((e_reg env ar).1, (e_reg env ar).2). 
          + by case: (e_reg env ar)=> //=. rewrite henv in har. move: har.
          move=> /andP [] hle hws. rewrite /le_all in hle. rewrite /is_le in hle'. 
          have foo' := foo hl hle.
          move: (hle' (e_reg env ar).1 l foo')=> hle1. rewrite hrho /= in hle1. 
          apply Public_only_less_than_Public in hle1.
          move: (hreg ar (e_reg env ar).1 (e_reg env ar).2 henv hle1)=> hreg1. 
          have henv' : e_reg env ao = ((e_reg env ao).1, (e_reg env ao).2). 
          + by case: (e_reg env ao)=> //=. rewrite henv' in hao. move: hao.
          move=> /andP [] hle'' hws'. rewrite /le_all in hle''. rewrite /is_le in hle'. 
          have foo'' := foo hl hle''.
          move: (hle' (e_reg env ao).1 l foo'')=> hle1'. rewrite hrho /= in hle1'. 
          apply Public_only_less_than_Public in hle1'.
          move: (hreg ao (e_reg env ao).1 (e_reg env ao).2 henv' hle1')=> hreg2. admit.
        (* none *)
        move=> ht. have henv : e_reg env ar = ((e_reg env ar).1, (e_reg env ar).2). 
        + by case: (e_reg env ar)=> //=. rewrite henv in har. move: har.
        move=> /andP [] hle hws. rewrite /le_all in hle. rewrite /is_le in hle'. 
        have foo' := foo hl hle.
        move: (hle' (e_reg env ar).1 l foo')=> hle1. rewrite hrho /= in hle1. 
        apply Public_only_less_than_Public in hle1.
        move: (hreg ar (e_reg env ar).1 (e_reg env ar).2 henv hle1)=> hreg1. admit.
     (* None *)
     case: (ad_offset r) hwt'=> //=. move=> ao hao ht.
     have henv' : e_reg env ao = ((e_reg env ao).1, (e_reg env ao).2). 
     + by case: (e_reg env ao)=> //=. rewrite henv' in hao. move: hao.
     move=> /andP [] hle'' hws'. rewrite /le_all in hle''. rewrite /is_le in hle'. 
     have foo'' := foo hl hle''.
     move: (hle' (e_reg env ao).1 l foo'')=> hle1'. rewrite hrho /= in hle1'. 
     apply Public_only_less_than_Public in hle1'.
     move: (hreg ao (e_reg env ao).1 (e_reg env ao).2 henv' hle1')=> hreg2. admit.
   (* Arip *)
   move=> s hassert hassert' hle. rewrite /le_all in hle; subst. admit.
 (* mem *)
 t_xrbindP=> rv hread hv1 hleak1 hassert' rv' hread' hv2 hleak2 hwt; subst.
 (*case: pt hwt=> //=.
 + move=> ptto hwt. split.
   + rewrite /value_equiv. move=> l hl hrho. rewrite /wt_addr in hwt.
     case: adr hassert hread hassert' hread' hwt=> //=.
     + move=> r hassert hread hassert' hread' /andP [/andP [hwt hwt'] hle].
       rewrite /wt_oreg in hwt hwt'. rewrite /decode_reg_addr /= in hread hread'. 
       case: (ad_base r) hwt hread hread'=> //=.*) admit.
(* XReg *)
move=> r hassert [] hv1 hleak1 hassert' [] hv2 hleak2; subst. case: ty=> //=.
move=> ws hxregty. rewrite /value_equiv. split=> //=.
move=> l hl hrho. 
have henv : e_xreg env r = ((e_xreg env r).1, (e_xreg env r).2). 
+ by case: (e_xreg env r)=> //=.
rewrite henv /= in hxregty. move: hxregty. move=> /andP [] hle hws.
rewrite /le_all in hle. rewrite /is_le in hle'. have foo' := foo hl hle.
move: (hle' (e_xreg env r).1 l foo')=> hle1. rewrite hrho /= in hle1. 
apply Public_only_less_than_Public in hle1.
move: (hxreg r (e_xreg env r).1 (e_xreg env r).2 henv hle1)=> {hxreg} hxreg. 
admit.
Admitted.

(*find_label lbl code2 = ok pc
find_label lbl (asm_fd_body fundef) = ok pc''*)

(* Type preserves state equivalence *) 
Lemma type_prev_state_equivalence : forall Env env env' rho s1 s2 c P Pt_info pts s1' s2' l1 l2, 
wt_code wt_cond fn c pts Env Pt_info s1.(asm_c) ->
oseq.onth Env s1.(asm_ip) = Some env ->
valid_valuation c rho ->
state_equiv rho s1 s2 env ->
asmsem1 P s1 l1 s1' ->
asmsem1 P s2 l2 s2' ->
oseq.onth Env s1'.(asm_ip) = Some env' ->
state_equiv rho s1' s2' env'.
Proof.
move=> Env env env' rho [] /= m1 fn1 code1 pc1 [] m2 fn2 code2 pc2 c P Pt_info pts s1' s2' l1 l2 hwt hpcenv hvalid hequiv.
have hequivcopy := hequiv. move: hequiv.
move=> [] /= hcode hpc hreg hregx hxreg hflag hmem hstep1 hstep2 hpcenv'; subst.
rewrite /wt_code /= in hwt.
move: (hwt pc2)=> /= hwtpc2. 
have hpc : pc2 < size code2. + admit. 
move: (hwtpc2 hpc)=> {hwtpc2} hwtpc2.
move: env env' hpcenv hpcenv' hreg hregx hxreg hflag hmem hequivcopy.
case: hwtpc2.
(* AsmOp *)
+ move=> o args env env' dpt apt env1 hpci hpcenv hpcenv' /= hn hargs htydests hle.
  rewrite hpcenv /=. move=> env1' env2' [] h; subst. move=> henv' hreg hregx hxreg hflag hmem hequivcopy.
  inversion hstep1; inversion hstep2; subst. rewrite /fetch_and_eval hpci /= in H0 H1.
  move: H0. t_xrbindP=> -[m leak] heval /= hs1' hleak. move: H1. t_xrbindP=> -[m' leak'] heval' /= hs2' hleak'.
  rewrite /st_update_next /= in hs1' hs2'. rewrite -hs1' -hs2' /=; subst. rewrite /= hpcenv' in henv'. case: henv'=> h; subst. 
  (*constructor; auto.
  + move=> r l ws hregty hrho /=. rewrite /ty_dests /= in htydests. case: (id_out (instr_desc_op o)) hargs htydests=> //=.
    + (* empty case: arg_desc *) admit.
    move=> a al hargs. case: dpt hn hargs=> //=.
    move=> pt ptl hn hargs. case: (id_tout (instr_desc_op o))=> //=.
    move=> st stl. t_xrbindP=> envi htydest /= htydests. rewrite /ty_dest in htydest.
    case: a hargs htydest=> //=.
    (* Implicit args *)
    + move=> i hargs htydest. *) admit.

(* Align *)
+ move=> env env' hpci hpcenv hpcenv' hle. rewrite hpcenv /=.
  move=> env1 env2 [] henv; subst. move=> hpcenv'' hreg hregx hxreg hflag hmem hequivcopy; subst.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval /= hpci /= in H0 H1.
  case: H0=> h h'; case: H1=> h'' h'''; subst.
  constructor; auto.
  + move=> r l ws hregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hreg' r l ws hregty hrho).
  + move=> r l ws hregxty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hregx' r l ws hregxty hrho).
  + move=> r l ws hxregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hxreg' r l ws hxregty hrho).
  + move=> f l hfty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hflag' f l hfty hrho).
  move=> pt l adr vp pts' hwvp hvp hpt hrho i hi. rewrite /= in hpcenv''. 
  rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
  have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
  case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
  by move: (hmem' pt l adr vp pts' hwvp hvp hpt hrho i hi).
(* LABEL lbl *)
+ move=> env env' lbl hpci hpcenv hpcenv' hle. rewrite hpcenv /=.
  move=> env1 env2 [] henv; subst. move=> hpcenv'' hreg hregx hxreg hflag hmem hequivcopy; subst.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval /= hpci /= in H0 H1.
  case: H0=> h h'; case: H1=> h'' h'''; subst.
  constructor; auto.
  + move=> r l ws hregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hreg' r l ws hregty hrho).
  + move=> r l ws hregxty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hregx' r l ws hregxty hrho).
  + move=> r l ws hxregty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h; subst.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hxreg' r l ws hxregty hrho).
  + move=> f l hfty hrho /=. rewrite /= in hpcenv''. 
    rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
    have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
    case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
    by move: (hflag' f l hfty hrho).
  move=> pt l adr vp pts' hwvp hvp hpt hrho i hi. rewrite /= in hpcenv''. 
  rewrite hpcenv' in hpcenv''. case: hpcenv''=> h. rewrite h in hle.
  have hequiv' := state_equiv_env_env' hequivcopy hvalid hle. 
  case: hequiv'=> /= hcode hpc' hreg' hregx' hxreg' hflag' hmem'.
  by move: (hmem' pt l adr vp pts' hwvp hvp hpt hrho i hi).
(* JMP (fn', lbl) *)
+ move=> env env' fn' lbl pc hpci hpcenv /eqP hfn.
  inversion hstep1; inversion hstep2. rewrite /fetch_and_eval /= hpci /= in H0 H1; subst.
  case: (get_fundef (asm_funcs P) fn') H0 H1=> //= fundef /= H0 H1; subst.
  move: H0. t_xrbindP=> pc' hlb' /= hs1' hleak; subst. move: H1. t_xrbindP=> pc'' hlb'' /= hs2' hleak'; subst.
  rewrite hlb' in hlb''. case: hlb''=> h; subst. 
  move=> hlbl hpcenv' hle env1 env2. rewrite hpcenv. move=> [] h; subst.   
  move=> hpcenv'' hreg hregx hxreg hflag hmem hequivcopy; subst.
  constructor; auto; subst.
  + admit.
  + admit.
  + admit.
  + admit.
  admit. 
(* JCC lbl ct *)
move=> env envf envt lbl ip ct hpci hpcenv hwct hlbl henvf henvt [hlef hlet] env1 env2.
rewrite hpcenv. move=> [] h; subst. move=> hpcenv' hreg hregx hxreg hflag hmem hequivcopy.
inversion hstep1; inversion hstep2. rewrite /fetch_and_eval /= hpci /= in H0 H1; subst.
rewrite /eval_Jcc /= in H0 H1. move: H0. t_xrbindP=> b hevalm pc hb hs1' hleak; subst.
move: H1. t_xrbindP=> b' hevalm' pc' hb' hs2' hleak'; subst. rewrite /= in hpcenv'. 
admit.
Admitted. 

(* Type preserves constant-time *) 
Lemma type_prev_leakage : forall Env env rho s1 s2 c P Pt_info pts s1' s2' l1 l2, 
wt_code wt_cond fn c pts Env Pt_info s1.(asm_c) ->
oseq.onth Env s1.(asm_ip) = Some env -> 
valid_valuation c rho ->
state_equiv rho s1 s2 env ->
asmsem1 P s1 l1 s1' ->
asmsem1 P s2 l2 s2' ->
l1 = l2.
Proof.
Admitted.

