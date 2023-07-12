From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Export array type expr gen_map low_memory warray_ sem_type sem_op_typed values typing sem.
Require Export
  flag_combination
  sem_params.

Section TYPING_PEXPR.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  (gd : glob_decls).

(* If a well-typed expression progresses to a value then the value has the same type *) 
Theorem sem_pexpr_well_typed : forall pd ty e s v,
ty_pexpr pd e = ok ty ->
sem_pexpr gd s e = ok v ->
type_of_val v = ty.
Proof.
move=> pd ty e s v hty hsem. case: e hty hsem.
(* Pconst *)
+ rewrite /ty_pexpr /sem_pexpr /type_of_val. by move=> z [<-] [<-]. 
(* Pbool *)
+ rewrite /ty_pexpr /sem_pexpr /type_of_val. by move=> b [<-] [<-].
(* Parr_init *)
+ rewrite /ty_pexpr /sem_pexpr /type_of_val. by move=> a [<-] [<-].  
(* Pvar *)
+ rewrite /ty_pexpr /sem_pexpr. move=> g [] <- hg. by have := type_of_get_gvar hg.
(* Pget *)
+ move=> a w g p /=. rewrite /ty_get_set /=. t_xrbindP=> tp htp ta htc ti hti <- /=.
  apply on_arr_gvarP. move=> n t harr hget. by t_xrbindP=> z zv hp hi z1 hz1 <- /=.
(* Psub *)
+ move=> a w p g p' /=. rewrite /ty_get_set_sub /=. t_xrbindP=> tp htp ta htc ti hti /= heq; subst.
  apply on_arr_gvarP. move=> n t harr hget. 
  t_xrbindP=> z zv he hi /= z1 hg hv; subst. by have heq' := to_intI hi; subst; rewrite /=. 
(* Pload *)
+ move=> w vi e /=. rewrite /ty_load_store /=. t_xrbindP=> pt het vit. rewrite /check_ptr /= /check_type.
  case: ifP => //=. case: (vtype vi)=> //= wsz hpd [] heq; subst. case: pt het=> //= wsz' het zt. 
  case: ifP=> //= hpd' [] heq; subst. move=> heq; subst. by move=> zw viv hg hp zw' viv' he hp' wz hr <- /=. 
(* Papp1 *)
+ move=> op e /=. rewrite /check_expr /= /check_type /=. case: op=> //=.
  + t_xrbindP=> w et et' het. case: ifP=> //= /eqP heq [] heq' hty; subst.
    move=> zv he hop. by have [x hov -> /=] := sem_sop1I hop.
  + t_xrbindP=> w zt zt' /= het. case: zt' het=> //= w' het. case: ifP=> //= hcmp [] heq hty'; subst.
    move=> z he hop. by have [x hov -> /=] := sem_sop1I hop.
  + t_xrbindP=> w w' zt zt' het. case: zt' het=> //= w'' het. case: ifP=> //= hcmp [] heq hty; subst.
    move=> z he hop. by have [x hov -> /=] := sem_sop1I hop.
  + t_xrbindP=> w w' zt zt' het. case: zt' het=> //= w'' het. case: ifP=> //= hcmp [] heq hty; subst.
    move=> z he hop. by have [x hov -> /=] := sem_sop1I hop.
  + t_xrbindP=> zt zt' het. case: ifP=> //= /eqP heq [] heq' hty; subst. move=> zv he hop.
    by have [x hov -> /=] := sem_sop1I hop.
  + t_xrbindP=> w zt zt' het. case: zt' het=> //= w' het. case: ifP=> //= hcmp [] heq hty; subst.
    move=> zv he hop. by have [x hov -> /=] := sem_sop1I hop. 
  move=> ok. case: ok=> //=.
  + t_xrbindP=> zt zt' /= hty. case: ifP=> //= /eqP heq [] heq' heq''; subst.
    move=> zv he hop. by have [x hov -> /=] := sem_sop1I hop.
  move=> w. t_xrbindP=> te te' hty. case: te' hty=> //= wsz hty. case: ifP=> //= hcmp [] ht ht'; subst.
  move=> zv he hop. by have [x hov -> /=] := sem_sop1I hop.
(* Papp2 *)
+ move=> op2 e1 e2 /=. rewrite /check_expr /= /check_type. t_xrbindP=> et1 et1' hty1. 
  case: ifP=> //= hsub [] heq et2 et2' hty2; subst. case: ifP=> //= hsub' [] heq' hty'; subst.
  move=> ev1 /= he1 ev2 he2 hop. have [w1 [w2 [w3 [/= hv hv' hop' hveq]]]] := sem_sop2I hop; subst.
  by apply type_of_to_val.
(* PappN *)
+ admit.
(* Pif *)
move=> sty b e1 e2 /=. rewrite /check_expr /= /check_type /=. 
t_xrbindP=> bty bty' htb. case: ifP=> //= /eqP heq; subst. move=> [] heq'; subst.
move=> e1t e1t' hte1. case: ifP=> //= hsub [] heq; subst. move=> e2t e2t' hte2.
case: ifP=> //= hsub' [] heq; subst. move=> hteq; subst. move=> bv bv' hb hbt e1v e1v' he1 ht e2v e2v' he2 ht' <-.
case: ifP=> //= _. by have := truncate_val_has_type ht. by have := truncate_val_has_type ht'.
Admitted.

Lemma get_gvar_not_tyerr : forall pd g ty s v,
ty_pexpr pd (Pvar g) = ok ty ->
get_gvar gd (evm s) g = Error v ->
v <> ErrType.
Proof.
move=> pd g ty s v /= [] hty. rewrite /get_gvar /=. case: ifP=> //=.
+ rewrite /get_var /= /on_vu. Search stype get_var. Check on_vuP. /on_vu. Print on Locate wf_vmap. Search vmap.  admit.
rewrite /get_global /=. case: g hty=> //=.
move=> gv gs -> /=. case: gv=> //= gr gi. case: gr=> //= gt gn. case: get_global_value=> //= a.


 case: (get_global_value gd (gv g))=> //=.
+ move=> a hf. case: ifP=> //= /eqP; subst. rewrite /type_of_val /=.
  case: (gv2val a)=> //=.
Admitted.

Theorem sem_pexpr_type_error : forall pd ty e s er,
ty_pexpr pd e = ok ty ->
sem_pexpr gd s e = Error er ->
er <> ErrType. 
Proof.
move=> pd ty e s v hty hsem. case: e hty hsem.
(* Pconst *)
+ by move=> z /= [] hty //=.
(* Pbool *)
+ by move=> b /= [] hty //=.
(* Parr_init *)
+ by move=> p /= [] hty //=.
(* Pgvar *)
+ move=> g. /= [] hty hg.  Search get_gvar.


case: g hty hg=> //= gi gs hty.
  case: get_gvar=> //= er. case: er=> //=. rewrite /vtype /= in hty.
move=> g /= [] hty. case: get_gvar=> //= e. case: e=> //=. 
  + by move=> [] <-. rewrite /get_gvar /=.
  case: ifP=> //=.
  (* lvar *)
  + move=> hl. case: get_var=> //.
(* Pget *)
+ move=> a w g e. rewrite /ty_get_set /check_array. 
  t_xrbindP=> t ht t'. admit.
(* Psub *)
+ admit.
(* Pload *)
+ move=> w x e hty he. have hrec := sem_pexpr_well_typed pd ty (Pload w x e) s. 
  rewrite hty in hrec. rewrite /= /ty_load_store /check_ptr /check_type in hty. move: hty.
  t_xrbindP=> t ht t'. case: ifP=> //=; subst. case: (vtype x)=> //=.
  move=> sz' hcmp [] heq; subst. case: t ht=> //= sz'' ht t1'. 
  case: ifP=> //= hcmp' [] heq'' hty; subst. 
  case: v he=> //=. 


case: get_var=> //=.
  + move=> p. case: to_pointer=> //=. admit. move=> e0 [] //= he; subst.
 admit.
(* Papp1 *)
+ admit.
(* Papp2 *)
+ admit.
(* Pappn *)
+ admit.
(* Pif *)
move=> t e1 e2 e3 hty he; subst. Print sem_pexpr.
Admitted. 
