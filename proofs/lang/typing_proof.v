From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Export array type expr gen_map low_memory warray_ sem_type sem_op_typed values psem_defs
typing psem.
Require Export
  flag_combination
  sem_params.


Section Supporting_lemmas.

Context
  {wsw : WithSubWord}.

(*Lemma get_var_undef_sub vm x v ty h :
get_var false vm x = ok v -> v <> Vundef ty h.
Proof.
Admitted.

Lemma get_gvar_undef_nosub gd vm x v ty h :
get_gvar false gd vm x = ok v -> v <> Vundef ty h.
Proof.
Admitted.

Lemma type_of_get_gvar_nosub x gd vm v :
get_gvar false gd vm x = ok v ->
type_of_val v = vtype x.(gv).
Proof.
Admitted.*)

End Supporting_lemmas.

Section TYPING_PEXPR.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  (wdb : bool)
  (gd : glob_decls).

(* If a well-typed expression progresses to a value then the value has the same type.
   The property is only proved for the source-level semantics. *) 
Theorem sem_pexpr_well_typed : forall pd ty e s v,
ty_pexpr pd e = ok ty ->
sem_pexpr (wsw:= nosubword) false gd s e = ok v ->
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
+ rewrite /ty_pexpr /sem_pexpr. move=> g [] <- hg. admit.
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
  case: ifP=> //= hpd' [] heq; subst. move=> heq; subst. 
  by move=> zw hp zw' zv he hp' wz hr <- /=. 
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

Lemma get_gvar_not_tyerr : forall g ty s v,
vtype (gv g) = ty ->
get_gvar (wsw := nosubword) false gd (evm s) g = Error v ->
v <> ErrType.
Proof.
move=> g ty s v /= [] hty. rewrite /get_gvar /=. case: ifP=> //=.
(* Need something like well formedness *)
admit.
Admitted.

Lemma truncate_val_not_tyerr : forall ty v v',
subtype ty (type_of_val v) ->
truncate_val ty v = Error v' ->
v' <> ErrType.
Proof.
move=> ty v v' hsub ht. case: v hsub ht=> //=.
+ move=> b hsub ht. have hty := subtypeE hsub; subst. rewrite /truncate_val /= in ht.
  by case: ht.
+ move=> z hsub ht. have hty := subtypeE hsub; subst. rewrite /truncate_val /= in ht.
  by case: ht.
+ move=> len arr hsub ht. have hty := subtypeE hsub; subst. rewrite /truncate_val /= in ht.
  move: ht. case ha: WArray.cast=> [av | aerr] //=. move=> [] hv; subst. rewrite /WArray.cast /= in ha. 
  move: ha. by case: ifP=> //= /eqP //=.
+ move=> sz wsz hsub ht. have [sz' [hty hsz']] := subtypeE hsub; subst. rewrite /truncate_val /= in ht.
  move: ht. case ht: truncate_word=> [wv | werr] //=. move=> [] hv; subst. have [h1 h2] := truncate_word_errP ht.
  by rewrite -cmp_nle_lt hsz' in h2. 
move=> t ti hsub ht. rewrite /truncate_val /= in ht. move: ht.
case hv : of_val=> [vv | verr] //=. move=> [] hv'; subst. have []:= is_undef_tE ti.
+ move=> ht; subst. have ht := subtypeE hsub; subst. rewrite /of_val /= /undef_error in hv. by case: hv=> heq; subst.
+ move=> ht; subst. have ht := subtypeE hsub; subst. rewrite /of_val /= /undef_error in hv. by case: hv=> heq; subst.
move=> ht; subst. have [w [hty hsz']] := subtypeE hsub; subst. rewrite /of_val /= /undef_error in hv. 
by case: hv=> heq; subst.
Qed.

Lemma to_bool_not_tyerr : forall b v,
type_of_val b = sbool ->
to_bool b = Error v ->
v <> ErrType.
Proof.
move=> b v ht hb. rewrite /to_bool /= in hb.
case: b ht hb=> //= t ht hb; subst; rewrite /undef_error.
by move=> [] hv; subst.
Qed.

Theorem sem_pexpr_type_error : forall pd ty e s er,
ty_pexpr pd e = ok ty ->
sem_pexpr (wsw:= nosubword) false gd s e = Error er ->
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
+ move=> g hty hg. admit.
(* Pget : a[e] where e is index *)
+ move=> a w g e /=. rewrite /ty_get_set.
  t_xrbindP=> te he. rewrite /check_array /=. move=> ta. case hta : (vtype (gv g))=> [ | | p |] //= [] heq; subst.
  move=> ti. rewrite /check_int /check_type. case: ifP=> //= /eqP hte [] hte' hty; subst.
  rewrite /on_arr_var /=. have hg := get_gvar_not_tyerr g (sarr p) s v hta. 
  case hgc: get_gvar=> [gv| gerr] //=.
  (* get_gvar evaluates to ok state *)
  + have [/= _ hc]:= get_gvar_compat hgc. rewrite hta in hc. 
    have hgv := compat_val_vm_truncate_val hc; subst. case: gv hgc hc hgv=> //=.
    move=> len alen hgc hc. case: ifP=> //=.
    + move=> /eqP hl hl' /=; subst. case hec: sem_pexpr=> [ve | eerr] //=.
      (* sem_pexpr evaluates to ok state *)
      + case hic : to_int=> [vi | ierr] //=.
        (* to_int evaluates to ok state *)
        + rewrite /WArray.get /=. case hrc: read=> [rv | rerr] //=. move=> [] hveq; subst.
          have hti := sem_pexpr_well_typed pd sint e s ve he hec. have hve := type_of_valI hti.
          case: hve=> //=. 
          + move=> hveq; subst. rewrite /to_int /undef_error in hic. by case: hic.
          move=> [] x hx; subst. rewrite /to_int in hic. case: hic=> hiceq; subst.
          admit.
        (* to_int evaluates to error state *)
        move=> [] hveq; subst. have htv := sem_pexpr_well_typed pd sint e s ve he hec. 
        case: ve he hec htv hic=> //= t i he hec hic ht; subst. by case: ht=> [] <-. 
      (* sem_pexpr evaluates to error state *)
      move=> [] hv; subst. admit.
    move=> /eqP hlen [] hlen'. by rewrite hlen' in hlen.
 (* get_gvar evaluates to error state *)
  move=> [] hv; subst. by have := get_gvar_not_tyerr g (sarr p) s v hta hgc.
(* Psub *)
+ admit.
(* Pload : [e] where e is the memory address *)
+ move=> w vi e /=. rewrite /ty_load_store /=. t_xrbindP=> te hte tptr /=. rewrite /check_ptr /check_type.
  case: ifP=> //=. case htp: (vtype vi)=> [| | |ptr] //= hsz [] heq; subst. move=> tptr. 
  case hte': te hte=> [| | | we] //=; subst. case: ifP=> //= hsz' hte [] heq htyeq; subst.
  case hptr : to_pointer=> [ptrv|ptrerr] //=.
  (* to_pointer evaluates to ok state *)
  + case he : sem_pexpr=> [ev| eerr]//=.
    (* sem_pexpr evaluates to ok state *)
    + case hptr' : to_pointer=> [ptrv'|ptrerr'] //=.
      (* to_pointer evaluates to ok state *)
      + case hr : read=> [rv | rerr] //=. move=> [] hv; subst. 
        have htev := sem_pexpr_well_typed pd (sword we) e s ev hte he. 
        have [sz' [w' [hvm ht]]] := to_wordI hptr. have [huptr hptrv] := truncate_wordP ht.
        rewrite hptrv /= in hr. have [sz1 [wsz1 [hev ht']]]:= to_wordI hptr'.
        have [huptr' hptrv']:= truncate_wordP ht'. admit.
      (* to_pointer evaluates to error state *)
      move=> [] hv; subst. have htev := sem_pexpr_well_typed pd (sword we) e s ev hte he. 
      rewrite /type_of_val /= in htev. case: ev he hptr' htev=> //=.
      + move=> sz1 wsz1 he hptr' [] heq; subst. have [h1 h2] := truncate_word_errP hptr'.
        admit.
      move=> t i /= he. case: t i he=> //= sz i he. rewrite /undef_error /=. by move=> [] hv; subst.
    (* sem_pexpr evaluates to an error state *)
    + admit.
  (* to_pointer evaluates to an error state *)
  + move=> [] hv; subst. admit.
(* Papp1 *)
+ move=> op e /=. admit.
(* Papp2 *)
+ admit.
(* Pappn *)
+ admit.
(* Pif *)
move=> t e e1 e2 /=. rewrite /check_expr /= /check_type /=. 
t_xrbindP=> te te' hte. case: ifP=> //= /eqP hte'eq [] h1; subst.
move=> te1 te1' hte1. case: ifP=> //= hsub [] heq; subst.
move=> te2 te2' hte2. case: ifP=> //= hsub' [] heq1 hrq2; subst.
case he2: sem_pexpr=> //= [ev2 | eerr2]. have hev2 := sem_pexpr_well_typed pd te2 e2 s ev2 hte2 he2.
(* sem_pexpr of e2 evaluates to ok state *)
+ case he1: sem_pexpr=> //= [ev1 | eerr1]. have hev1 := sem_pexpr_well_typed pd te1 e1 s ev1 hte1 he1. 
  (* sem_pexpr of e1 evaluates to ok state *)
  + case he: sem_pexpr=> //= [ev | eerr].
    (* sem_pexpr of e evaluates to ok state *)
    + have hev := sem_pexpr_well_typed pd sbool e s ev hte he.
      case hb : to_bool=> [bv | berrr] //=.
      (* to_bool evaluates to ok state *)
      + case ht2 : truncate_val=> [tv | terr] //=.
        (* truncate_val of ev2 evaluates to ok state *)
        + case ht1 : truncate_val => [tv' | terr'] //=.
          (* truncate_val of ev1 evaluates to error state *)
          move=> [] hv; subst. by have := truncate_val_not_tyerr ty ev1 v hsub ht1.
        (* truncate_val of ev2 evaluates to error state *)
        move=> ht1. rewrite -hev2 in hsub'. have her := truncate_val_not_tyerr ty ev2 terr hsub' ht2.
        rewrite -hev1 in hsub. move: ht1. case ht1: truncate_val=> [tv1 | terr1] //=.
        + by move=> [] hv; subst.
        move=> [] hv; subst. by have := truncate_val_not_tyerr ty ev1 v hsub ht1.
     (* to_bool evaluates to error state *)
     move=> [] hv; subst. by have := to_bool_not_tyerr ev v hev hb.  
    (* sem_pexpr of e evaluates to error state *)
    move=> [] hv; subst. admit.
  (* sem_pexpr of e1 evaluates to error state *)
  case he : sem_pexpr=> [ev | eerr] //=.
  (* sem_pexpr of e evaluates to ok state *)
  + have htev := sem_pexpr_well_typed pd sbool e s ev hte he. case: ev he htev=> //=.
    + move=> b he _ [] hv; subst. admit.
    move=> t ht he hteq /=; subst. rewrite /undef_error /=. by move=> [] hv; subst.
  (* sem_pexpr of e evaluates to error state *)
  move=> [] hv; subst. admit.
(* sem_pexpr of e2 evaluates to error state *)
case he1 : sem_pexpr=> [ev1| eerr1] //=.
(* sem_pexpr of e1 evaluates to ok state *)
+ case he : sem_pexpr=> [ev| eerr] //=.
  (* sem_pexpr of e evaluates to ok state *)
  + admit.
  (* sem_pexpr of e evalautes to error state *)
  move=> [] hv; subst. admit.
(* sem_pexpr of e1 evaluates to error state *)
case he : sem_pexpr=> [ev | eerr] //=.
(* sem_pepxr of e evaluates to ok state *)
+ admit.
(* sem_pexpr of e evaluates to error state *)
move=> [] hv; subst. admit.
Admitted. 
