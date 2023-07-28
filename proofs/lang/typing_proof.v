From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Export array type expr gen_map low_memory warray_ sem_type sem_op_typed values psem_defs
typing psem.
Require Export
  flag_combination
  sem_params.


Section Supporting_lemmas.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {wsw : WithSubWord}
  (wdb : bool)
  (gd : glob_decls).

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
  {wsw : WithSubWord}
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

Lemma to_int_not_tyerr : forall i v,
type_of_val i = sint ->
to_int i = Error v ->
v <> ErrType.
Proof.
move=> i v ht hi. rewrite /to_int /= in hi.
case: i ht hi=> //= t ht hi; subst; rewrite /undef_error.
by move=> [] hv; subst.
Qed.

Lemma to_arr_not_tyerr : forall i p v,
type_of_val i = (sarr p) ->
to_arr p i = Error v ->
v <> ErrType.
Proof.
move=> i p v ht hi. rewrite /to_arr /= in hi. 
case: i ht hi=> //= t ht [] hi; subst. 
+ rewrite /WArray.cast /=. by case: ifP=> //= /eqP //=. 
rewrite /type_error. move=> [] hv; subst.
rewrite /is_undef_t /= in ht. move: ht. by move=> /eqP.
Qed.

Lemma to_word_not_tyerr : forall sz sz' ev v,
(sz' <= sz)%CMP -> 
type_of_val ev = (sword sz) ->
to_word sz' ev = Error v ->
v <> ErrType.
Proof.
move=> sz sz' ev v hsz hte. rewrite /to_word /=.
case: ev hte=> //=.
+ move=> sz'' w [] heq ht; subst. have [h1 h2] := truncate_word_errP ht.
  by rewrite -cmp_nle_lt hsz in h2.
move=> t ht heq; subst. rewrite /undef_error. by move=> [] hv; subst.
Qed.

Lemma sem_sop1_not_tyerr : forall pd e s tin tout ty ev op ov,
type_of_op1 op = (tin, tout) ->
subtype tin ty ->
ty_pexpr pd e = ok ty ->
sem_pexpr (wsw:= nosubword) false gd s e = ok ev ->
sem_sop1 op ev = Error ov ->
ov <> ErrType.
Proof.
move=> pd e s tin tout ty ev op er /= hty hsub hte he hop.
rewrite /sem_sop1 /= in hop. move: hop.
case hof : of_val=> [ov | oerr] //=. move=> [] hv; subst.
rewrite hty /= in hof. 
case: tin hty hsub hof=> //=.
+ move=> hty /eqP ht hb; subst. 
  have heb := sem_pexpr_well_typed pd sbool e s ev hte he.
  by have := to_bool_not_tyerr ev er heb hb. 
+ move=> hty /eqP ht hi; subst. have hei := sem_pexpr_well_typed pd sint e s ev hte he.
  by have := to_int_not_tyerr ev er hei hi.
+ move=> p /= hty /eqP ht ha; subst. have hai := sem_pexpr_well_typed pd (sarr p) e s ev hte he.
  by have := to_arr_not_tyerr ev p er hai ha.
+ move=> w hty. case: ty hte=> //= w' hte hsz hw.
  have hev := sem_pexpr_well_typed pd (sword w') e s ev hte he.
  by have := to_word_not_tyerr w' w ev er hsz hev hw.
Qed.

Lemma sem_sop2_not_tyerr : forall pd op te1 te2 s e1 ev1 e2 ev2 er,
subtype (type_of_op2 op).1.1 te1 ->
subtype (type_of_op2 op).1.2 te2 ->
ty_pexpr pd e1 = ok te1 ->
ty_pexpr pd e2 = ok te2 ->
sem_pexpr (wsw:= nosubword) false gd s e1 = ok ev1 ->
sem_pexpr (wsw:= nosubword) false gd s e2 = ok ev2 ->
sem_sop2 op ev1 ev2 = Error er ->
er <> ErrType.
Proof.
move=> i p v te2 s e1 ev1 e2 ev2 er hsub hsub' hte1 hte2 he1 he2. 
rewrite /sem_sop2 /=. 
case hv2 : of_val=> [v2 | err2] //=.
(* of_val of second argument evaluates to ok *)
+ case hv1 : of_val=> [v1 | err1] //=.
  (* of_val of first argument evaluates to ok *)
  + case ho : sem_sop2_typed=> [vo | erro] //=.
    move=> [] hv; subst. have hsub1 := of_val_subtype hv1.
    have hsub2 := of_val_subtype hv2. 
    have htev1 := sem_pexpr_well_typed i v e1 s ev1 hte1 he1.
    have htev2 := sem_pexpr_well_typed i te2 e2 s ev2 hte2 he2.
    rewrite htev1 /= in hsub1. rewrite htev2 /= in hsub2.
    subst.
Admitted.  

Lemma sem_sopN_not_tyerr : forall pd e te es tys tes ev mv er op s,
ty_pexpr pd e = ok te ->
mapM2 ErrType 
(fun (e : pexpr) (ty : stype) => 
  Let te := ty_pexpr pd e in (if subtype ty te then ok te else type_error)) es tys = ok tes ->
sem_pexpr (wsw := nosubword) false gd s e = ok ev ->
mapM (sem_pexpr false gd s) es = ok mv ->
sem_opN op (ev :: mv) = Error er ->
er <> ErrType.
Proof.
Admitted.

Lemma read_sint_not_tyerr : forall s e ve vi p (alen:WArray.array p) a w er,
sem_pexpr (wsw := nosubword) false gd s e = ok ve ->
to_int ve = ok vi ->
read alen (vi * mk_scale a w)%Z w = Error er ->
type_of_val ve = sint ->
compat_val (wsw := nosubword) (sarr p) (Varr alen) ->
er <> ErrType.
Proof.
Admitted.

Lemma read_ptr_not_tyerr: forall pd s e ev we vi ptrv ptrv' er w,
sem_pexpr (wsw := nosubword) false gd s e = ok ev ->
ty_pexpr pd e = ok (sword we) ->
to_pointer (evm s).[vi] = ok ptrv ->
to_pointer ev = ok ptrv' ->
read (emem s) (ptrv + ptrv')%R w = Error er ->
er <> ErrType.
Proof.
Admitted.

Lemma to_pointer_not_tyerr : forall s e ev we er,
sem_pexpr (wsw := nosubword) false gd s e = ok ev ->
type_of_val ev = sword we ->
to_pointer ev = Error er ->
er <> ErrType.
Proof.
move=> s e ev we er he ht hp.
Admitted.

Lemma to_pointer_not_tyerr_var : 
forall (s : @estate nosubword syscall_state ep) vi ptr er,
vtype vi = sword ptr -> 
to_pointer (evm s).[vi] = Error er ->
er <> ErrType.
Proof.
move=> s vi ptr er hty hptr. have hc := Vm.getP (evm s) vi.
rewrite /to_pointer /= in hptr. case: ((evm s).[vi]) hc hptr=> //=.
+ move=> b hc [] hv; subst.
Admitted.

Theorem sem_pexpr_type_error : forall pd ty e s er,
ty_pexpr pd e = ok ty ->
sem_pexpr (wsw:= nosubword) false gd s e = Error er ->
er <> ErrType. 
Proof.
move=> pd ty e. move: ty. elim: e. 
(* Pconst *)
+ by move=> z /= [] hty //=.
(* Pbool *)
+ by move=> b /= [] hty //=.
(* Parr_init *)
+ by move=> p /= [] hty //=.
(* Pgvar *)
+ move=> g ty s er /= [] hte /= he. by have := get_gvar_not_tyerr g ty s er hte he.
(* Pget : a[e] where e is index *)
+ move=> a w g e /=. rewrite /ty_get_set /= /check_array /=.
  t_xrbindP=> hind ty s er te he ta. case hta : (vtype (gv g))=> [ | | p |] //= [] heq; subst.
  move=> ti. rewrite /check_int /check_type. case: ifP=> //= /eqP hte [] hte' hty; subst.
  rewrite /on_arr_var /=.  
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
          have hti := sem_pexpr_well_typed pd sint e s ve he hec. 
          by have := read_sint_not_tyerr s e ve vi p alen a w er hec hic hrc hti hc.
        (* to_int evaluates to error state *)
        move=> [] hveq; subst. have htv := sem_pexpr_well_typed pd sint e s ve he hec. 
        case: ve he hec htv hic=> //= t i he hec hic ht; subst. by case: ht=> [] <-. 
      (* sem_pexpr evaluates to error state *)
      move=> [] hv; subst. by move: (hind sint s er he hec).
    move=> /eqP hlen [] hlen'. by rewrite hlen' in hlen.
 (* get_gvar evaluates to error state *)
  move=> [] hv; subst. by have := get_gvar_not_tyerr g (sarr p) s er hta hgc. 
(* Psub *)
+ move=> aa sz len x e hind /=. rewrite /ty_get_set_sub /check_array /check_int /check_type.
  t_xrbindP=> ty s er te hte tx. case hta: (vtype (gv x))=> [ | | p|] //= [] heq; subst.
  move=> ti. case: ifP=> //= /eqP heq [] heq' hty; subst.
  rewrite /on_arr_var /=.  
  case hgc: get_gvar=> [gv| gerr] //=.
  (* get_gvar evaluates to ok state *)
  + have [/= _ hc]:= get_gvar_compat hgc. rewrite hta in hc. 
    have hgv := compat_val_vm_truncate_val hc; subst. case: gv hgc hc hgv=> //=.
    move=> len' alen hgc hc. case: ifP=> //=.
    + move=> /eqP hl hl' /=; subst. case hec: sem_pexpr=> [ve | eerr] //=.
      (* sem_pexpr evaluates to ok state *)
      + case hic : to_int=> [vi | ierr] //=.
        (* to_int evaluates to ok state *)
        + rewrite /WArray.get_sub /=. by case: ifP=> //= hf [] hv; subst. 
        (* to_int evaluates to error state *)
        move=> [] hveq; subst. have htv := sem_pexpr_well_typed pd sint e s ve hte hec. 
        case: ve hte hec htv hic=> //= t i he hec hic ht; subst. by case: ht=> [] <-. 
      (* sem_pexpr evaluates to error state *)
      move=> [] hv; subst. by move: (hind sint s er hte hec).
    move=> /eqP hlen [] hlen'. by rewrite hlen' in hlen.
 (* get_gvar evaluates to error state *)
  move=> [] hv; subst. by have := get_gvar_not_tyerr x (sarr p) s er hta hgc.
(* Pload : [e] where e is the memory address *)
+ move=> w vi e hind ty s er /=. rewrite /ty_load_store /=. t_xrbindP=> te hte tptr /=. rewrite /check_ptr /check_type.
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
        by have := read_ptr_not_tyerr pd s e ev we vi ptrv ptrv' er w he hte hptr hptr' hr.
      (* to_pointer evaluates to error state *)
      move=> [] hv; subst. have htev := sem_pexpr_well_typed pd (sword we) e s ev hte he. 
      by have := to_pointer_not_tyerr s e ev we er he htev hptr'.
    (* sem_pexpr evaluates to an error state *)
    + move=> [] hv; subst. by move: (hind (sword we) s er hte he).
  (* to_pointer evaluates to an error state *)
  + move=> [] hv; subst. by have := to_pointer_not_tyerr_var s vi ptr er htp hptr. 
(* Papp1 *)
+ move=> op e hind /= ty s er. case hto: type_of_op1=> [tin tout] //=. rewrite /check_expr /check_type /=.
  t_xrbindP=> te to hte. case: ifP=> //= hsub [] ht ht'; subst.
  case he : sem_pexpr=> [ev | eerr] //=.
  + move=> ho. by have := sem_sop1_not_tyerr pd e s tin ty te ev op er hto hsub hte he ho.
  move=> [] hv; subst. by move: (hind te s er hte he).
(* Papp2 *)
+ move=> op e1 hind1 e2 hind2 ty s er /=. rewrite /check_expr /check_type /=.
  t_xrbindP=> te1 te1' hte1. case: ifP=> //= hsub [] ht; subst. move=> te2 te2' hte2.
  case: ifP=> //= hsub' [] ht /= hty. 
  case he2 : sem_pexpr=> [ev2 | eer2] //=.
  (* sem_pexpr of e2 evaluates to ok *)
  + case he1 : sem_pexpr=> [ev1 | eer1] //=.
    (* sem_pexpr of e1 evaluates to ok *)
    + move=> hop. 
      by have := sem_sop2_not_tyerr pd op te1 te2' s e1 ev1 e2 ev2 er hsub hsub' hte1 hte2 he1 he2 hop.
    (* sem_pexpr of e1 evaluates to error *)
    move=> [] hv; subst. by move: (hind1 te1 s er hte1 he1).
  (* sem_pexpr of e2 evaluates to error *)
  case he1 : sem_pexpr=> [ev1 | eer1] //=.
  (* sem_pexpr of e1 evaluates to ok *)
  + move=> [] hv; subst. by move: (hind2 te2 s er hte2 he2).
  (* sem_pexpr of e1 evaluates to error *)
  move=> [] hv; subst. by move: (hind1 te1 s er hte1 he1).
(* PappN *)
+ move=> op es hind /=. elim: es hind=> [ | e es hind'] //=.  
  + move=> /= hind te _ er. case: ((type_of_opN op).1)=> //=.
    move=> [] hte /=; subst. admit.
  move=> hind ty s er /=. case: ((type_of_opN op).1)=> //= te tes.
  rewrite /check_expr /check_type /=. t_xrbindP=> tes1 te1 te1' hte.
  case: ifP=> //= hsub [] heq'; subst. move=> tes1' hes heq hty; subst.
  case he: sem_pexpr=> [ev | err] //=.
  + case hesc : mapM=> [mv | merr] //=.
    + move=> ho. by have := sem_sopN_not_tyerr pd e te1 es tes tes1' ev mv er op s hte hes he hesc ho.
  move=> [] hv; subst. admit.
  move=> [] hv; subst. have heq : e = e \/ List.In e es. + by left. by move: (hind e heq te1 s er hte he).
(* Pif *)
move=> ty e hinde e1 hinde1 e2 hinde2 /=. rewrite /check_expr /check_type /=.
t_xrbindP=> te s er te1 te2 hte. case: ifP=> //= /eqP heq [] heq' te2' te1' hte1; subst.
case: ifP=> //= hsub [] heq' te2 te2'' hte2. case: ifP=> //= hsub' [] heq1 heq''; subst.
case he2: sem_pexpr=> //= [ev2 | eerr2]. have hev2 := sem_pexpr_well_typed pd te2 e2 s ev2 hte2 he2.
(* sem_pexpr of e2 evaluates to ok state *)
+ case he1: sem_pexpr=> //= [ev1 | eerr1]. have hev1 := sem_pexpr_well_typed pd te2' e1 s ev1 hte1 he1. 
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
          move=> [] hv; subst. by have := truncate_val_not_tyerr te ev1 er hsub ht1.
        (* truncate_val of ev2 evaluates to error state *)
        move=> ht1. rewrite -hev2 in hsub'. have her := truncate_val_not_tyerr te ev2 terr hsub' ht2.
        rewrite -hev1 in hsub. move: ht1. case ht1: truncate_val=> [tv1 | terr1] //=.
        + by move=> [] hv; subst.
        move=> [] hv; subst. by have := truncate_val_not_tyerr te ev1 er hsub ht1.
     (* to_bool evaluates to error state *)
     move=> [] hv; subst. by have := to_bool_not_tyerr ev er hev hb.  
    (* sem_pexpr of e evaluates to error state *)
    move=> [] hv; subst. by move: (hinde sbool s er hte he).
  (* sem_pexpr of e1 evaluates to error state *)
  case he : sem_pexpr=> [ev | eerr] //=.
  (* sem_pexpr of e evaluates to ok state *)
  + have htev := sem_pexpr_well_typed pd sbool e s ev hte he. case: ev he htev=> //=.
    + move=> b he _ [] hv; subst. by move: (hinde1 te2' s er hte1 he1).
    move=> t ht he hteq /=; subst. rewrite /undef_error /=. by move=> [] hv; subst.
  (* sem_pexpr of e evaluates to error state *)
  move=> [] hv; subst. by move: (hinde sbool s er hte he).
(* sem_pexpr of e2 evaluates to error state *)
case he1 : sem_pexpr=> [ev1| eerr1] //=.
(* sem_pexpr of e1 evaluates to ok state *)
+ case he : sem_pexpr=> [ev| eerr] //=.
  (* sem_pexpr of e evaluates to ok state *)
  + case hb : to_bool=> [bv | ber] //=.
    (* to_bool evaluates to ok state *)
    + case ht : truncate_val=> [tv | ter] //=.
      (* truncate_val of ev1 evaluates to ok *)
      + move=> [] hv; subst. by move: (hinde2 te2 s er hte2 he2).
      (* truncate_val of ev1 evaluates to error *)
      move=> [] hv; subst. have hev1 := sem_pexpr_well_typed pd te2' e1 s ev1 hte1 he1. 
      rewrite -hev1 in hsub. by have := truncate_val_not_tyerr te ev1 er hsub ht.
    (* to_bool evaluates to error state *)
    move=> [] hv; subst. have hev := sem_pexpr_well_typed pd sbool e s ev hte he.
    by have := to_bool_not_tyerr ev er hev hb.
  (* sem_pexpr of e evaluates to error state *)
  move=> [] hv; subst. by move: (hinde sbool s er hte he).
(* sem_pexpr of e1 evaluates to error state *)
case he : sem_pexpr=> [ev | eerr] //=.
(* sem_pexpr of e evaluates to ok state *)
+ case hb : to_bool=> [bv | ber] //=.
  (* to_bool evaluates to ok state *)
  + move=> [] hv; subst. by move: (hinde1 te2' s er hte1 he1).
  (* to_bool evaluates to error state *)
  move=> [] hv; subst. have hev := sem_pexpr_well_typed pd sbool e s ev hte he.
  by have := to_bool_not_tyerr ev er hev hb.
(* sem_pexpr of e evaluates to error state *)
move=> [] hv; subst. by move: (hinde sbool s er hte he).
Admitted. 

End TYPING_PEXPR.
