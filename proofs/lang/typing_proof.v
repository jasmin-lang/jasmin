From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Export array type expr gen_map low_memory warray_ sem_type sem_op_typed values psem_defs
typing psem.
Require Export
  flag_combination
  sem_params.

Section TYPING_PEXPR.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {wsw : WithSubWord}
  (wdb : bool)
  (gd : glob_decls).

Lemma type_of_get_gvar_eq vm x v :
get_gvar (wsw:= nosubword) false gd vm x = ok v ->
type_of_val v = vtype x.(gv).
Proof.
move=> hg. have /= [_ hc ]:= get_gvar_compat hg.
have := compat_valE hc. case hv: v hg hc=> [ | | | sz wsz | ui i] //=; subst.
+ move=> hg hc [] sz' hvt hsz; subst. by rewrite hvt.
move=> hg _ hsub. rewrite /get_gvar in hg. move: hg.
case: ifP=> //= hl.
(* get_var is undef *)
+ move=> hg. have [hu _ _] /=:= get_varP hg.
  case hui: ui i hg hsub hu => [ | | w | w'] //=.
  (* undef of bool *)
  + by move=> i hvm /eqP.
  (* undef of int *)
  + by move=> i hvm /eqP.
  (* undef of word *)
  case ht: (vtype (gv x))=> [ | | w1 | w'']//=.
  move=> i hg hsz hv. 
  case: w' hui i hg hv hsz=> [ hui i| hui i| hui i| hui i| hui i|].
  (* u8 *)
  + move=> hg hv hsz. case: w'' hsz ht.
    + move=> //=.
    + move=> //. admit.
    + move=> //=. admit.
    + move=> //. admit.
    + move=> //. admit.
    admit.
  (* u16 *) (* not correct: there is somewhere bug *)
  + move=> hg hv hsz. case: w'' hsz ht.
    + by move=> //. (* correct *) (* U16 <= U8 in the assumption *)
    + by move=> hsz ht. (* correct *) 
      (* U16 <= U16 in assumption and we need to prove sword16 = sword16 *)
    + by move=> hsz ht. (* not correct *)
      (* U16 <= U32 in assumption and we need to prove sword16 = sword32 *)
    + by move=> hsz ht. (* not correct *)
      (* U16 <= U64 in assumption and we need to prove sword16 = sword64 *)
    + by move=> hsz ht. (* not correct *)
      (* U16 <= U128 in assumption and we need to prove sword16 = sword128 *)
    by move=> hsz ht. (* not correct *)
    (* U16 <= U256 in assumption and we need to prove sword16 = sword256 *)
  (* u32 *) (* not correct: there is somewhere bug *)
  + move=> hg hv hsz. case: w'' hsz ht.
    + by move=> //. (* correct *) (* U32 <= U8 in the assumption *)
    + by move=> hsz ht. (* correct *) (* U32 <= U16 in assumption *)
    + by move=> hsz ht. (* correct *) (* U32 <= U32 in assumption *)
    + by move=> hsz ht. (* not correct *)
      (* U32 <= U64 in assumption and we need to prove sword32 = sword64 *)
    + by move=> hsz ht. (* not correct *)
      (* U32 <= U128 in assumption and we need to prove sword32 = sword128 *)
    by move=> hsz ht. (* not correct *)
    (* U32 <= U256 in assumption and we need to prove sword32 = sword256 *)
  (* u64 *) (* not correct: there is somewhere bug *)
  + move=> hg hv hsz. case: w'' hsz ht.
    + by move=> //. (* correct *) (* U64 <= U8 in the assumption *)
    + by move=> hsz ht. (* correct *) (* U64 <= U16 in assumption *)
    + by move=> hsz ht. (* correct *) (* U64 <= U32 in assumption *)
    + by move=> hsz ht. (* correct *) (* U64 <= U64 in assumption *)
    + by move=> hsz ht. (* not correct *)
      (* U64 <= U128 in assumption and we need to prove sword64 = sword128 *)
    by move=> hsz ht. (* not correct *)
    (* U64 <= U256 in assumption and we need to prove sword64 = sword256 *)
  (* u128 *) (* not correct: there is somewhere bug *)
  + move=> hg hv hsz. case: w'' hsz ht.
    + by move=> //. (* correct *) (* U128 <= U8 in the assumption *)
    + by move=> hsz ht. (* correct *) (* U128 <= U16 in assumption *)
    + by move=> hsz ht. (* correct *) (* U128 <= U32 in assumption *)
    + by move=> hsz ht. (* correct *) (* U128 <= U64 in assumption *)
    + by move=> hsz ht. (* correct *) (* U128 <= U128 in assumption *)
    by move=> hsz ht. (* not correct *)
    (* U128 <= U256 in assumption and we need to prove sword128 = sword256 *)
  (* u256 *)
  move=> hui hu hg. case: w'' ht.
  + by move=> ht hv hsz. (* correct *)
  + by move=> ht hv hsz. (* correct *)
  + by move=> ht hv hsz. (* correct *)
  + by move=> ht hv hsz. (* correct *)
  + by move=> ht hv hsz. (* correct *)
  by move=> ht hv hsz. (* correct *)
move=> hg. case hui: ui i hg hsub=> [ | | w | w'] //=.
+ by move=> i hg /eqP.
+ by move=> i hg /eqP.
move=> i hg. rewrite /get_global in hg. 
case hgv: (get_global_value gd (gv x)) hg=> [ a | ] //=.
case: ifP=> //= /eqP ht [] hv; subst. rewrite hv in ht.
rewrite /type_of_val /= in ht. by rewrite -ht /=. 
Admitted.

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
+ rewrite /ty_pexpr /sem_pexpr. move=> g [] <- hg. 
  by have := type_of_get_gvar_eq (evm s) g v hg.
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
+ move=> o es /=. case hc: check_pexprs=> [vc | vcr] //= [] hts; subst.
  case hm: mapM=> [vm | vmr] //= ho.
  rewrite /sem_opN in ho. move: ho.
  case ha: app_sopn=> [va | var] //= [] heq; subst.
  apply type_of_to_val.
(* Pif *)
move=> sty b e1 e2 /=. rewrite /check_expr /= /check_type /=. 
t_xrbindP=> bty bty' htb. case: ifP=> //= /eqP heq; subst. move=> [] heq'; subst.
move=> e1t e1t' hte1. case: ifP=> //= hsub [] heq; subst. move=> e2t e2t' hte2.
case: ifP=> //= hsub' [] heq; subst. move=> hteq; subst. move=> bv bv' hb hbt e1v e1v' he1 ht e2v e2v' he2 ht' <-.
case: ifP=> //= _. by have := truncate_val_has_type ht. by have := truncate_val_has_type ht'.
Qed.

Lemma get_global_value_ty : forall g a,
is_lvar g = false ->
get_global_value gd (gv g) = Some a ->
type_of_val (gv2val a) == vtype (gv g).
Proof.
move=> g a hl. 
Admitted.

Lemma get_gvar_not_tyerr : forall g ty s v,
vtype (gv g) = ty ->
get_gvar (wsw := nosubword) false gd (evm s) g = Error v ->
v <> ErrType.
Proof.
move=> g ty s v ht. rewrite /get_gvar. case: ifP=> //= hl.
rewrite /get_global /= ht /=. Print get_global. case hv: (get_global_value gd (gv g))=> [ va | ] //=.
+ case: ifP=> //= /eqP ht' [] heq; subst. by have /eqP ht'':= get_global_value_ty g va hl hv.
move=> [] hv'; subst. (* We should not return type error here *)
admit.
Admitted.

Lemma truncate_val_not_tyerr : forall ty v v',
subtype ty (type_of_val v) ->
truncate_val ty v = Error v' ->
v' <> ErrType.
Proof.
move=> ty v v' hsub ht. case: v hsub ht=> //=.
+ move=> b hsub ht. have hty := subtypeE hsub; subst. by rewrite /truncate_val /= in ht.
+ move=> z hsub ht. have hty := subtypeE hsub; subst. by rewrite /truncate_val /= in ht.
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
case: i ht hi=> //= t ht hi; subst. case: hi=> hi'; subst. 
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

Lemma of_val_not_tyerr : forall pd s e t t' v err, 
ty_pexpr pd e = ok t ->
subtype t' t ->
sem_pexpr (wsw:= nosubword) false gd s e = ok v ->
of_val t' v = Error err ->
err <> ErrType.
Proof.
move=> pd s e t t' ev err ht hsub he. 
have hvt := sem_pexpr_well_typed pd t e s ev ht he.
rewrite /of_val. case: t' hsub=> //=.
+ move=> /eqP heq. rewrite -heq in hvt. 
  by have := to_bool_not_tyerr ev err hvt.
+ move=> /eqP heq. rewrite -heq in hvt. 
  by have := to_int_not_tyerr ev err hvt.
+ move=> p /eqP heq. rewrite -heq in hvt. 
  by have := to_arr_not_tyerr ev p err hvt.
move=> w. case: t ht hvt=> //= w' ht hvt hsz.
by have := to_word_not_tyerr w' w ev err hsz hvt.
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
move=> pd op t1 t2 s e1 ev1 e2 ev2 err hsub1 hsub2 ht1 ht2 he1 he2.
rewrite /sem_sop2 /=. case hvo : of_val=> [vo | vor] //=.
+ case hvo': of_val=> [vo' | vor'] //=.
  + case hso : sem_sop2_typed=> [so | sor] //=. 
    case: op hsub1 hsub2 vo hvo vo' hvo' hso ht1=> //= ok.
    + by case: ok=> //=.
    + by case: ok=> //=.
    + by case: ok=> //=.
    + case: ok=> //= sg sz. case: t1=> //= sz' hsz. 
      case: t2 ht2=> //= sz'' ht2 hsz' vo hw vo' hw'. rewrite /mk_sem_divmod /=.
      case: ifP=> //=. by move=> _ [] heq _ [] heq'; subst.
    + case: ok=> //= sg sz. case: t1=> //= sz' hsz. 
      case: t2 ht2=> //= sz'' ht2 hsz' vo hw vo' hw'. rewrite /mk_sem_divmod /=.
      case: ifP=> //=. by move=> _ [] heq _ [] heq'; subst.
    + by case: ok=> //=. 
    + by case: ok=> //=.
    + by case: ok=> //=.
    + by case: ok=> //=.
    + by case: ok=> //=.
    + by case: ok=> //=.
    + by case: ok=> //=.
    by case: ok=> //=.
  move=> [] heq; subst. 
  by have := of_val_not_tyerr pd s e1 t1 (type_of_op2 op).1.1 ev1 err ht1 hsub1 he1 hvo'.
case hvo' : of_val=> [vo' | vor'] //=.
+ move=> [] heq; subst. 
  by have := of_val_not_tyerr pd s e2 t2 (type_of_op2 op).1.2 ev2 err ht2 hsub2 he2 hvo.
move=> [] heq; subst. 
by have := of_val_not_tyerr pd s e1 t1 (type_of_op2 op).1.1 ev1 err ht1 hsub1 he1 hvo'.
Qed.

Lemma array_get8_not_tyerr: forall p (alen:WArray.array p) (i: Z) err, 
WArray.get8 alen i = Error err ->
err <> ErrType.
Proof.
move=> p alen i err. rewrite /WArray.get8 /=.
case ha1: assert=> [va1 | var1] //=.
+ case ha2: assert=> [va2 | var2] //= [] <-.
  rewrite /assert in ha2. move: ha2. by case: ifP=> //= ha2 [] <-.
case ha3: assert=> [va3 | var3] //= [] <-.
+ rewrite /assert in ha1. move: ha1. by case: ifP=> //= ha1 [] <-.
rewrite /assert in ha3. move: ha3. by case: ifP=> //= ha3 [] <-.
Qed.


Lemma read_sint_not_tyerr : forall pd s e ve vi p (alen:WArray.array p) a w er,
ty_pexpr pd e = ok sint ->
sem_pexpr (wsw := nosubword) false gd s e = ok ve ->
to_int ve = ok vi ->
read alen (vi * mk_scale a w)%Z w = Error er ->
er <> ErrType.
Proof.
move=> pd s e ve vi p alen a w er hte he hi hr.
have hvt := sem_pexpr_well_typed pd sint e s ve hte he.
rewrite readE in hr. move: hr. 
case hm: mapM=> [vm | vmr] //.
+ case ha: assert=> [va | vr] //= [] heq; subst. 
  rewrite /assert in ha. move: ha. by case: ifP=> //= ha [] <-.
case ha: assert=> [va | vr] //= [] heq; subst.
+ move: hm. move: er. elim: (ziota 0 (wsize_size w))=> [ | n ns] //= hin.
  case hr: read=> [vr | vrr] //= er.
  + case hm': mapM=> [vm | vmr] //= [] <-. by move: (hin vmr hm').
    move=> [] <-. move: hr. rewrite /read !ziotaE /=. case ha': assert=> [va' | var'] //=. 
    + case hwr: WArray.get8=> [wv | wvr] //= [] <-.
    by have := array_get8_not_tyerr p alen (add (add (vi * mk_scale a w)%Z n) 0)%Z wvr hwr.
  move=> [] <-. rewrite /assert in ha'. move: ha'. by case: ifP=> //= ha' [] <-.
rewrite /assert in ha. move: ha. by case: ifP=> //= ha [] <-.
Qed.

Lemma read_ptr_not_tyerr: forall pd s e ev we vi ptrv ptrv' er w,
sem_pexpr (wsw := nosubword) false gd s e = ok ev ->
ty_pexpr pd e = ok (sword we) ->
to_pointer (evm s).[vi] = ok ptrv ->
to_pointer ev = ok ptrv' ->
read (emem s) (ptrv + ptrv')%R w = Error er ->
er <> ErrType.
Proof.
move=> pd s e ev we vi ptrv ptrv' er w he hte hp hp' hr.
have hvt := sem_pexpr_well_typed pd (sword we) e s ev hte he.
rewrite /read in hr. move: hr. case hm: mapM=> [vm | vmr] //=.
+ case ha: assert=> [va | vr] //= [] heq; subst. 
  rewrite /assert in ha. move: ha. by case: ifP=> //= ha [] <-.
case ha: assert=> [va | vr] //= [] heq; subst.
+ move: hm. move: er. elim: (ziota 0 (wsize_size w))=> [ | n ns] //= hin.
  case hr: get=> [vr | vrr] //= er.
  + case hm': mapM=> [vm | vmr] //= [] <-. by move: (hin vmr hm').
  move=> [] <-. move: hr. rewrite addE. admit. 
rewrite /assert in ha. move: ha. by case: ifP=> //= ha [] <-.
Admitted.

Lemma to_pointer_not_tyerr : forall pd (s:@estate nosubword syscall_state ep) e ev we er,
ty_pexpr pd e = ok (sword we) ->
sem_pexpr (wsw := nosubword) false gd s e = ok ev ->
(pd ≤ we)%CMP ->
to_pointer ev = Error er ->
er <> ErrType.
Proof.
move=> pd s e ev we er ht he hp.
have hvt := sem_pexpr_well_typed pd (sword we) e s ev ht he.
case hv: ev he ht hp hvt=> [ | | | w ws | u i]//=.
+ move=> he hte hsub [] heq htr; subst.
  have [ht ht'] := truncate_word_errP htr. move=> h; subst.
  have ht'' := cmp_le_lt_trans hsub ht'. 
  admit.
move=> he ht hsub heq; subst. by move=> [] <-.
Admitted.

Lemma to_pointer_not_tyerr_var : 
forall (s : @estate nosubword syscall_state ep) vi ptr er,
vtype vi = sword ptr -> 
to_pointer (evm s).[vi] = Error er ->
er <> ErrType.
Proof.
move=> s vi ptr er hty hptr. have hc := Vm.getP (evm s) vi.
rewrite /to_pointer /= in hptr. 
case: ((evm s).[vi]) hc hptr=> [ b| z| len arr | ws w| undef i] //=.
+ move=> hc [] hv; subst. rewrite hty /= in hc. 
  by have := compat_valE hc.
+ move=> hc [] hv; subst. rewrite hty /= in hc. 
  by have := compat_valE hc.
+ move=> hc [] hv; subst. rewrite hty /= in hc. 
  by have := compat_valE hc.
+ rewrite /compat_val /=. move=> /eqP hty'.
  case: truncate_wordP'=> //= hws [] h; subst. 
  rewrite hty in hty'. case: hty'=> hty''; subst.
  admit. (* truncate_word should return some kind of arithmetic error *)
move=> hc. case: undef i hc=> //=; subst.
+ move=> i hc [] heq; subst. rewrite hty /= in hc. 
  by have := compat_valE hc.
+ move=> i hc [] heq; subst. rewrite hty /= in hc. 
  by have := compat_valE hc.
by move=> w i hc [] heq; subst.
Admitted.

Theorem sem_sopn_type_error: forall pd ty (s:@estate nosubword syscall_state ep) es op er,
ty_pexpr pd (PappN op es) = ok ty ->
sem_pexpr false gd s (PappN op es) = Error er -> 
er <> ErrType.
Proof.
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
          by have := read_sint_not_tyerr pd s e ve vi p alen a w er he hec hic hrc.
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
      by have := to_pointer_not_tyerr pd s e ev we er hte he hsz' hptr'.
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
+ move=> op es hind ty s er ht he. 
  by have:= sem_sopn_type_error pd ty s es op er ht he.
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
Qed. 

End TYPING_PEXPR.

(*Compute xH. (* 1 *)

Compute (xO xH). (* 10 *)

Compute (xI xH). (* 11 *)

Compute (xO (xO xH)). (* 100*)*)
