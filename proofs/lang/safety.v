From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import psem_defs typing.

(* Sequence of safety condition for an expression to execute to an ok state apart from type error 
Definition safety_cond := seq bool.*)

Section Safety_conditions.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {wsw : WithSubWord}
  (wdb : bool)
  (gd : glob_decls).

Inductive safe_sop2 : sop2 -> Prop := 
| Soadd sz:
   (sz ≤ U64)%CMP ->
   (forall v w t, v <> (Vundef (sword w) t)) -> 
   safe_sop2 (Oadd (Op_w sz))
| Somul sz:
   ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
   (forall v w t, v <> (Vundef (sword w) t)) -> 
   safe_sop2 (Omul (Op_w sz))
| Sosub sz:
   (sz ≤ U64)%CMP ->
   (forall v w t, v <> (Vundef (sword w) t)) -> 
   safe_sop2 (Osub (Op_w sz))
(* Property not used because in x86 semantics of DIV it returns type error and 
   at high-level it uses Z.Div *)
| Sodiv:
   (forall v t, v <> (Vundef sint t)) ->
   (forall v1 v2 sz w r wr, 
    of_val (type_of_op2 (Odiv Cmp_int)).1.2 v2 = ok w ->
    (w <> 0%R) ->
    sem_sop2 (Odiv Cmp_int) v1 v2 = ok r ->
    ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
    to_word sz r = ok wr ->
    (wunsigned wr <=? wmax_unsigned sz)%Z) -> 
   safe_sop2 (Odiv Cmp_int)
| Sodivs u sz: 
   (forall v w t, v <> (Vundef (sword w) t)) -> 
   ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
   (forall v1 v2 w w1, 
    of_val (type_of_op2 (Odiv (Cmp_w u sz))).1.2 v2 = ok w ->
    to_word sz v1 = ok w1 ->
    not ((w == 0%R) || (wsigned w1 == wmin_signed sz) && (w == (-1)%R))) ->
   safe_sop2 (Odiv (Cmp_w u sz))
| Somod:
   (forall v t, v <> (Vundef sint t)) ->
   (forall v1 v2 sz w r wr, 
    of_val (type_of_op2 (Odiv Cmp_int)).1.2 v2 = ok w ->
    (w <> 0%R) ->
    sem_sop2 (Odiv Cmp_int) v1 v2 = ok r ->
    ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
    to_word sz r = ok wr ->
    (wunsigned wr <=? wmax_unsigned sz)%Z) -> 
   safe_sop2 (Omod Cmp_int)
| Somods u sz:
   (forall v w t, v <> (Vundef (sword w) t)) -> 
   ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
   (forall v1 v2 w w1, 
    of_val (type_of_op2 (Odiv (Cmp_w u sz))).1.2 v2 = ok w ->
    to_word sz v1 = ok w1 ->
    not ((w == 0%R) || (wsigned w1 == wmin_signed sz) && (w == (-1)%R))) ->
   safe_sop2 (Omod (Cmp_w u sz))
(* Fix me *)
| Soland sz:
   safe_sop2 (Oland sz)
| Solor sz:
   (sz ≤ U64)%CMP || ((U128 ≤ sz) && (sz ≤ U256))%CMP ->
   safe_sop2 (Olor sz)
| Solxor sz:
   (sz ≤ U64)%CMP || ((U128 ≤ sz) && (sz ≤ U256))%CMP ->
   safe_sop2 (Olxor sz)
| Solsr sz:
   (sz ≤ U64)%CMP ->
   safe_sop2 (Olsr sz)
| Solsl sz:
   (sz ≤ U64)%CMP ->
   safe_sop2 (Olsl (Op_w sz))
| Soasr sz:
   (sz ≤ U64)%CMP ->
   safe_sop2 (Oasr (Op_w sz))
| Soror sz:
   (sz ≤ U64)%CMP ->
   safe_sop2 (Oror sz)
| Sorol sz:
   (sz ≤ U64)%CMP ->
   safe_sop2 (Orol sz)
| Svadd ve sz:
   ((U128 ≤ sz) && (sz ≤ U256))%CMP ->
   safe_sop2 (Ovadd ve sz)
| Svsub ve sz:
   ((U128 ≤ sz) && (sz ≤ U256))%CMP ->
   safe_sop2 (Ovsub ve sz)
| Svmul ve sz:
   ((U16 ≤ sz) && (sz ≤ U32))%CMP ->
   safe_sop2 (Ovmul ve sz)
| Svlsr ve sz:
   ((U128 ≤ sz) && (sz ≤ U256))%CMP ->
   safe_sop2 (Ovlsr ve sz)
| Svlsl ve sz:
   ((U128 ≤ sz) && (sz ≤ U256))%CMP ->
   safe_sop2 (Ovlsl ve sz)
| Svasr ve sz:
   ((U128 ≤ sz) && (sz ≤ U256))%CMP ->
   safe_sop2 (Ovasr ve sz).

Inductive safe_sop1 : sop1 -> Prop := 
| Soword_of_int sz:
   (forall v t, v <> (Vundef sint t)) ->
   safe_sop1 (Oword_of_int sz)
| Soint_of_word sz:
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Oint_of_word sz)
| SosignextU8 szi szo:
   szi = U8 ->
   ((U16 ≤ szo) && (szo ≤ U64))%CMP -> 
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Osignext szo szi)
| SosignextU16 szi szo:
   szi = U16 ->
   ((U16 ≤ szo) && (szo ≤ U64))%CMP -> 
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Osignext szo szi)
| SosignextU32 szi szo:
   szi = U32 ->
   ((U32 ≤ szo) && (szo ≤ U64))%CMP -> 
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Osignext szo szi)
| SozeroextU8 szi szo:
   szi = U8 ->
   ((U16 ≤ szo) && (szo ≤ U64))%CMP -> 
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Ozeroext szo szi)
| SozeroextU16 szi szo:
   szi = U16 ->
   ((U32 ≤ szo) && (szo ≤ U64))%CMP -> 
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Ozeroext szo szi)
(* Fix me *)
| SozeroextU3264 szi szo:
   szi = U32 ->
   szo = U64 ->
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Ozeroext szo szi)
| SozeroextU32128 szi szo:
   szi = U32 ->
   szo = U128 ->
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Ozeroext szo szi)
| SozeroextU32256 szi szo:
   szi = U32 ->
   szo = U256 ->
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Ozeroext szo szi)
| SozeroextU64128 szi szo:
   szi = U64 ->
   szo = U128 ->
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Ozeroext szo szi)
| SozeroextU64256 szi szo:
   szi = U64 ->
   szo = U256 ->
   (forall v w t, v <> (Vundef (sword w) t)) ->
   safe_sop1 (Ozeroext szo szi)
| Sonot:
  (forall v t, v <> (Vundef sbool t)) ->
  safe_sop1 Onot
| Solnot sz:
  (forall v w t, v <> (Vundef (sword w) t)) ->
  ((U8 ≤ sz) && (sz ≤ U64))%CMP -> 
  safe_sop1 (Olnot sz)
| Soneg sz:
  (forall v w t, v <> (Vundef (sword w) t)) ->
  ((U8 ≤ sz) && (sz ≤ U64))%CMP -> 
  safe_sop1 (Oneg (Op_w sz)).

Inductive safe_get_var : @estate nosubword syscall_state ep -> gvar -> Prop := 
| SLvar s v:
   is_lvar v ->
   ~~ wdb || is_defined (evm s).[gv v] ->
   safe_get_var s v
| Sglobal s v a:
   not (is_lvar v) ->
   get_global_value gd (gv v) = Some a ->
   type_of_val (gv2val a) == vtype (gv v) ->
   safe_get_var s v.   

Inductive safe_expr : @estate nosubword syscall_state ep -> pexpr -> Prop :=
| Sconst s z :
   safe_expr s (Pconst z)
| Sbool s b :
   safe_expr s (Pbool b)
| Sarr_init s n :
   safe_expr s (Parr_init n)
| Svar s v :
   safe_get_var s v ->
   safe_expr s (Pvar v)
(* pos will be array size *)
| Sget s aa ws x e i pos:
   safe_get_var s x ->
   safe_expr s e ->
   sem_pexpr false gd s e = ok (Vint i) ->
   is_align (i * mk_scale aa ws)%Z ws ->
   WArray.in_range pos (i * mk_scale aa ws)%Z ws ->
   safe_expr s (Pget aa ws x e)
(* pos will be obtained from vm *)
| Ssub s aa ws len x e i:
   safe_get_var s x ->
   safe_expr s e ->
   sem_pexpr false gd s e = ok (Vint i) ->
   (forall pos, (0 <=? (i * mk_scale aa ws))%Z && 
    ((i * mk_scale aa ws + arr_size ws len) <=? pos)%Z) ->
   safe_expr s (Psub aa ws len x e)
| Sload s ws x e vx t i w1 w2:
   (~~ wdb || is_defined (evm s).[v_var x]) ->
   get_var wdb s.(evm) x = ok vx ->
   vx <>  Vundef (sword ws) t ->
   safe_expr s e ->
   sem_pexpr false gd s e = ok (Vint i) ->
   to_pointer vx = ok w1 ->
   to_pointer i = ok w2 ->
   validw (emem s) (w1 + w2)%R ws ->
   safe_expr s (Pload ws x e)
| Sapp1 s o e:
   safe_expr s e ->
   (*sem_pexpr s e = ok v ->
   v <> Vundef ->*)
   safe_sop1 o ->
   safe_expr s (Papp1 o e)
| Sapp2 s o e1 e2:
   safe_expr s e1 ->
   safe_expr s e2 ->
   safe_sop2 o ->
   safe_expr s (Papp2 o e1 e2)
| SappN s o es:
   safe_exprs s es ->
   safe_expr s (PappN o es)
| Sif s ty b et ef vt vf vb:
   safe_expr s b ->
   safe_expr s et ->
   safe_expr s ef ->
   sem_pexpr false gd s b = ok vb ->
   sem_pexpr false gd s et = ok vt ->
   sem_pexpr false gd s ef = ok vf ->
   ((forall t, (vb <> (Vundef sint t))) 
    /\ (forall t, (vb <> (Vundef sbool t))) /\ 
    (forall w t, (vb <> (Vundef (sword w) t)))) ->
   ((forall t, (vt <> (Vundef sint t))) 
    /\ (forall t, (vt <> (Vundef sbool t))) /\ 
    (forall w t, (vt <> (Vundef (sword w) t)))) ->
   ((forall t, (vf <> (Vundef sint t))) 
    /\ (forall t, (vf <> (Vundef sbool t))) /\ 
    (forall w t, (vf <> (Vundef (sword w) t)))) ->
   safe_expr s (Pif ty b et ef) 

with safe_exprs : @estate nosubword syscall_state ep -> pexprs -> Prop :=
| Sempty s: 
   safe_exprs s [::]
| Sseq s s' e es:
   safe_expr s e ->
   safe_exprs s' es ->
   safe_exprs s (e :: es).

Lemma to_word_not_undef : forall s e ve er sz,
sem_pexpr (wsw := nosubword) false gd s e = ok ve ->
(forall w t, ve <> Vundef (sword w) t) ->
to_word sz ve = Error er ->
er = ErrType.
Proof.
move=> s e ve er sz. case: ve=> //=.
+ rewrite /type_error. by move=> b he hb [] <-. 
+ rewrite /type_error. by move=> z he hb [] <-.
+ rewrite /type_error. by move=> len a he hb [] <-.
+ rewrite /type_error. move=> sw wo he hb ht.
  by have [-> h2]:= truncate_word_errP ht.
move=> ti i he hb. case: ti i he hb=> //=.
+ rewrite /type_error. by move=> i he hi [] <-.
+ rewrite /type_error. by move=> i he hi [] <-.
move=> ws i he ht. by move: (ht  ws i)=> //=. 
Qed.

Lemma to_int_not_undef : forall s e ve er,
sem_pexpr (wsw := nosubword) false gd s e = ok ve ->
(forall t, ve <> Vundef sint t) ->
to_int ve = Error er ->
er = ErrType.
Proof.
move=> s e ve er. case: ve=> //=.
+ rewrite /type_error. by move=> b he hb [] <-. 
+ rewrite /type_error. by move=> len a he hb [] <-.
+ rewrite /type_error. by move=> sw wo he hb [] <-.
move=> ti i he hb. case: ti i he hb=> //=.
+ rewrite /type_error. by move=> i he hi [] <-.
+ move=> i he ht _. by move: (ht i)=> //=.
rewrite /type_error. by move=> ws i he ht [] <-. 
Qed.

Lemma to_bool_not_undef : forall s e ve er,
sem_pexpr (wsw := nosubword) false gd s e = ok ve ->
(forall t, ve <> Vundef sbool t) ->
to_bool ve = Error er ->
er = ErrType.
Proof.
move=> s e ve er. case: ve=> //=.
+ rewrite /type_error. by move=> b he hb [] <-. 
+ rewrite /type_error. by move=> len a he hb [] <-.
+ rewrite /type_error. by move=> sw wo he hb [] <-.
move=> ti i he hb. case: ti i he hb=> //=.
+ move=> i he ht _. by move: (ht i)=> //=.
+ rewrite /type_error. by move=> i he hi [] <-.
rewrite /type_error. by move=> ws i he ht [] <-. 
Qed.

Lemma of_val_not_undef : forall s e ve ty er,
sem_pexpr (wsw := nosubword) false gd s e = ok ve ->
(forall ty t, ve <> Vundef ty t) ->
of_val ty ve = Error er ->
er = ErrType.
Proof.
move=> s e ve ty er. rewrite /of_val /=. case: ve=> //=.
+ move=> b he ht /=. case: ty=> //=.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> p [] <-.
  rewrite /type_error. by move=> w [] <-.
+ move=> z he ht /=. case: ty=> //=.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> p [] <-.
  rewrite /type_error. by move=> w [] <-.
+ move=> len a he ht /=. case: ty=> //=.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /WArray.cast /=. move=> p. case: ifP=> //= /eqP _. 
    rewrite /type_error. by move=> [] <-.
  rewrite /type_error. by move=> w [] <-.
+ move=> w b he ht /=. case: ty=> //=.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> p [] <-.
  move=> ws ht'. by have [-> h2]:= truncate_word_errP ht'.
move=> t i he ht /=. case: ty=> //=.
+ case: t i he ht=> //=.
  + move=> i he ht _. move: (ht sbool i)=> //=.
  + rewrite /type_error. by move=> i he ht [] <-.
  move=> w i he ht _. by move: (ht (sword w) i)=> //=.
+ case: t i he ht=> //=.
  + move=> i he ht _. move: (ht sbool i)=> //=.
  + move=> i he ht _. move: (ht sint i)=> //=.
  + rewrite /type_error. by move=> w i he ht [] <-.
  rewrite /type_error. by move=> p [] <-.
case: t i he ht=> //=.
+ move=> i he ht w _. move: (ht sbool i)=> //=.
+ move=> i he ht w _. move: (ht sint i)=> //=.
move=> w i he ht w' _. by move: (ht (sword w) i)=> //=.
Qed.

Lemma sem_sop1_safe : forall s op e ve r,
safe_sop1 op ->
sem_pexpr (wsw:= nosubword) false gd s e = ok ve ->
sem_sop1 op ve = r -> 
is_ok r \/ r = Error ErrType.
Proof.
move=> s op e ve r hs he /=; rewrite /sem_sop1 /=; inversion hs; subst; rewrite /=.
(* Oword_of_int *)
+ case hi: to_int=> [vi | vr] //=.
  (* to_int reaches an ok state *)
  + move=> hr; subst. by left.
  (* to_int reaches an error state *)
  move: (H ve)=> {H} H.
  have <- := to_int_not_undef s e ve vr he H hi. move=> <-. by right.
(* Oint_of_word *)
+ case hw: to_word=> [vw | vr] //=.
  (* to_word reaches an ok state *)
  + move=> hr; subst. by left.
  (* to_word reaches an error state *)
  move: (H ve)=> {H} H.
  have <- := to_word_not_undef s e ve vr sz he H hw. move=> <-. by right.
(* Osignext *)
+ case hw: to_word=> [vw | vr] //=.
  (* to_word reaches an ok state *)
  + move=> hr; subst. by left.
  (* to_word reaches an error state *)
  move: (H1 ve)=> {H1} H1.
  have <- := to_word_not_undef s e ve vr U8 he H1 hw. move=> <-. by right. 
   (* U16 signext *)
  + case hw: to_word=> [vw | vr] //=.
    (* to_word reaches an ok state *)
    + move=> hr; subst. by left.
    (* to_word reaches an error state *)
    move: (H1 ve)=> {H1} H1.
    have <- := to_word_not_undef s e ve vr U16 he H1 hw. move=> <-. by right.
  (* U32 signext *)
  case hw: to_word=> [vw | vr] //=.
  (* to_word reaches an ok state *)
  + move=> hr; subst. by left.
  (* to_word reaches an error state *)
  move: (H1 ve)=> {H1} H1.
  have <- := to_word_not_undef s e ve vr U32 he H1 hw. move=> <-. by right.
(* Zeroext *)
+ case hw: to_word=> [vw | vr] //=.
  (* to_word evaluates to ok state *)
  + move=> hr; subst. by left.
  (* to_word evaluates to error state *)
  move: (H1 ve)=> {H1} H1.
  have <- := to_word_not_undef s e ve vr U8 he H1 hw. move=> <-. by right.
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move: (H1 ve)=> {H1} H1.
  have <- := to_word_not_undef s e ve vr U16 he H1 hw. move=> <-. by right.
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move=> hr; subst. move: (H1 ve)=> {H1} H1. 
    have <- := to_word_not_undef s e ve vr U32 he H1 hw. by right.
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move: (H1 ve)=> {H1} H1.
    have <- := to_word_not_undef s e ve vr U32 he H1 hw. move=> <-. by right.
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move: (H1 ve)=> {H1} H1.
    have <- := to_word_not_undef s e ve vr U32 he H1 hw. move=> <-. by right.
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move: (H1 ve)=> {H1} H1.
    have <- := to_word_not_undef s e ve vr U64 he H1 hw. move=> <-. by right.
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move: (H1 ve)=> {H1} H1.
    have <- := to_word_not_undef s e ve vr U64 he H1 hw. move=> <-. by right.
 (* Onot *)
 + case hb: to_bool=> [vb | vr] //=.
   (* to_bool reaches ok state *)
   + move=> <-. by left.
   (* to_bool reaches error state *)
   move: (H ve)=> {H} H.
    have <- := to_bool_not_undef s e ve vr he H hb. move=> <-. by right.
(* Olnot *)
+ case hw: to_word=> [vb | vr] //=.
  (* to_word reaches ok state *)
  + move=> <-. by left.
  (* to_word reaches error state *)
  move: (H ve)=> {H} H.
  have <- := to_word_not_undef s e ve vr sz he H hw. move=> <-. by right.
(* Oneg *)
case hw: to_word=> [vb | vr] //=.
(* to_word reaches ok state *)
+ move=> <-. by left.
(* to_word reaches error state *)
move: (H ve)=> {H} H.
have <- := to_word_not_undef s e ve vr sz he H hw. move=> <-. by right.
Qed.

Lemma sem_sop2_safe : forall s op e1 ve1 e2 ve2 r,
safe_sop2 op ->
sem_pexpr (wsw:= nosubword) false gd s e1 = ok ve1 ->
sem_pexpr (wsw:= nosubword) false gd s e2 = ok ve2 ->
sem_sop2 op ve1 ve2 = r -> 
is_ok r \/ r = Error ErrType.
Proof.
move=> s op e1 ve1 e2 ve2 r hs he1 he2. rewrite /sem_sop2 /=; inversion hs; subst.
(* Oadd *)
+ case hv1 : of_val=> [ w| wer] //=.
  (* ok *)
  + case hw: to_word=> [wo| woer] //=. 
    (* ok *)
    + move=> <-. by left.
    (* error *)
    move: (H0 ve1)=> {H0} H0.
    have -> := to_word_not_undef s e1 ve1 woer sz he1 H0 hw. move=> <-. by right.
  (* error *)
  have hr : wer = ErrType. rewrite /of_val /= in hv1.  
  move: (H0 ve2)=> {H0} H0.
  by have := to_word_not_undef s e2 ve2 wer sz he2 H0 hv1.
  + rewrite /of_val /= in hv1. 
  case hw : to_word=> [wv | wr] //=.
  + move=> hreq; subst. by right.
  move: (H0 ve1)=> {H0} H0.
  move=> hreq; subst. right. by have -> := to_word_not_undef s e1 ve1 wr sz he1 H0 hw.
(* Omul *)
+ case hv1 : of_val=> [ w| wer] //=.
  (* ok *)
  + case hw: to_word=> [wo| woer] //=. 
    (* ok *)
    + move=> <-. by left.
    (* error *)
    move: (H0 ve1)=> {H0} H0.
    have -> := to_word_not_undef s e1 ve1 woer sz he1 H0 hw. move=> <-. by right.
  (* error *)
  have hr : wer = ErrType. rewrite /of_val /= in hv1.  
  move: (H0 ve2)=> {H0} H0.
  by have := to_word_not_undef s e2 ve2 wer sz he2 H0 hv1.
  + rewrite /of_val /= in hv1. 
  case hw : to_word=> [wv | wr] //=.
  + move=> hreq; subst. by right.
  move: (H0 ve1)=> {H0} H0.
  move=> hreq; subst. right. by have -> := to_word_not_undef s e1 ve1 wr sz he1 H0 hw.
(* Osub *)
+ case hv1 : of_val=> [ w| wer] //=.
  (* ok *)
  + case hw: to_word=> [wo| woer] //=. 
    (* ok *)
    + move=> <-. by left.
    (* error *)
    move: (H0 ve1)=> {H0} H0.
    have -> := to_word_not_undef s e1 ve1 woer sz he1 H0 hw. move=> <-. by right.
  (* error *)
  have hr : wer = ErrType. rewrite /of_val /= in hv1.  
  move: (H0 ve2)=> {H0} H0.
  by have := to_word_not_undef s e2 ve2 wer sz he2 H0 hv1.
  + rewrite /of_val /= in hv1. 
  case hw : to_word=> [wv | wr] //=.
  + move=> hreq; subst. by right.
  move: (H0 ve1)=> {H0} H0.
  move=> hreq; subst. right. by have -> := to_word_not_undef s e1 ve1 wr sz he1 H0 hw.
(* Odiv *) (* Property never used in proof except undef *) 
+ case hv1 : of_val=> [w| wer] //=.
  (* ok *)
  + case hi : to_int=> [vi | vr] //=.
    (* ok *)
    + move=> hr; subst. by left.
    (* error *)
    move=> hr; subst. move: (H ve1)=> {H} H. 
    have -> := to_int_not_undef s e1 ve1 vr he1 H hi. by right.
  case hi : to_int=> [vi | vr] //=.
  + move=> hr; subst. 
    have hr : wer = ErrType. + rewrite /of_val /= in hv1. move:(H ve2)=> {H} H.
    by have := to_int_not_undef s e2 ve2 wer he2 H hv1.
    subst. by right.
  move=> hr; subst. move: (H ve1)=> {H} H. 
  have -> := to_int_not_undef s e1 ve1 vr he1 H hi. by right.
(* Odiv *)
+ case hv1 : of_val=> [w| wer] //=.
  (* ok *)
  + case hi : to_word=> [vi | vr] //=.
    (* ok *)
    + case hm : mk_sem_divmod=> [mr | mer] //=.
      (* ok *)
      + move=> <-. by left.
      (* error *)
      move=> hr; subst. rewrite /mk_sem_divmod /= in hm. 
      move: hm. move: (H1 ve1 ve2 w vi hv1 hi)=> h. by case: ifP=> //=.
    (* error *)
    move=> hr; subst. move: (H ve1)=> {H} H. right. 
    by have -> := to_word_not_undef s e1 ve1 vr sz he1 H hi.
  (* error *)
  have hr : wer = ErrType. rewrite /of_val /= in hv1.  
  move: (H ve2)=> {H} H.
  by have := to_word_not_undef s e2 ve2 wer sz he2 H hv1.
  + rewrite /of_val /= in hv1. 
  case hw : to_word=> [wv | wr] //=.
  + move=> hreq; subst. by right.
  move: (H ve1)=> {H} H.
  move=> hreq; subst. right. by have -> := to_word_not_undef s e1 ve1 wr sz he1 H hw.
(* Omod *) (* Property never used in proof except undef *) 
+ case hv1 : of_val=> [w| wer] //=.
  (* ok *)
  + case hi : to_int=> [vi | vr] //=.
    (* ok *)
    + move=> hr; subst. by left.
    (* error *)
    move=> hr; subst. move: (H ve1)=> {H} H. 
    have -> := to_int_not_undef s e1 ve1 vr he1 H hi. by right.
  case hi : to_int=> [vi | vr] //=.
  + move=> hr; subst. 
    have hr : wer = ErrType. + rewrite /of_val /= in hv1. move:(H ve2)=> {H} H.
    by have := to_int_not_undef s e2 ve2 wer he2 H hv1.
    subst. by right.
  move=> hr; subst. move: (H ve1)=> {H} H. 
  have -> := to_int_not_undef s e1 ve1 vr he1 H hi. by right.
(* Omods *)
+ case hv1 : of_val=> [w| wer] //=.
  (* ok *)
  + case hi : to_word=> [vi | vr] //=.
    (* ok *)
    + case hm : mk_sem_divmod=> [mr | mer] //=.
      (* ok *)
      + move=> <-. by left.
      (* error *)
      move=> hr; subst. rewrite /mk_sem_divmod /= in hm. 
      move: hm. move: (H1 ve1 ve2 w vi hv1 hi)=> h. by case: ifP=> //=.
    (* error *)
    move=> hr; subst. move: (H ve1)=> {H} H. right. 
    by have -> := to_word_not_undef s e1 ve1 vr sz he1 H hi.
  (* error *)
  have hr : wer = ErrType. rewrite /of_val /= in hv1.  
  move: (H ve2)=> {H} H.
  by have := to_word_not_undef s e2 ve2 wer sz he2 H hv1.
  + rewrite /of_val /= in hv1. 
  case hw : to_word=> [wv | wr] //=.
  + move=> hreq; subst. by right.
  move: (H ve1)=> {H} H.
  move=> hreq; subst. right. by have -> := to_word_not_undef s e1 ve1 wr sz he1 H hw.
(* Oland *)
Admitted.

Lemma safe_truncate_val_typeerror : forall t s e ve er, 
safe_expr s e ->
sem_pexpr (wsw:= nosubword) false gd s e = ok ve ->
(forall t, (ve <> (Vundef sint t))) 
    /\ (forall t, (ve <> (Vundef sbool t))) /\ 
(forall w t, (ve <> (Vundef (sword w) t))) ->
truncate_val t ve = Error er ->
er = ErrType.
Proof.
move=> t s e ve er hs he [] hse1 [] hse2 hse3. rewrite /truncate_val /=.
case hv: of_val=> [v | ev] //=. move=> [] hr; subst.
rewrite /of_val /= in hv. case: t hv=> //=.
+ rewrite /to_bool /=. case hb : (ve)=> [b | i | l arr | wo woo | t ut] //=; subst.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> [] <-.
  case: t ut hse3 hse2 hse1 he=> //=.
  + move=> i hse3 hse2 hse1 he hr. by move: (hse2 i)=> //=.
  + move=> i hse3 hse2 hse1 he hr. by move: (hse1 i)=> //=.
  move=> w i hse3 hse2 hse1 he hr. by move: (hse3 w i)=> //=. 
+ rewrite /to_int /=. case hb : (ve)=> [b | i | l arr | wo woo | t ut] //=; subst.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> [] <-.
  case: t ut hse3 hse2 hse1 he=> //=.
  + move=> i hse3 hse2 hse1 he hr. by move: (hse2 i)=> //=.
  + move=> i hse3 hse2 hse1 he hr. by move: (hse1 i)=> //=.
  move=> w i hse3 hse2 hse1 he hr. by move: (hse3 w i)=> //=.  
+ rewrite /to_arr. case hb : (ve)=> [b | i | l arr | wo woo | t ut] //=; subst.
  + rewrite /type_error. by move=> p [] <-.
  + rewrite /type_error. by move=> p [] <-.
  + move=> p. rewrite /WArray.cast /=. case: ifP=> //=.
    move=> /eqP hp. rewrite /type_error. by move=> [] <-.
  + rewrite /type_error. by move=> p [] <-.
  rewrite /type_error. by move=> p [] <-.
move=> w. rewrite /to_word. 
case hb : (ve)=> [b | i | l arr | wo woo | t ut] //=; subst.
+ rewrite /type_error. by move=> [] <-.
+ rewrite /type_error. by move=> [] <-.
+ rewrite /type_error. by move=> [] <-.
+ move=> ht. by have [-> h2]:= truncate_word_errP ht.
case: t ut hse3 hse2 hse1 he=> //=.
+ move=> i hse3 hse2 hse1 he hr. by move: (hse2 i)=> //=.
+ move=> i hse3 hse2 hse1 he hr. by move: (hse1 i)=> //=.
move=> ws i hse3 hse2 hse1 he hr. by move: (hse3 ws i)=> //=. 
Qed.

Lemma safe_to_bool_typeerror : forall s e ve er, 
safe_expr s e ->
sem_pexpr (wsw:= nosubword) false gd s e = ok ve ->
(forall t, (ve <> (Vundef sint t))) 
    /\ (forall t, (ve <> (Vundef sbool t))) /\ 
(forall w t, (ve <> (Vundef (sword w) t))) ->
to_bool ve = Error er ->
er = ErrType.
Proof.
move=> s e ve er hs he hse. rewrite /to_bool.
case: ve he hse=> //=.
+ rewrite /type_error. by move=> z he hse [] <-. 
+ rewrite /type_error. by move=> len a he hse [] <-. 
+ rewrite /type_error. by move=> w sw he hse [] <-. 
move=> t i he hse. case: t i he hse=> //=.
+ move=> t he [] h1 [] h2 h3 hr. by move: (h2 t).
+ move=> t he [] h1 [] h2 h3 hr. by move: (h1 t).
move=> w i he [] h1 [] h2 h3 hr. by move: (h3 w i).
Qed.


Theorem sem_pexpr_safe : forall e s r,
safe_expr s e ->
sem_pexpr (wsw:= nosubword) false gd s e = r ->
is_ok r \/ r = Error ErrType.
Proof.
move=> e s r. move: r s. elim: e.
(* Pconst *)
+ move=> z r s hs hr /=; subst. by left. 
(* Pbool *)
+ move=> b  r s hs hr /=; subst. by left.
(* Parr *)
+ move=> n r s hs hr /=; subst. by left.
(* Pvar *)
+ move=> x r s hs hg. inversion hs; subst; inversion H1; subst. 
  + left. rewrite /is_ok /= /get_gvar. case: ifP=> //= hgl. by rewrite H in hgl.
  left. rewrite /is_ok /= /get_gvar /=. case: ifP=> //= hl. by rewrite /get_global /= H0 /= H2.
(* Pget *)
+ move=> aa sz x e hin r s hs. inversion hs; subst. rewrite /on_arr_var /=.
  case hg : get_gvar=> [vg| er]//=.
  (* get_gvar reaches ok state *) 
  + case hg': vg hg=> [ v1 | v2 | l arr | ws w | t ut ] //=; subst; move=> hg ht; subst.
    (* get_gvar returns bool -> type error as it should be arr *) 
    + by right. 
    (* get_gvar return int -> type error as it should be arr *)
    + by right. 
    + left. rewrite H6 /=. case hw : WArray.get=> [vg | ee] //=.
      rewrite /WArray.get in hw. admit.
    (* get_gvar return word -> type error as it should be arr *)
    + right. move: hg. rewrite /get_gvar /=. by case: ifP=> //= hl.
    (* get_gvar return undef -> type error as it should be arr *)
    + right. move: hg. rewrite /get_gvar /=. by case: ifP=> //=.
  (* get_gvar reaches error state --> type error 
     safe conditions are met but still error means there is a type error *)
  move=> hr; subst. rewrite /get_gvar in hg. move: hg. inversion H3; subst.
  + case: ifP=> //= hl. by rewrite H in hl.
  case: ifP=> //= hl. rewrite /get_global H0 /=. case: ifP=> //= /eqP ht hr; subst.
  by right.
(* Psub *)
+ move=> aa sz len x e hin r s hs. inversion hs; subst. rewrite /on_arr_var /=.
  case hg : get_gvar=> [vg | ver] //=.
  (* get_gvar reaches ok state *)
  + case hg': vg hg=> [ v1 | v2 | l arr | ws w | t ut ] //=; 
    subst; move=> hg ht; subst.
    (* get_gvar returns bool -> type error as it should be arr *) 
    + by right. 
    (* get_gvar return int -> type error as it should be arr *)
    + by right. 
    + left. rewrite H7 /=. case hw : WArray.get_sub=> [vg | ee] //=.
      rewrite /WArray.get_sub in hw. move: hw. case: ifP=> //= hl hr.
      by rewrite H8 in hl.
    (* get_gvar return word -> type error as it should be arr *)
    + right. move: hg. rewrite /get_gvar /=. by case: ifP=> //= hl.
    (* get_gvar return undef -> type error as it should be arr *)
    + right. move: hg. rewrite /get_gvar /=. by case: ifP=> //=.
  move=> hr; subst. rewrite /get_gvar in hg. move: hg. inversion H4; subst.
  + case: ifP=> //= hl. by rewrite H in hl.
  case: ifP=> //= hl. rewrite /get_global H0 /=. case: ifP=> //= /eqP ht hr; subst.
  by right.
(* Pload *)
+ move=> sz x e hin r s hs /=. inversion hs; subst.
  by case hp : to_pointer=> [p | per] //=.
(* Psop1 *)
+ move=> op e hin r s hs /=. inversion hs; subst.
  case he: sem_pexpr=> [ve | vr] //=.
  + move=> ho. by have := sem_sop1_safe s op e ve r H3 he ho.
  move=> hr. rewrite hr in he. by move: (hin r s H2 he).
(* Psop2 *)
+ move=> op e1 hin1 e2 hin2 r s hs /=; inversion hs; subst.
  case he1: sem_pexpr=> [ev1 | vr1] //=.
  (* e1 evaluates to ok state *)
  + case he2: sem_pexpr=> [ev2 | vr2] //=.
    (* e2 evaluates to ok state *)
    + move=> ho. by have := sem_sop2_safe s op e1 ev2 e2 ev1 r H5 he2 he1 ho. 
    (* e1 evaluates to error state *)
    move=> hr. rewrite hr in he2. by move: (hin1 r s H3 he2). 
  (* e2 evaluates to error state *)
  case he2: sem_pexpr=> [ev1 | vr2] //=.
  move=> hr. rewrite hr in he1. by move: (hin2 r s H4 he1).
  move=> hr. rewrite hr in he2. by move: (hin1 r s H3 he2). 
(* PsopN *)
+ admit.
(* Pif *)
move=> t e hei e1 hei1 e2 hei2 r s hs /=; inversion hs; subst.
rewrite H6 /=. case hb : to_bool=> [bv | br] //=.
+ rewrite H7 /=. case ht: truncate_val=> [tv | tr] //=.
  + rewrite H9 /=. case ht': truncate_val=> [tv' | tr'] //=.
    + move=> <-. by left.
    move=> hr. 
    have hreq := safe_truncate_val_typeerror t s e2 vf tr' H5 H9 H12 ht'.
    rewrite hreq in hr. by right.
  move=> hr. have hreq := safe_truncate_val_typeerror t s e1 vt tr H4 H7 H11 ht.
  rewrite hreq in hr. by right.
move=> hrr. have hreq:= safe_to_bool_typeerror s e vb br H3 H6 H10 hb.
rewrite hreq in hrr. by right.
Admitted.

