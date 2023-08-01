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
   safe_sop2 (Oadd (Op_w sz))
| Somul sz:
   ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
   safe_sop2 (Omul (Op_w sz))
| Sosub sz:
   (sz ≤ U64)%CMP ->
   safe_sop2 (Osub (Op_w sz))
| Sodiv v1 v2 tin tin' tout sz r wr:
   v2 <> 0 ->
   type_of_op2 (Odiv Cmp_int) = (tin, tin', tout) ->
   is_word_type tin = Some sz ->
   is_word_type tin' = Some sz ->
   is_word_type tout = Some sz ->
   ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
   sem_sop2 (Odiv Cmp_int) v1 v2 = ok r ->
   to_word sz r = ok wr ->
   (wunsigned wr <=? wmax_unsigned sz)%Z -> 
   safe_sop2 (Odiv Cmp_int)
| Sodivs u v1 v2 sz r wr:
   v2 <> 0 ->
   ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
   sem_sop2 (Odiv (Cmp_w u sz)) v1 v2 = ok r ->
   to_word sz r = ok wr ->
   (wsigned wr >=? wmin_signed sz)%Z && (wsigned wr <=? wmax_signed sz)%Z ->
   safe_sop2 (Odiv (Cmp_w u sz))
| Somod v1 v2 tin tin' tout sz r wr:
   v2 <> 0 ->
   type_of_op2 (Odiv Cmp_int) = (tin, tin', tout) ->
   is_word_type tin = Some sz ->
   is_word_type tin' = Some sz ->
   is_word_type tout = Some sz ->
   ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
   sem_sop2 (Omod Cmp_int) v1 v2 = ok r ->
   to_word sz r = ok wr ->
   (wunsigned wr <=? wmax_unsigned sz)%Z -> 
   safe_sop2 (Odiv Cmp_int)
| Somods u v1 v2 tin tin' tout sz r wr:
   v2 <> 0 ->
   type_of_op2 (Odiv Cmp_int) = (tin, tin', tout) ->
   is_word_type tin = Some sz ->
   is_word_type tin' = Some sz ->
   is_word_type tout = Some sz ->
   ((U16 ≤ sz) && (sz ≤ U64))%CMP ->
   sem_sop2 (Omod Cmp_int) v1 v2 = ok r ->
   to_word sz r = ok wr ->
   (wsigned wr >=? wmin_signed sz)%Z && (wsigned wr <=? wmax_signed sz)%Z ->
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
| Sif s ty b et ef:
   safe_expr s b ->
   safe_expr s et ->
   safe_expr s ef ->
   safe_expr s (Pif ty b et ef) 

with safe_exprs : @estate nosubword syscall_state ep -> pexprs -> Prop :=
| Sempty s: 
   safe_exprs s [::]
| Sseq s s' e es:
   safe_expr s e ->
   safe_exprs s' es ->
   safe_exprs s (e :: es).

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
  move=> hr; subst. rewrite /to_int /= in hi.
  case hi: (ve) hi=> [b | i | l arr | wo w | t ut] //=; subst.
  + rewrite /type_error. move=> [] <-. by right. 
  + rewrite /type_error. move=> [] <-. by right. 
  + rewrite /type_error. move=> [] <-. by right. 
  case: t ut he=> //=.
  + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
  + move=> ut he hr. by move: (H (Vundef sint ut) ut)=> //=.
  move=> w ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
(* Oint_of_word *)
+ case hw: to_word=> [vw | vr] //=.
  (* to_word reaches an ok state *)
  + move=> hr; subst. by left.
  (* to_word reaches an error state *)
  move=> hr; subst. rewrite /to_word /= in hw.
  case hw: (ve) hw=> [b | i | l arr | wo w | t ut] //=; subst.
  + rewrite /type_error. move=> [] <-. by right. 
  + rewrite /type_error. move=> [] <-. by right. 
  + rewrite /type_error. move=> [] <-. by right. 
  + move=> ht. have [-> h2]:= truncate_word_errP ht. by right.
  case: t ut he=> //=.
  + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
  + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
  move=> w ut he /= hr. right. by move: (H (Vundef (sword w) ut) w ut).
(* Osignext *)
+ case hw: to_word=> [vw | vr] //=.
  (* to_word reaches an ok state *)
  + move=> hr; subst. by left.
  (* to_word reaches an error state *)
  move=> hr; subst. rewrite /to_word in hw. 
  + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
    + rewrite /type_error. move=> [] hr; subst. by right.
    + rewrite /type_error. move=> [] hr; subst. by right.
    + rewrite /type_error. move=> [] hr; subst. by right.
    + move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
    case: t ut he=> //=.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut).  
   (* U16 signext *)
  + case hw: to_word=> [vw | vr] //=.
    (* to_word reaches an ok state *)
    + move=> hr; subst. by left.
    (* to_word reaches an error state *)
    move=> hr; subst. rewrite /to_word in hw. 
    + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
      case: t ut he=> //=.
      + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
      + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
      move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut).
  (* U32 signext *)
  case hw: to_word=> [vw | vr] //=.
  (* to_word reaches an ok state *)
  + move=> hr; subst. by left.
  (* to_word reaches an error state *)
  move=> hr; subst. rewrite /to_word in hw. 
  + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
    + rewrite /type_error. move=> [] hr; subst. by right.
    + rewrite /type_error. move=> [] hr; subst. by right.
    + rewrite /type_error. move=> [] hr; subst. by right.
    + move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
    case: t ut he=> //=.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut).
(* Zeroext *)
+ case hw: to_word=> [vw | vr] //=.
  (* to_word evaluates to ok state *)
  + move=> hr; subst. by left.
  (* to_word evaluates to error state *)
  move=> hr; subst. rewrite /to_word in hw. 
  (* U8 signext *)
  + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
    + rewrite /type_error. move=> [] hr; subst. by right.
    + rewrite /type_error. move=> [] hr; subst. by right.
    + rewrite /type_error. move=> [] hr; subst. by right.
    + move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
    case: t ut he=> //=.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut).
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move=> hr; subst. rewrite /to_word in hw. 
    (* U16 zeroext *)
    + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
    case: t ut he=> //=.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut).
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move=> hr; subst. rewrite /to_word in hw. 
    (* U64 zeroext *)
    + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
    case: t ut he=> //=.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut).
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move=> hr; subst. rewrite /to_word in hw. 
    (* U12832 zeroext *)
    + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
    case: t ut he=> //=.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut).
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move=> hr; subst. rewrite /to_word in hw. 
    (* U25632 zeroext *)
    + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
    case: t ut he=> //=.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut).
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move=> hr; subst. rewrite /to_word in hw. 
    (* U12864 zeroext *)
    + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
    case: t ut he=> //=.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut).
  + case hw: to_word=> [vw | vr] //=.
    (* to_word evaluates to ok state *)
    + move=> hr; subst. by left.
    (* to_word evaluates to error state *)
    move=> hr; subst. rewrite /to_word in hw. 
   (* U25664 zeroext *)
    + case: (ve) hw=> [b | i | l arr | wo woo | t ut] //=; subst.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      + rewrite /type_error. move=> [] hr; subst. by right.
      move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
    case: t ut he=> //=.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    + move=> ut he hr. right. rewrite /type_error in hr. by case: hr=> <-.
    move=> w' ut he /= hr. right. by move: (H1 (Vundef (sword w') ut) w' ut). 
 (* Onot *)
 + case hb: to_bool=> [vb | vr] //=.
   (* to_bool reaches ok state *)
   + move=> <-. by left.
   (* to_bool reaches error state *)
   move=> hr; subst. rewrite /to_bool in hb.
   case: (ve) hb he=> [b | i | l arr | wo woo | t ut] //=; subst.
   + rewrite /type_error. move=> [] hr; subst. by right.
   + rewrite /type_error. move=> [] hr; subst. by right.
   + rewrite /type_error. move=> [] hr; subst. by right.
   case: t ut=> //=.
   + move=> ut hr he. right. by move: (H (Vundef sbool ut) ut).
   + move=> ut hr he. rewrite /type_error in hr. case: hr=> <-. by right.
   move=> w ut hr. rewrite /type_error in hr. case: hr=> <-. by right.
(* Olnot *)
+ case hw: to_word=> [vb | vr] //=.
  (* to_word reaches ok state *)
  + move=> <-. by left.
  (* to_word reaches error state *)
  move=> hr; subst. rewrite /to_word in hw.
  case: (ve) hw he=> [b | i | l arr | wo woo | t ut] //=; subst.
  + rewrite /type_error. move=> [] hr; subst. by right.
  + rewrite /type_error. move=> [] hr; subst. by right.
  + rewrite /type_error. move=> [] hr; subst. by right.
  + move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
  case: t ut=> //=.
  + move=> ut hr he. right. rewrite /type_error in hr. by case: hr=> <-.
  + move=> ut hr he. right. rewrite /type_error in hr. by case: hr=> <-.
  move=> w' ut /= hr he. right. by move: (H (Vundef (sword w') ut) w' ut). 
(* Oneg *)
case hw: to_word=> [vb | vr] //=.
(* to_word reaches ok state *)
+ move=> <-. by left.
(* to_word reaches error state *)
move=> hr; subst. rewrite /to_word in hw.
case: (ve) hw he=> [b | i | l arr | wo woo | t ut] //=; subst.
+ rewrite /type_error. move=> [] hr; subst. by right.
+ rewrite /type_error. move=> [] hr; subst. by right.
+ rewrite /type_error. move=> [] hr; subst. by right.
+ move=> ht. have [-> h2]:= truncate_word_errP ht. by right. 
case: t ut=> //=.
+ move=> ut hr he. right. rewrite /type_error in hr. by case: hr=> <-.
+ move=> ut hr he. right. rewrite /type_error in hr. by case: hr=> <-.
move=> w' ut /= hr he. right. by move: (H (Vundef (sword w') ut) w' ut).
Qed.

Lemma sem_sop2_safe : forall s op e1 ve1 e2 ve2 r,
safe_sop2 op ->
sem_pexpr (wsw:= nosubword) false gd s e1 = ok ve1 ->
sem_pexpr (wsw:= nosubword) false gd s e2 = ok ve2 ->
sem_sop2 op ve1 ve2 = r -> 
is_ok r \/ r = Error ErrType.
Proof.
Admitted.

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
case he2 : sem_pexpr=> [ve2 | vr2] //=.
+ case he1 : sem_pexpr=> [ve1 | vr1] //=.
  + case he : sem_pexpr=> [ve | vr] //=.
    + case hb : to_bool=> [vb |  br] //=.
      + case ht : truncate_val=> [vt | tr] //=.
        + case ht' : truncate_val => [vt' | tr'] //=.
          + move=> <-. by left.
          move=> hr.  
Admitted.

