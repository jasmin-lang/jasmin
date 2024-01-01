From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import psem_defs typing.

Section Safety_conditions.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {wsw : WithSubWord}
  (wdb : bool)
  (gd : glob_decls).

(* can be used to check that an expression does not evaluate to 0 *)
Definition not_zero_pexpr (e : pexpr) (s : @estate nosubword syscall_state ep) :=
forall v n, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
            to_int v = ok n -> 
n <> 0.

(* checks that a variable is defined in the memory *)
Definition defined_var (x : var_i) (s : @estate nosubword syscall_state ep) : bool :=
is_defined (evm s).[x].

(* Here len is the array length which is obtained from get_gvar *)
Definition alignment_range_check (aa : arr_access) (ws : wsize) (x : gvar) (e : pexpr) 
(s : @estate nosubword syscall_state ep) :=
forall v i len, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
                to_int v = ok i -> 
is_align (i * mk_scale aa ws)%Z ws /\ WArray.in_range len (i * mk_scale aa ws)%Z ws. 

(* Here len is the array length which is obtained from get_gvar *)
Definition alignment_sub_range_check (aa : arr_access) (ws : wsize) (slen : positive) (x : gvar) (e : pexpr) 
(s : @estate nosubword syscall_state ep) :=
forall v i len, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
                to_int v = ok i -> 
is_align (i * mk_scale aa ws)%Z ws /\
((0 <=? (i * mk_scale aa ws))%Z && ((i * mk_scale aa ws + arr_size ws slen) <=? len)%Z).

(* checks if the address is valid or not *)
Definition addr_check (x : var_i) (ws : wsize) (e : pexpr) (s : @estate nosubword syscall_state ep) :=
forall vx ve w1 w2, get_var wdb s.(evm) x = ok vx ->
              sem_pexpr (wsw:= nosubword) false gd s e = ok ve ->
              to_pointer vx = ok w1 ->
              to_pointer ve = ok w2 ->
validw (emem s) (w1 + w2)%R ws.

(* checks the safety condition for operations: except division and modulo, rest of the operations are safe without any 
   explicit condition *)
Definition safe_op2 (op : sop2) (e : pexpr) (s : @estate nosubword syscall_state ep) :=
match op with 
| Odiv ck => match ck with 
             | Cmp_w u sz => not_zero_pexpr e s
             | Cmp_int => True
             end
| Omod ck => match ck with 
             | Cmp_w u sz => not_zero_pexpr e s
             | Cmp_int => True
             end
| _ => True
end.  

Section safe_pexprs.

Variable safe_pexpr : @estate nosubword syscall_state ep -> pexpr -> Prop.

Fixpoint safe_pexprs (s : @estate nosubword syscall_state ep) (es : seq pexpr) : Prop :=
match es with 
| [::] => True 
| e :: es => safe_pexpr s e /\ safe_pexprs s es
end.

End safe_pexprs. 

Fixpoint safe_pexpr (s : @estate nosubword syscall_state ep) (e: pexpr)  := 
match e with 
 | Pconst _ | Pbool _ | Parr_init _ => True 
 | Pvar x => defined_var (gv x) s
 | Pget aa ws x e => defined_var (gv x) s /\ safe_pexpr s e /\ alignment_range_check aa ws x e s
 | Psub aa ws p x e => defined_var (gv x) s /\ safe_pexpr s e /\ alignment_sub_range_check aa ws p x e s
 | Pload ws x e => defined_var x s /\ addr_check x ws e s
 | Papp1 op e => safe_pexpr s e
 | Papp2 op e1 e2 => safe_pexpr s e1 /\ safe_pexpr s e2 /\ safe_op2 op e2 s
 | PappN op es => safe_pexprs (safe_pexpr) s es
 | Pif t e1 e2 e3 => safe_pexpr s e1 /\ safe_pexpr s e2 /\ safe_pexpr s e3
end.

Lemma get_gvar_ty_error : forall s x er, 
defined_var (gv x) s ->
get_gvar false gd (evm s) x = Error er ->
er = ErrType.
Proof.
move=> s x er. rewrite /defined_var /is_defined /= /get_gvar /=. 
case: ifP=> //= hl. rewrite /get_global /=.
case hg: get_global_value=> //=.
+ by case: ifP=> //= /eqP ht _ [] <-. 
by move=> _ [] <-.
Qed.

Lemma read_ty_error : forall vi aa sz l (arr:WArray.array l) ver,
is_align (vi * mk_scale aa sz)%Z sz ->
WArray.in_range l (vi * mk_scale aa sz)%Z sz ->
read arr (vi * mk_scale aa sz)%Z sz = Error ver ->
ver = ErrType.
Proof.
move=> vi aa sz l arr ver ha hw hr. 
Admitted.

Lemma to_int_ty_error : forall s e ve er,
sem_pexpr (wsw := nosubword) false gd s e = ok ve ->
safe_pexpr s e ->
to_int ve = Error er ->
er = ErrType.
Proof.
move=> s e. elim: e=> //=; rewrite /to_int /=.
+ move=> z ve er [] he _ //=; subst. by move=> //=. 
+ move=> b ve er [] he _ //=; subst. by move=> [] <-. 
+ move=> n ve er [] he _ //=; subst. by move=> [] <-.
+ move=> x ve er hg hd. case: ve hg=> //=.
  + by move=> b hg [] <-.
  + by move=> len a hw [] <-.
  + by move=> sz sw hg [] <-.
  move=> t i hg. case: t i hg=> //=.
  + by move=> i hg [] <-.
  move=> i hg [] hr. rewrite /get_gvar in hg. move: hg.
  case: ifP=> hl hg.
  + rewrite /get_var /= in hg. case: hg=> hg. by rewrite /defined_var hg /= in hd. 
    rewrite /get_global in hg. move: hg. case : get_global_value=> //= a. 
    case: ifP=> //= /eqP ht.
    move=> [] hv. rewrite /gv2val in hv. by case: a hv ht=> //=.
  by move=> w i hg [] <-.
+ move=> aa sz x e hin ve er. rewrite /on_arr_var /=. t_xrbindP=> z hg. case: z hg=> //= l a hg. 
  t_xrbindP=> z zv he hv zw hw hv1 [] hd [] hs ha hm. case: ve hin hv1 hm=> //=.
  by move=> sz' ws hin [] hsz h1 [] <-.
+ move=> aa sz len x e hin ve er. rewrite /on_arr_var /=. t_xrbindP=> z hg. case: z hg=> //= l a hg. 
  t_xrbindP=> z zv he hv zw hw hv1 [] hd [] hs ha hm. case: ve hin hv1 hm=> //=.
  by move=> sz' ws hin [] hsz h1 [] <-.
+ move=> sz x e hin ve er. t_xrbindP=> pt hp w z he hp' w' hr hv [] hd ha; subst. by move=> [] <-.
+ move=> op e hin ve er. t_xrbindP=> z he hop hs.
  case: ve hop=> //=.
  + by move=> b hop [] <-.
  + by move=> len a hop [] <-.
  + by move=> sz ws hop [] <-.
  move=> t i hop ht. apply hin with z. 
  + apply he.
  + apply hs.
  case: z he hop=> //=.
Admitted.

Lemma to_bool_ty_error : forall s e ve er,
sem_pexpr (wsw := nosubword) false gd s e = ok ve ->
safe_pexpr s e ->
to_bool ve = Error er ->
er = ErrType.
Proof.
Admitted.

Lemma truncate_val_ty_error : forall s e ve er t,
sem_pexpr (wsw := nosubword) false gd s e = ok ve ->
safe_pexpr s e ->
truncate_val t ve = Error er ->
er = ErrType.
Proof.
Admitted.

Theorem sem_pexpr_safe : forall e s r,
safe_pexpr s e ->
sem_pexpr (wsw:= nosubword) false gd s e = r ->
is_ok r \/ r = Error ErrType.
Proof.
move=> e s r. move: r s. elim: e.
(* Pconst *)
- move=> z r s /= _ <-. by left.
(* Pbool *)
- move=> b r s /= _ <-. by left.
(* Parr_init *)
- move=> n r s /= _ <-. by left.
(* Pvar *)
- move=> x r s /= hd hg. rewrite /defined_var /is_defined /= in hd.
  rewrite /get_gvar /= in hg. move: hg. case: ifP=> //= -[hlval hgob].
  (* lvar *)
  - rewrite /get_var /= in hgob; subst. by left.
  (* glob *)
  rewrite /get_global /= in hgob. move: hgob. case hgobv : get_global_value=> //=. 
  (* some value *)
  + case: ifP=> //= /eqP ht.
    * move=> <- /=. by left.
    move=> <-. by right.
  (* none *)
  move=> <- /=. by right.
(* Pget *)
- move=> aa sz x e /= hin r s [] hv [] he ha.
  rewrite /on_arr_var /=. case hg : get_gvar=> [vg| er]//=.
  (* get_gvar evaluates to ok *)
  + case hg': vg hg=> [ v1 | v2 | l arr | ws w | t ut ] //=; subst; move=> hg ht; subst.
    * by right.
    * by right.
    * case he': sem_pexpr=> [ve | ver] //=. 
      + case hi : to_int=> [vi | vir ] //=. rewrite /WArray.get /=. 
        rewrite /alignment_range_check /= in ha. move: (ha ve vi l he' hi)=> [] h1 h2.
        case hr: read=> [vr | ver] //=.
        + by left.
        right. by have -> := read_ty_error vi aa sz l arr ver h1 h2 hr.
      right. by have -> := to_int_ty_error s e ve vir he' he hi.
    by move: (hin (Error ver) s he he')=> /=.
    * by right.
    * by right.
  have -> := get_gvar_ty_error s x er hv hg. move=> <- /=. by right.
(* Psub *)
- admit.
(* Pload *)
- admit.
(* Papp1 *)
- move=> op e hin r s /= hs /=. admit.
(* Papp2 *)
- admit.
(* PappN *)
- admit.
move=> t e hie e1 hie1 e2 hie2 r s /= [] hse [] hse1 hse2.
case he2: sem_pexpr=> [ve2 | ver2] /=. (* e2 evaluates to ok or error *)
+ case he1: sem_pexpr=> [ve1 | ver1] /=. (* e1 evaluates to ok or error *)
  + case he: sem_pexpr=> [ve | ver] /=. (* e evaluates to ok or error *)
    + case hb: to_bool=> [vb | vbr] /=. (* to_bool evaluates to ok or error *)
      + case ht: truncate_val=> [vt | vtr] /=. (* truncate_val evaluates to ok or error *)
        + case ht': truncate_val=> [vt' | vtr'] /=. (* truncate_val evaluates to ok or error *)
          + move=> <- /=. by left.
          have -> := truncate_val_ty_error s e1 ve1 vtr' t he1 hse1 ht'. move=> <-. by right.
        case ht'': truncate_val=> [vt'' | vtr''] /= hr; subst.
        + have -> := truncate_val_ty_error s e2 ve2 vtr t he2 hse2 ht. by right.
Admitted.
          
          
End Safety_conditions.

