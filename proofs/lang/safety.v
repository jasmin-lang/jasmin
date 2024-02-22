From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import word_ssrZ.
Require Import psem_defs typing typing_proof.

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

Definition get_len_stype (t : stype) : positive :=
match t with 
| sbool => xH
| sint => xH 
| sarr n => n
| sword w => xH
end.

(* Here len is the array length which is obtained from get_gvar *)
(*Definition is_align_check (aa : arr_access) (ws : wsize) (e : pexpr) 
(s : @estate nosubword syscall_state ep) :=
forall v i, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
            to_int v = ok i -> 
is_align (i * mk_scale aa ws)%Z ws. *)

Definition is_align_check_array (e : pexpr) (ws : wsize) (s : @estate nosubword syscall_state ep) :=
forall v vp, sem_pexpr (wsw:= nosubword) false gd s e = ok v ->  
to_int v = ok vp ->
is_align vp ws.

Definition is_align_check_memory (e : pexpr) (ws : wsize) (s : @estate nosubword syscall_state ep) :=
forall v vp, sem_pexpr (wsw:= nosubword) false gd s e = ok v ->  
to_pointer v = ok vp ->
is_align vp ws.

Definition in_range_check (aa : arr_access) (ws : wsize) (x : var_i) (e : pexpr) 
(s : @estate nosubword syscall_state ep) :=
forall v i, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
            to_int v = ok i -> 
WArray.in_range (get_len_stype x.(v_var).(vtype)) (i * mk_scale aa ws)%Z ws. 

(* Here len is the array length which is obtained from get_gvar *)
Definition in_sub_range_check (aa : arr_access) (ws : wsize) (slen : positive) (x : var_i) (e : pexpr) 
(s : @estate nosubword syscall_state ep) :=
forall v i, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
                to_int v = ok i -> 
((0 <=? (i * mk_scale aa ws))%Z && ((i * mk_scale aa ws + arr_size ws slen) <=? (get_len_stype x.(v_var).(vtype)))%Z).

(* checks if the address is valid or not *) (* the index are initialized *) 
Definition addr_check (x : var_i) (ws : wsize) (e : pexpr) (s : @estate nosubword syscall_state ep) :=
forall ve w1 w2, defined_var x s ->
              sem_pexpr (wsw:= nosubword) false gd s e = ok ve ->
              to_pointer (evm s).[x] = ok w1 ->
              to_pointer ve = ok w2 ->
validw (emem s) (w1 + w2)%R ws. 

Inductive safe_cond : Type :=
| Defined_var : var_i -> safe_cond
| Not_zero : pexpr -> pexpr -> safe_cond
| Is_align : bool -> pexpr -> wsize -> safe_cond
| In_range : pexpr -> arr_access -> wsize -> var_i -> safe_cond
| In_sub_range : pexpr -> arr_access -> wsize -> positive -> var_i -> safe_cond
| Is_valid_addr : pexpr -> var_i -> wsize -> safe_cond.


(* checks the safety condition for operations: except division and modulo, rest of the operations are safe without any 
   explicit condition *)
Definition gen_safe_cond_op2 (op : sop2) (e1 e2 : pexpr) : seq safe_cond :=
match op with 
| Odiv ck => match ck with 
             | Cmp_w u sz => [:: Not_zero e1 e2]
             | Cmp_int => [::]
             end
| Omod ck => match ck with 
             | Cmp_w u sz => [:: Not_zero e1 e2]
             | Cmp_int => [::]
             end
| _ => [::]
end.

Definition interp_safe_cond_op2 (s : @estate nosubword syscall_state ep) (op : sop2) (e : pexpr) (sc: seq safe_cond) :=
match sc with 
| [::] => True 
| [:: sc] => not_zero_pexpr e s
| _ => True
end. 

Section gen_safe_conds. 

Variable gen_safe_cond : pexpr -> seq safe_cond.

Fixpoint gen_safe_conds (es : seq pexpr) : seq (seq safe_cond) := 
match es with
| [::] => [::]
| e :: es => gen_safe_cond e :: gen_safe_conds es
end. 

End gen_safe_conds. 


Definition Pmul := Papp2 (Omul Op_int).
Definition Padd := Papp2 (Oadd (Op_w Uptr)).
 
Fixpoint gen_safe_cond (e : pexpr) : seq safe_cond :=
match e with   
| Pconst _ | Pbool _ | Parr_init _ => [::] 
| Pvar x => [:: Defined_var (gv x)]
| Pget aa ws x e => [:: Defined_var (gv x); 
                        Is_align true (Pmul (Pconst (mk_scale aa ws)) e) ws; 
                        In_range e aa ws (gv x)] 
                     ++ gen_safe_cond e 
| Psub aa ws p x e => [:: Defined_var (gv x);
                          Is_align true (Pmul (Pconst (mk_scale aa ws)) e) ws; 
                          In_sub_range e aa ws p (gv x)] 
                       ++ gen_safe_cond e 
| Pload ws x e => [:: Defined_var x;
                      Is_align false (Padd (Pvar (mk_lvar x)) e) ws;
                      Is_valid_addr e x ws] 
                   ++ gen_safe_cond e 
| Papp1 op e => gen_safe_cond e
| Papp2 op e1 e2 => gen_safe_cond e1 ++ gen_safe_cond e2 ++ gen_safe_cond_op2 op e1 e2
| PappN op es => flatten (gen_safe_conds (gen_safe_cond) es)
| Pif t e1 e2 e3 => gen_safe_cond e1 ++ gen_safe_cond e2 ++ gen_safe_cond e3
end.

Section safe_pexprs.

Variable safe_pexpr : @estate nosubword syscall_state ep -> pexpr -> seq safe_cond -> Prop.

End safe_pexprs. Print arr_access.

Fixpoint interp_safe_cond (sc : safe_cond) (s : @estate nosubword syscall_state ep) : Prop :=
match sc with 
| Defined_var x => defined_var x s
| Not_zero e1 e2 => not_zero_pexpr e2 s
| Is_align b e ws => if b then is_align_check_array e ws s else is_align_check_memory e ws s
| In_range e aa ws x => in_range_check aa ws x e s
| In_sub_range e aa ws len x => in_sub_range_check aa ws len x e s
| Is_valid_addr e x ws => addr_check x ws e s
end.

Fixpoint interp_safe_conds (sc : seq safe_cond) (s : @estate nosubword syscall_state ep) : Prop :=
match sc with 
| [::] => True 
| sc1 :: sc2 => interp_safe_cond sc1 s /\ interp_safe_conds sc2 s
end.

Lemma interp_safe_concat : forall sc1 sc2 s,
interp_safe_conds (sc1 ++ sc2) s ->
interp_safe_conds sc1 s /\ interp_safe_conds sc2 s.
Proof.
move=> sc1 sc2 s /=. elim: sc1=> [h | s1 s2] //=.
move=> ht [] hs1 hs2. move: (ht hs2)=> [] hs3 hs4.
by split=> //=.
Qed.

Lemma wt_safe_get_gvar_not_undef : forall x s t i ty,
vtype (gv x) = ty ->
defined_var (gv x) s ->
get_gvar false gd (evm s) x <> ok (Vundef t i).
Proof.
move=> x s t i ty ht hd hg.
rewrite /defined_var /is_defined in hd.
rewrite /get_gvar /= in hg. move: hg. case: ifP=> //= hl.
+ rewrite /get_var /=. move=> [] hg. by rewrite hg in hd.
move=> /get_globalI [gv [hg hg'' hg']]. by case: gv hg hd hg''=> //=.
Qed.

Lemma wt_safe_get_gvar_not_error : forall x s ty err,
vtype (gv x) = ty ->
defined_var (gv x) s ->
get_gvar false gd (evm s) x <> Error err.
Proof.
move=> x s ty err ht hd hg.
have hter := @get_gvar_not_tyerr asm_op syscall_state ep spp wsw wdb gd x ty s err ht hg.
rewrite /get_gvar in hg. move: hg. case: ifP=> //= hl.
rewrite /get_global. case hv: (get_global_value gd (gv x)) ht=> [a | ] //=.
+ case: ifP=> //= /eqP hty ht [] h. by rewrite h in hter.
move=> ht [] h. by rewrite h in hter.
Qed.

Lemma safe_not_undef : forall e s t he,
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e <> ok (Vundef t he).
Proof.
move=> e s t u. elim: e=> //=.
(* Pvar *)
+ move=> x [] hd _ hg. rewrite /defined_var /is_defined in hd.
  rewrite /get_gvar /= in hg. move: hg. case: ifP=> //= hl.
  + rewrite /get_var /=. move=> [] hg. by rewrite hg in hd.
  move=> /get_globalI [gv [hg hg'' hg']]. by case: gv hg hd hg''=> //=.
(* Pget *)
+ move=> aa sz x e hin [] hs1 [] hs2 [] hs3 hs4. rewrite /on_arr_var /=.
  case hg: get_gvar=> [vg | er] //=. case: vg hg=> //= len a hg /=.
  move: (hin hs4)=> he. case he': sem_pexpr=> [ve | err] //=.
  case hi: to_int=> [vi | vrr] //=. by case ha : WArray.get=> [va | err] //=.
(* Psub *)
+ move=> aa sz len x e hin [] hs1 [] hs2 [] hs3 hs4. rewrite /on_arr_var /=.
  case hg: get_gvar=> [vg | er] //=. case: vg hg=> //= len' a hg /=.
  move: (hin hs4)=> he. case he': sem_pexpr=> [ve | err] //=.
  case hi: to_int=> [vi | vrr] //=. by case ha : WArray.get_sub=> [va | err] //=.
(* Pload *)
+ move=> sz x e hin [] hs1 [] hs2 [] hs3 hs4. case hp: to_pointer=> [vp | verr] //=.
  move: (hin hs4)=> he. case he': sem_pexpr=> [ve | verr] //=.
  case hp': to_pointer=> [vp' | verr'] //=. by case hr: read=> [vr | verr] //=.
(* Papp1 *)
+ move=> op e hin hs. move: (hin hs)=> he. case he': sem_pexpr=> [ve | verr] //=.
  rewrite /sem_sop1 /=. case hv: of_val=> [vv | verr] //=. case ht: to_val=> //= [t' ti].
  by have := to_valI ht.
(* Papp2 *)
+ move=> op e1 hin e2 hin' hs. 
  have [hs1 {hs} hs] := interp_safe_concat (gen_safe_cond e1) 
                        (gen_safe_cond e2 ++ gen_safe_cond_op2 op e1 e2) s hs.
  have [hs2 hs3] := interp_safe_concat (gen_safe_cond e2) (gen_safe_cond_op2 op e1 e2) s hs.
  move: (hin hs1)=> her1. move: (hin' hs2)=> her2. case he1 : sem_pexpr=> [ve1| ver1] //=.
  + case he2 : sem_pexpr=> [ve2| ver2] //=. rewrite /sem_sop2 /=. case hv : of_val=> [vv | ver] //=.
    + case hv' : of_val=> [vv' | ver'] //=. case ho: sem_sop2_typed=> [vo | vor] //=.
      case ht: to_val=> //= [t' ti]. by have := to_valI ht.
    by case hv' : of_val=> [vv | vvr] //=.
  by case he1': sem_pexpr=> [ve | ver] //=.
(* PappN *)
+ move=> op es hin hs. case hm: mapM=> [vm | vmr] //=. rewrite /sem_opN /=.
  case ha: app_sopn=> [va | var] //=. case ht: to_val=> //= [t' ti]. by have := to_valI ht.
(* Pif *)
move=> ty e hin e1 hin1 e2 hin2 hs.
have [hs1 hs2] := interp_safe_concat (gen_safe_cond e) (gen_safe_cond e1 ++ gen_safe_cond e2) s hs.
have [hs3 hs4] := interp_safe_concat (gen_safe_cond e1) (gen_safe_cond e2) s hs2.
move: (hin hs1)=> he1. move: (hin1 hs3)=> he2. move: (hin2 hs4)=> he3.
case h1: sem_pexpr=> [ve | ver] //=.
+ case h2: sem_pexpr=> [ve1 | ver1] //=.
  + case h3: sem_pexpr=> [ve2 | ver2] //=. case hb : to_bool=> [vb | vbr] //=.
    case ht: truncate_val=> [vt | vtr] //=.
    + case ht': truncate_val=> [vt' | vtr'] //=. case: ifP=> //= h; subst.
      + move: ht'. rewrite /truncate_val /=. case hv: of_val=> [vv | vvr] //=.
        move=> [] hv'. have := to_valI hv'. by case: vt' hv hv'=> //=.
      move: ht. rewrite /truncate_val /=. case hv: of_val=> [vv | vvr] //=.
      move=> [] hv'. have := to_valI hv'. by case: vt hv hv'=> //=.
    by case ht': truncate_val=> [vee | vtr1] //=.
  case he: sem_pexpr=> [vee | ver] //=. by case hb: to_bool=> [vb | vbr] //=.
case he1': sem_pexpr=> [ve1 | veer1] //=.  
+ case he': sem_pexpr=> [ve | vee] //=. case hb: to_bool=> [vb | vbr] //=.
  by case ht: truncate_val=> [vt | vtr] //=.  
case he' : sem_pexpr=> [ve | veer] //=. by case hb: to_bool=> [vb | vbr] //=.  
Qed.

Lemma wt_safe_truncate_not_error : forall pd e s v t ty err,
interp_safe_conds (gen_safe_cond e) s ->
ty_pexpr pd e = ok t ->
sem_pexpr false gd s e = ok v ->
subtype ty t ->
truncate_val ty v <> Error err.
Proof.
Admitted.

Lemma sem_op1_val_ty : forall tin tout op v vo,
type_of_op1 op = (tin, tout) ->
sem_sop1 op v = ok vo ->
type_of_val vo = tout.
Proof.
move=> tin tout op v vo ht ho.
rewrite /sem_sop1 /= in ho.  move: ho. 
t_xrbindP=> z h1 h2. have := to_valI h2. case: vo h2=> //=.
+ move=> b /= hb [] b' heq; subst. by rewrite -b' /= ht /=. 
+ move=> zi /= hi [] zi' heq; subst. by rewrite -zi' /= ht /=.
+ move=> len a ha [] len' heq; subst. by rewrite -len' /= ht /=.
move=> w w' hw [] wt heq; subst. by rewrite -wt /= ht /=.
Qed.

Lemma of_val_equal_not_error : forall t1 t2 ve1 ve2 err,
value_uincl ve2 ve1 ->
subtype t2 t1 ->
of_val t1 ve1 <> Error err ->
of_val t2 ve2 <> Error err.
Proof. 
Admitted.

Lemma wt_safe_of_val_not_error : forall pd s e t ty ve err,
ty_pexpr pd e = ok t ->
subtype ty t ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
of_val ty ve <> Error err.
Proof.
move=> pd s e. elim: e=> //=.
+ move=> z t ty ve err [] h hsub hs [] he; subst. rewrite /of_val /=.
  by case: ty hsub=> //=.
+ move=> b t ty ve err [] h hsub hs [] he; subst. rewrite /of_val /=.
  by case: ty hsub=> //=.
+ admit.
+ admit.
+ admit.
+ admit.
+ admit.
+ move=> op e hin t ty ve err. case hto: type_of_op1=> [tin tout] //=. 
  rewrite /check_expr /= /check_type.
  t_xrbindP=> t1 t2 hte. case: ifP=> //= hsub [] heq heq'; subst. 
  move=> hsub' hs vz he ho hof. have htve := sem_op1_val_ty tin t op vz ve hto ho.
  rewrite /sem_sop1 in ho. admit.
+ admit.
+ admit.
move=> t e hin1 e1 hin2 e2 hin3 t1 t2 v err hc hsub2 hs. 
have [hs1 {hs} hs] := interp_safe_concat (gen_safe_cond e) (gen_safe_cond e1 ++ gen_safe_cond e2) s hs.
have [hs2 {hs} hs3] := interp_safe_concat (gen_safe_cond e1) (gen_safe_cond e2) s hs.
move: hc. rewrite /check_expr /check_type. 
case hte2: ty_pexpr=> [te2 | ter2] //=. 
+ case hte1: ty_pexpr=> [te1 | ter1] //=.
  + case hte: ty_pexpr=> [te | ter] //=. case: ifP=> //=.
    + move=> hsub2'. case: ifP=> //=.
      + move=> hsub1. case: ifP=> //=. move=> /eqP hb [] hteq; subst.
        case he2: sem_pexpr=> [ve2 | ver2] //=.
        + case he1: sem_pexpr=> [ve1 | ver1] //=.
          + case he: sem_pexpr=> [ve | ver] //=. case hb: to_bool=> [vb | vbr] //=.
            case htr: truncate_val=> [vt | vtr] //=.
            + case htr': truncate_val=> [vt' | vtr'] //=. move=> [] hv; subst. 
              case: ifP=> /=.
              + move=> hvb. move: (hin2 te1 t1 ve1 err hte1 hsub1 hs2 he1)=> hvr.
                have hveq := truncate_value_uincl htr'. 
Admitted.              
  

Lemma wt_safe_sem_op1_not_error : forall pd op tin tout t1 e s v err,
type_of_op1 op = (tin, tout) ->
subtype tin t1 ->
ty_pexpr pd e = ok t1 ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok v ->
sem_sop1 op v <> Error err.
Proof.
move=> pd op tin tout t e s ve err htop hsub hte hse hs. 
rewrite /sem_sop1 /=.
case hvo: of_val=> [vo | vor] //=. rewrite htop /= in hvo.
Admitted.

Lemma wt_safe_sem_sop2_not_error : forall pd op t1 e1 t2 e2 s ve1 ve2 err,
subtype (type_of_op2 op).1.1 t1 ->
ty_pexpr pd e1 = ok t1 ->
subtype (type_of_op2 op).1.2 t2 ->
ty_pexpr pd e2 = ok t2 ->
interp_safe_conds (gen_safe_cond e1) s ->
interp_safe_conds (gen_safe_cond e2) s ->
interp_safe_conds (gen_safe_cond_op2 op e1 e2) s ->
sem_pexpr false gd s e1 = ok ve1 ->
type_of_val ve1 = t1 ->
sem_pexpr false gd s e2 = ok ve2 ->
type_of_val ve2 = t2 ->
sem_sop2 op ve1 ve2 <> Error err.
Proof.
Admitted.

Lemma wt_safe_read_not_error : forall pd e t (x:var_i) s w ve vp vp' err,
subtype (sword pd) t ->
ty_pexpr pd e = ok t ->
subtype (sword pd) (vtype x) ->
defined_var x s ->
is_align_check_memory (Padd (mk_lvar x) e) w s ->
addr_check x w e s ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
to_pointer ve = ok vp ->
to_pointer (evm s).[x] = ok vp' ->
read (emem s) (vp' + vp)%R w <> Error err.
Proof.
Admitted.


Lemma wt_safe_to_pointer_error : forall x s err,
defined_var x s ->
to_pointer (evm s).[x] <> Error err.
Proof.
Admitted.

Lemma wt_safe_exp_to_pointer_error : forall pd e t (x:var_i) s (*w*) ve err,
ty_pexpr pd e = ok t ->
subtype (sword pd) t ->
interp_safe_conds (gen_safe_cond e) s ->
(*interp_safe_conds [:: Is_valid_addr e x w] s ->*)
sem_pexpr false gd s e = ok ve ->
(*type_of_val ve = t ->*)
to_pointer ve <> Error err.
Proof.
move=> pd e t x s ve err ht hsub hs he. 
have htve := @sem_pexpr_well_typed asm_op syscall_state ep spp wsw wdb gd pd t e s ve ht he.
move: ht hs he htve. elim: e=> //=.
+ move=> z [] ht _ [] hve htve; subst. by rewrite /subtype in hsub.
+ move=> b [] ht _ [] hve htve; subst. by rewrite /subtype in hsub.
+ move=> n [] ht _ [] hve htve; subst. by rewrite /subtype in hsub.
+ move=> x' [] ht [] hd _ hg htve; subst. rewrite /to_pointer /=.
  case: ve hg htve=> //=.
  + move=> b hg htve; subst. by rewrite /subtype -htve in hsub.
  + move=> z hg htve; subst. by rewrite /subtype -htve in hsub.
  + move=> len a hg htve; subst. by rewrite /subtype -htve in hsub.
  + move=> wsz w hg htve; subst. rewrite /subtype -htve in hsub.
    case htt : (truncate_word Uptr (s':=wsz) w)=> //= [etr].
Admitted.

Lemma wt_safe_read_arr_not_error : forall pd e x p aa sz s arr (p':WArray.array arr) ve vi err,
ty_pexpr pd e = ok sint ->
vtype (gv x) = sarr p ->
defined_var (gv x) s ->
is_align_check_array (Pmul (mk_scale aa sz) e) sz s ->
in_range_check aa sz (gv x) e s ->
interp_safe_conds (gen_safe_cond e) s ->
get_gvar false gd (evm s) x = ok (Varr p') ->
sem_pexpr false gd s e = ok ve ->
read p' (vi * mk_scale aa sz)%Z sz <> Error err.
Proof.
Admitted.

Lemma wt_safe_to_int_not_error : forall pd e (s: @estate nosubword syscall_state ep) ve err,
ty_pexpr pd e = ok sint ->
interp_safe_conds (gen_safe_cond e) s ->
sem_pexpr false gd s e = ok ve ->
to_int ve <> Error err.
Proof.
move=> pd e s ve err ht hs he. 
have htve := @sem_pexpr_well_typed asm_op syscall_state ep spp wsw wdb gd pd sint e s ve ht he.
rewrite /to_int /=. case: ve he htve=> //= t i he hte; subst.
by have := safe_not_undef e s sint i hs he.
Qed.

Lemma wt_safe_sem_opN_not_error : forall pd es op vm vma s err,
mapM2 ErrType (check_expr ty_pexpr pd) es (type_of_opN op).1 = ok vm ->
interp_safe_conds (flatten (gen_safe_conds gen_safe_cond es)) s ->
mapM (sem_pexpr false gd s) es = ok vma ->
sem_opN op vma <> Error err.
Proof.
Admitted.

Lemma wt_safe_mapM_not_error : forall pd es op vm s err,
mapM2 ErrType (check_expr ty_pexpr pd) es (type_of_opN op).1 = ok vm ->
interp_safe_conds (flatten (gen_safe_conds gen_safe_cond es)) s ->
mapM (sem_pexpr false gd s) es <> Error err.
Proof.
Admitted.

Lemma type_of_get_gvar_eq : forall x (vm : @Vm.t nosubword) v,
is_defined v ->
get_gvar false gd vm x = ok v ->
(type_of_val v) = (vtype x.(gv)).
Proof.
move=> x vm v. rewrite /get_gvar. case: ifP=> //= hl hd hg.
+ have /= [_ h]:= get_var_compat hg. rewrite /compat_val /= /compat_type in h.
  move: h. case: ifP=> //=.
  + move=> hd'. by rewrite hd in hd'.
  by move=> hd' /eqP ->.
by have := type_of_get_global hg.
Qed.

Theorem sem_pexpr_safe : forall pd e s ty,
ty_pexpr pd e = ok ty ->
interp_safe_conds (gen_safe_cond e) s ->
exists v, sem_pexpr (wsw := nosubword) false gd s e = ok v /\ type_of_val v = ty.
Proof.
move=> pd e s. elim: e=> //=.
(* Pconst *)
+ move=> z ty [] ht _; subst. by exists z. 
(* Pbool *)
+ move=> b ty [] ht _; subst. by exists b. 
(* Parr_init *)
+ move=> n ty [] ht _; subst. by exists (Varr (WArray.empty n)).
(* Pvar *)
+ move=> x ty [] ht [] hd _. case hg: get_gvar=> [vg | vgr] //=.
  + exists vg. split=> //=. have hvg : is_defined vg. 
    + rewrite /is_defined /=. 
      case: vg hg=> //= t i hg. 
      by have := wt_safe_get_gvar_not_undef x s t i ty ht hd. 
    have hsub := type_of_get_gvar_eq x (evm s) vg hvg hg.
    by rewrite ht /= in hsub. 
  by have := wt_safe_get_gvar_not_error x s ty vgr ht hd hg.
(* Pget *)
+ move=> aa sz x e hin ty. rewrite /ty_get_set /check_array /=. 
  t_xrbindP=> t hte t'. case ht: (vtype (gv x))=> [  | | p |] //= [] heq; subst.
  rewrite /check_int /check_type /=. case: ifP=> //= /eqP hteq t2 [] hteq' hteq''; subst. 
  move=> [] hs1 [] hs2 [] hs3 hs4.
  rewrite /on_arr_var /=. case hg: get_gvar=> [vg | vgr] //=.
  + case hvg: vg=> [b | z | p' arr| w wsz| t i] //=; subst.
    + have hdb : is_defined b. + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) b hdb hg. by rewrite ht /= in ht'.
    + have hdb : is_defined z. + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) z hdb hg. by rewrite ht /= in ht'.
    + move: (hin sint hte hs4) => [] ve [] he htve. rewrite he /=. 
      case hi : to_int=> [vi | vr] //=.
      + case hw : WArray.get=> [vw | vwr] //=.
        + exists (Vword (s:=sz) vw). by split=> //=.
        rewrite /WArray.get /= in hw.
        by have := wt_safe_read_arr_not_error pd e x p aa sz s p' arr ve vi vwr hte ht hs1 hs2 hs3 hs4 hg he.
      by have := wt_safe_to_int_not_error pd e s ve vr hte hs4 he. 
    + have hdb : is_defined (Vword (s:=w) wsz). + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) (Vword (s:=w) wsz) hdb hg. by rewrite ht /= in ht'.
    by have := wt_safe_get_gvar_not_undef x s t i (sarr p) ht hs1. 
  by have := wt_safe_get_gvar_not_error x s (sarr p) vgr ht hs1.
(* Psub *)
+ move=> aa sz len x e hin ty. rewrite /ty_get_set_sub /check_array /= /check_int /= /check_type /=.
  t_xrbindP => t hte t'. case ht: (vtype (gv x))=> [  | | p|] //= [] heq; subst.
  move=>ti. case: ifP=> //= /eqP hteq [] hteq' hteq''; subst. move=> [] hs1 [] hs2 [] hs3 hs4.   
  rewrite /on_arr_var /=. case hg: get_gvar=> [vg | vgr] //=.
  + case hvg: vg=> [b | z | p' arr| w wsz| t i] //=; subst.
    + have hdb : is_defined b. + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) b hdb hg. by rewrite ht /= in ht'.
    + have hdb : is_defined z. + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) z hdb hg. by rewrite ht /= in ht'.
    + move: (hin sint hte hs4) => [] ve [] he htve. rewrite he /=. 
      case hi : to_int=> [vi | vr] //=.
      + case hw : WArray.get_sub=> [vw | vwr] //=.
        + exists (Varr vw). by split=> //=.
        rewrite /WArray.get_sub /= in hw. move: hw. case: ifP=> //= /andP [].
        rewrite /in_sub_range_check /= ht /= in hs3.
        have hd : is_defined (Varr arr).
        + by rewrite /is_defined.
        move: (hs3 ve vi he hi)=> /andP. have hsub' := type_of_get_gvar_eq x (evm s) (Varr arr) hd hg. 
        rewrite ht /= in hsub'. by move: hsub'=> [] heq'; subst.
      by have := wt_safe_to_int_not_error pd e s ve vr hte hs4 he. 
    + have hdb : is_defined (Vword (s:=w) wsz). + by rewrite /is_defined. 
      have ht' := type_of_get_gvar_eq x (evm s) (Vword (s:=w) wsz) hdb hg. by rewrite ht /= in ht'.
    by have := wt_safe_get_gvar_not_undef x s t i (sarr p) ht hs1.
  by have := wt_safe_get_gvar_not_error x s (sarr p) vgr ht hs1.
(* Pload *)
+ move=> w x e hin ty. rewrite /ty_load_store /= /check_ptr /check_type.
  t_xrbindP=> te hte t1. case: ifP=> //= hsub heq t2; subst. 
  case: ifP=> //= hsub' heq' t3 hs; subst. case: heq'=> heq'; subst.
  move:hs=> [] hs1 [] hs2 [] hs3 hs4.
  move: (hin t2 hte hs4)=> [] ve [] he htve. rewrite he /=.
  case hp: to_pointer=> [vp | vpr] //=.
  + case hp': to_pointer=> [vp' | vpr'] //=.
    + case hr: read=> [vr | vrr] //=.
      + exists (Vword (s:=w) vr). by split=> //=.
      by have /= := wt_safe_read_not_error pd e t2 x s w ve vp vp' vrr hsub' hte hsub hs1 hs2 hs3 hs4 he hp hp'.
    by have //= := wt_safe_to_pointer_error x s vpr' hs1.
  by have //= := wt_safe_exp_to_pointer_error pd e t2 x s ve vpr hte hsub' hs4 he.
(* Papp1 *)
+ move=> op e hin ty. case hto: type_of_op1=> [tin tout]. rewrite /check_expr /= /check_type.
  t_xrbindP=> t1 t2 hte. case: ifP=> //= hsub [] heq heq'; subst. 
  move=> hs. move: (hin t1 hte hs)=> [] v [] he ht. rewrite he /=.
  case ho: sem_sop1=> [ vo | vor] //=.
  + exists vo. split=> //=.
    by have := sem_op1_val_ty tin ty op v vo hto ho.
  by have //= := wt_safe_sem_op1_not_error pd op tin ty t1 e s v vor hto hsub hte hs he.
(* Papp2 *)
+ move=> op e1 hin1 e2 hin2 ty. rewrite /check_expr /check_type /=.
  t_xrbindP=> t1 t1' ht1. case: ifP=> //= hsub [] hteq t2 t2' ht2; subst.
  case: ifP=> //= hsub' [] hteq' hteq hs; subst.
  have [hs1 hs2] := interp_safe_concat (gen_safe_cond e1) 
                         ((gen_safe_cond e2) ++ (gen_safe_cond_op2 op e1 e2)) s hs.
  have [hs3 hs4] := interp_safe_concat (gen_safe_cond e2) (gen_safe_cond_op2 op e1 e2) s hs2.
  move: (hin1 t1 ht1 hs1)=> [] ve1 [] he1 hte1.
  move: (hin2 t2 ht2 hs3)=> [] ve2 [] he2 hte2. rewrite he1 /= he2 /=.
  case ho: sem_sop2=> [vo | vor] //=.
  + exists vo. split=> //=. rewrite /sem_sop2 /= in ho.
    move: ho. t_xrbindP=> z h1 z' h2 z1 h3 h4 /=. rewrite -h4 /=. by apply type_of_to_val. 
  by have := wt_safe_sem_sop2_not_error pd op t1 e1 t2 e2 s ve1 ve2 
             vor hsub ht1 hsub' ht2 hs1 hs3 hs4 he1 hte1 he2 hte2 ho.
(* PappN *)
+ move=>op es hin t. rewrite /check_pexprs /=. case hm: mapM2=> [vm | vmr] //=.
  move=> [] heq hs; subst. case hma: mapM=> [vma | vmar] //=.
  + case ho: sem_opN=> [vo | vor] //=.
    + exists vo. split=> //=. 
      + rewrite /sem_opN /= in ho. move: ho. t_xrbindP=> tso happ htv.
        have := type_of_to_val tso. by rewrite htv. 
      by have := wt_safe_sem_opN_not_error pd es op vm vma s vor hm hs hma.
    by have := wt_safe_mapM_not_error pd es op vm s vmar hm hs.
(* Pif *)
move=> t e hin e1 hin1 e2 hin2 ty hty hs. move: hty.
rewrite /check_expr /= /check_type /=. t_xrbindP=> te te' hte. 
case: ifP=> //= /eqP hte' [] heq; subst.
move=> t1 t2 hte1. case: ifP=> //= hsub [] heq; subst.
move=> t2 t3 hte2. case: ifP=> //= hsub' [] heq' heq''; subst.
have [hs1 hs2]:= interp_safe_concat (gen_safe_cond e) 
                        ((gen_safe_cond e1) ++ (gen_safe_cond e2)) s hs.
have [hs3 hs4]:= interp_safe_concat (gen_safe_cond e1) (gen_safe_cond e2) s hs2.
move: (hin sbool hte hs1)=> [] b [] he hbt.
move: (hin1 t1 hte1 hs3)=> [] v1 [] he1 ht1.
move: (hin2 t2 hte2 hs4)=> [] v2 [] he2 ht2.
rewrite he /= he1 /= he2 /=. 
case: b he hbt=> //= b he hbt /=. 
+ case ht: truncate_val=> [vt | vtr] //=.
  + case ht': truncate_val=> [vt' | vtr'] //=.
    + exists (if b then vt' else vt). split=> //=.
      case hb: b he=> //= he.
      + by have := truncate_val_has_type ht'.
      by have := truncate_val_has_type ht.
    by have //= := wt_safe_truncate_not_error pd e1 s v1 t1 ty vtr' hs3 hte1 he1 hsub.
  by have //= := wt_safe_truncate_not_error pd e2 s v2 t2 ty vtr hs4 hte2 he2 hsub'.
move=> hbeq; subst. by have //= := safe_not_undef e s sbool he hs1 hbt. 
Qed.


(*Theorem sem_pexpr_safe : forall e s r,
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
- move=> aa sz len x e /= hin r s [] hd [] hs ha. rewrite /on_arr_var /=. 
  case hg : get_gvar=> [vg | vgr] //=.
  + case hg': vg hg=> [ v1 | v2 | l arr | ws w | t ut ] //=; subst; move=> hg ht; subst.
    * by right.
    * by right.
    * case he': sem_pexpr=> [ve | ver] //=.
      + case hi: to_int=> [vi | vir] //=. case hwa : WArray.get_sub=> [wa | war] //=.
        + by left.
        rewrite /WArray.get_sub in hwa. move: hwa. case: ifP=> //= h.
        rewrite /alignment_sub_range_check in ha. move: (ha ve vi l he' hi)=> [] hal hc.
        by rewrite hc in h.
      have -> := to_int_ty_error s e ve vir he' hs hi. by right.
    by move: (hin (Error ver) s hs he') => /=.
    * by right.
    * by right.
  have -> := get_gvar_ty_error s x vgr hd hg. move=> <- /=. by right.   
(* Pload *)
- move=> sz z e hin r s /= [] hs [] hd ha.
  case hp: to_pointer=> [vp | vpr] //=.
  + case he: sem_pexpr=> [ve | ver] //=.
    + case hp': to_pointer=> [vp' | vpr']//=.
      + case hr: read=> [vr | vre] //=.
        + move=> <-. by left.
        move=> h; subst. rewrite /addr_check in ha.
        move: (ha z ve vp vp' hd he hp hp')=> hw. 
        rewrite /validw in hw. move: hw. move=> /andP [] hal hall. 
        have -> := read_mem_ty_error vp vp' sz s vre hal hr. by right.
       move=> h; subst. have -> := to_pointer_ty_error s e ve vpr' he hs hp'. by right.
     move=> hr; subst. by move: (hin (Error ver) s hs he).
  move=> h; subst. have -> := to_pointer_ty_error' s z vpr hd hp. by right.
(* Papp1 *)
- move=> op e hin r s /= hs /=.
  case he: sem_pexpr=> [ve | ver] //=.
  + rewrite /sem_sop1 /=. case hv: of_val=> [vv | vvr] //=.
    + move=> <-. by left.
    move=> h; subst. have -> := of_val_ty_error (type_of_op1 op).1 s e ve vvr he hs hv.
    by right.
  move=> h; subst. by move: (hin (Error ver) s hs he).
(* Papp2 *)
- move=> op e1 hin e2 hin' r s /= [] hs1 [] hs2 hs3.
  case he2: sem_pexpr=> [ve2 | ver2] //=.
  + case he1: sem_pexpr=> [ve1 | ver1] //=.
    + move=> ho. by have := sem_sop2_safe s op e1 ve1 e2 ve2 r hs3 he1 he2 ho.
    move=> h; subst. by move: (hin (Error ver1) s hs1 he1).
  case he1: sem_pexpr=> [ve1 | ver1] //=. 
  + move=> h; subst. by move: (hin' (Error ver2) s hs2 he2).
  move=>h; subst. by move: (hin (Error ver1) s hs1 he1). 
(* PappN *)
- move=> op es hin r s hs /=. 
  case hm: mapM=> [vm | vmr] //= ho. 
  + case hr: r ho=> [vo | vor] //=.
    + subst. by left.
    move=> ho. have -> := sem_opN_safe s es vm vor op hs hm ho. by right.
  subst. case: es hin hs hm=> //= e es hin [] hse hses.
  case h: sem_pexpr=> [ve | ver] //=.
  + case hm: mapM=> [vs | vsr] //=.
    + move=> [] heq; subst. have heq : e = e \/ List.In e es. + by left.
      have -> := sem_pexprs_ty_error s es vmr hses hm. by right.
    have heq : e = e \/ List.In e es. + by left.
    move=> [] h'; subst. by move: (hin e heq (Error vmr) s hse h)=> /=.
move=> t e hie e1 hie1 e2 hie2 r s /= [] hse [] hse1 hse2.
case he2: sem_pexpr=> [ve2 | ver2] /=. 
+ case he1: sem_pexpr=> [ve1 | ver1] /=. 
  + case he: sem_pexpr=> [ve | ver] /=. 
    + case hb: to_bool=> [vb | vbr] /=. 
      + case ht: truncate_val=> [vt | vtr] /=. 
        + case ht': truncate_val=> [vt' | vtr'] /=. 
          + move=> <- /=. by left.
          have -> := truncate_val_ty_error s e1 ve1 vtr' t he1 hse1 ht'. move=> <-. by right.
        case ht'': truncate_val=> [vt'' | vtr''] /= hr; subst.
        + have -> := truncate_val_ty_error s e2 ve2 vtr t he2 hse2 ht. by right.
        have -> := truncate_val_ty_error s e1 ve1 vtr'' t he1 hse1 ht''. by right.
      move=> h; subst. have -> := to_bool_ty_error s e ve vbr he hse hb. by right.
    move=> h; subst. by move: (hie (Error ver) s hse he).  
  case he: sem_pexpr=> [ve | ver] //=.
  + case hb: to_bool=> [vb | vbr] //=.
    + move=> h; subst. by move: (hie1 (Error ver1) s hse1 he1). 
    move=> h; subst. have -> := to_bool_ty_error s e ve vbr he hse hb. by right.
  move=> h; subst. by move: (hie (Error ver) s hse he).
case he1: sem_pexpr=> [ve1 | ver1] //=.
+ case he: sem_pexpr=> [ve | ver] //=.
  + case hb: to_bool=> [vb | vbr] //=.
    + case ht: truncate_val=> [vt | vtr] //=.
      + move=> h; subst. by move: (hie2 (Error ver2) s hse2 he2).
      move=> h; subst. have -> := truncate_val_ty_error s e1 ve1 vtr t he1 hse1 ht. by right.
    move=> h; subst. have -> := to_bool_ty_error s e ve vbr he hse hb. by right.
  move=> h; subst. by move: (hie (Error ver) s hse he).
case he: sem_pexpr=> [ve | ver] //=.
+ case hb: to_bool=> [vb | vbr] //=.
  + move=> h; subst. by move: (hie1 (Error ver1) s hse1 he1).
  have -> := to_bool_ty_error s e ve vbr he hse hb. move=> <-. by right.
move=> h; subst. by move: (hie (Error ver) s hse he).
Qed.*)
          
          
End Safety_conditions.

