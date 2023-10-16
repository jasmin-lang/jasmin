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

Definition not_zero_pexpr (e : pexpr) (s : @estate nosubword syscall_state ep) :=
forall v n, sem_pexpr (wsw:= nosubword) false gd s e = ok v -> 
            to_int v = ok n -> 
n <> 0.

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

Definition addr_check (x : var_i) (ws : wsize) (e : pexpr) (s : @estate nosubword syscall_state ep) :=
forall vx ve w1 w2, get_var wdb s.(evm) x = ok vx ->
              sem_pexpr (wsw:= nosubword) false gd s e = ok ve ->
              to_pointer vx = ok w1 ->
              to_pointer ve = ok w2 ->
validw (emem s) (w1 + w2)%R ws.

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

End Safety_conditions.



