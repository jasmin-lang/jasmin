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

Inductive safe_get_var : estate -> var -> Prop := 
| SLvar s v :
   is_lvar v ->
   ~~ wdb || is_defined (evm s).[gv v] ->
   safe_get_var s (gv v)
| Sglobal pd s v :
   not (is_lvar v) ->
   get_global_value gd (gv v) <> None ->
   ty_pexpr pd (Pvar v) = ok (v.(gv).(v_var).(vtype)) -> 
   safe_get_var s (gv v).

Inductive safe_expr : estate -> pexpr -> Prop :=
| Sconst s z :
   safe_expr s (Pconst z)
| Sbool s b :
   safe_expr s (Pbool b)
| Sarr_init s n :
   safe_expr s (Parr_init n)
| Svar_lvar s v :
   is_lvar v ->
   ~~ wdb || is_defined (evm s).[gv v] ->
   safe_expr s (Pvar v)
| Svar_global pd s v :
   not (is_lvar v) ->
   get_global_value gd (gv v) <> None ->
   ty_pexpr pd (Pvar v) = ok (v.(gv).(v_var).(vtype)) -> 
   safe_expr s (Pvar v)
(* pos will be array size *)
| Sget s pd aa ws x e i pos:
   safe_get_var s (gv x) ->
   safe_expr s e ->
   ty_get_set ty_pexpr pd ws x e = ok (sword ws) ->
   sem_pexpr false gd s e = ok (Vint i) ->
   is_align (i * mk_scale aa ws)%Z ws ->
   WArray.in_range pos (i * mk_scale aa ws)%Z ws ->
   safe_expr s (Pget aa ws x e)
(* pos will be obtained from vm *)
| Ssub pd s aa ws len x e i pos:
   safe_get_var s (gv x) ->
   safe_expr s e ->
   ty_get_set_sub ty_pexpr pd ws len x e = 
     ok (sarr (Z.to_pos (wsize_size ws) * len)) ->
   sem_pexpr false gd s e = ok (Vint i) ->
   (0 <=? (i * mk_scale aa ws))%Z && ((i * mk_scale aa ws + arr_size ws len) <=? pos)%Z ->
   safe_expr s (Psub aa ws len x e)
(* Fix me *)
| Sload pd s ws x e vx t i:
   ty_load_store ty_pexpr pd ws x e = ok (sword ws) ->
   (~~ wdb || is_defined (evm s).[v_var x]) ->
   get_var wdb s.(evm) x = ok vx ->
   vx <>  Vundef (sword ws) t ->
   safe_expr s e ->
   sem_pexpr false gd s e = ok (Vint i) ->
   (*validw (emem s) (w1 + w2)%R sz*)
   safe_expr s (Pload ws x e)
| Sapp1 pd s o e te:
   safe_expr s e ->
   check_expr ty_pexpr pd e (type_of_op1 o).1 = ok te ->
   safe_expr s (Papp1 o e)
(* Fix me *)
| Sapp2 s o e1 e2 pd te1 te2:
   safe_expr s e1 ->
   safe_expr s e2 ->
   check_expr ty_pexpr pd e1 (type_of_op2 o).1.1 = ok te1 ->
   check_expr ty_pexpr pd e2 (type_of_op2 o).1.1 = ok te2 ->
   safe_expr s (Papp2 o e1 e2)
(* Fix me *)
| SappN s o es pd tes:
   check_pexprs ty_pexpr pd es (type_of_opN o).1 = ok tes ->
   safe_expr s (PappN o es)
| Sif s pd ty b et ef tb tet tef:
   check_expr ty_pexpr pd b sbool = ok tb ->
   check_expr ty_pexpr pd et ty = ok tet ->
   check_expr ty_pexpr pd ef ty = ok tef -> 
   safe_expr s b ->
   safe_expr s et ->
   safe_expr s ef ->
   safe_expr s (Pif ty b et ef).

   

