(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import xseq.
Require Export type expr gen_map low_memory warray_ sem_type sem_op_typed values varmap low_memory syscall_sem.
Require Export
  flag_combination
  sem_params.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Open Scope vm_scope.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Definition sem_sop1 {sm : SemMode} (o: sop1) (v: value) : exec value :=
  Let x := of_val _ v in
  Let r := sem_sop1_typed o x in
  ok (to_val r).

Definition sem_sop2 {sm : SemMode} (o: sop2) (v1 v2: value) : exec value :=
  Let x1 := of_val _ v1 in
  Let x2 := of_val _ v2 in
  Let r  := sem_sop2_typed o x1 x2 in
  ok (to_val r).

Definition sem_opN
  {cfcd : FlagCombinationParams} {sm : SemMode} (op: opN) (vs: values) : exec value :=
  Let w := app_sopn _ (sem_opN_typed op) vs in
  ok (to_val w).

Definition sem_opN_safety (op: opN_safety) (vs: values) : exec bool :=
  app_sopn _ (sem_opN_safety_typed op) vs.

(* The total mode of the operators: a success of the partial mode is a
   success of the total mode, and on defined arguments the total mode fails
   only with a type error. *)
Lemma sem_sop1_partialE o v r : sem_sop1 (sm := partial) o v = ok r -> sem_sop1 (sm := total) o v = ok r.
Proof.
rewrite /sem_sop1; t_xrbindP => x hx y hy <-.
have := sem_sop1_typed_partialE hy; rewrite sem_sop1_typed_total => -[<-].
by rewrite hx.
Qed.

Lemma sem_sop2_partialE o v1 v2 r :
  sem_sop2 (sm := partial) o v1 v2 = ok r -> sem_sop2 (sm := total) o v1 v2 = ok r.
Proof.
rewrite /sem_sop2; t_xrbindP => x1 hx1 x2 hx2 y hy <-.
have := sem_sop2_typed_partialE hy; rewrite sem_sop2_typed_total => -[<-].
by rewrite hx1 /= hx2.
Qed.

Lemma sem_opN_partialE {cfcd : FlagCombinationParams} op vs r :
  sem_opN (sm := partial) op vs = ok r -> sem_opN (sm := total) op vs = ok r.
Proof. by rewrite /sem_opN /sem_opN_typed; t_xrbindP => w /mk_sem_op_partialE -> <-. Qed.

Lemma sem_sop1_total_errty o v e : is_defined v -> sem_sop1 (sm := total) o v = Error e -> e = ErrType.
Proof.
move=> hv; rewrite /sem_sop1; case hof: (of_val _ v) => [x|e'] //=.
by move=> [<-]; apply: of_val_defined_errty hv hof.
Qed.

Lemma sem_sop2_total_errty o v1 v2 e :
  is_defined v1 -> is_defined v2 -> sem_sop2 (sm := total) o v1 v2 = Error e -> e = ErrType.
Proof.
move=> hv1 hv2; rewrite /sem_sop2; case hof1: (of_val _ v1) => [x1|e'] //=;
  last by move=> [<-]; apply: of_val_defined_errty hv1 hof1.
by case hof2: (of_val _ v2) => [x2|e'] //= [<-]; apply: of_val_defined_errty hv2 hof2.
Qed.

Lemma sem_opN_total_errty {cfcd : FlagCombinationParams} op vs e :
  all is_defined vs -> sem_opN (sm := total) op vs = Error e -> e = ErrType.
Proof.
move=> hvs; rewrite /sem_opN /sem_opN_typed.
by case h: (app_sopn _ _ vs) => [w|e'] //= [<-]; exact: mk_sem_op_total_errty hvs h.
Qed.

(* ** Global access
 * -------------------------------------------------------------------- *)
Definition get_global_value (gd: glob_decls) (g: var) : option glob_value :=
  assoc gd g.

Definition gv2val (gd:glob_value) :=
  match gd with
  | Gword ws w => Vword w
  | Garr p a   => Varr a
  end.

Definition get_global gd g : exec value :=
  if get_global_value gd g is Some ga then
    let v := gv2val ga in
    if type_of_val v == eval_atype (vtype g) then ok v
    else type_error
  else type_error.

Section WSW.
Context {wsw:WithSubWord}.

(* ** State
 * ------------------------------------------------------------------------- *)

Record estate
  {syscall_state : Type}
  {ep : EstateParams syscall_state} := Estate
  {
    escs : syscall_state;
    emem : mem;
    evm  : Vm.t
  }.

Arguments Estate {syscall_state}%_type_scope {ep} _ _ _%_vm_scope.

(* ** Variable map
 * -------------------------------------------------------------------- *)

Definition get_gvar (wdb : bool) (gd : glob_decls) (vm : Vm.t) (x : gvar) :=
  if is_lvar x then get_var wdb vm x.(gv)
  else get_global gd x.(gv).

Definition get_var_is wdb vm := mapM (fun x => get_var wdb vm (v_var x)).

Definition on_arr_var A (v:exec value) (f:forall n, WArray.array n -> exec A) :=
  Let v := v  in
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.

Notation "'Let' ( n , t ) ':=' wdb ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_var wdb s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0, right associativity).

Notation "'Let' ( n , t ) ':=' wdb ',' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar wdb gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0, right associativity).

Section ESTATE_UTILS.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}.

Definition with_vm (s:estate) vm :=
  {| escs := s.(escs); emem := s.(emem); evm := vm |}.

Definition with_mem (s:estate) m :=
  {| escs := s.(escs); emem := m; evm := s.(evm) |}.

Definition with_scs (s:estate) scs :=
  {| escs := scs; emem := s.(emem); evm := s.(evm) |}.

End ESTATE_UTILS.

Section SEM_PEXPR.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sm : SemMode}
  (wdb : bool)
  (gd : glob_decls).

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec value :=
  match e with
  | Pconst z => ok (Vint z)
  | Pbool b  => ok (Vbool b)
  | Parr_init ws n =>
    let len := arr_size ws n in
    ok (Varr (WArray.empty len))
  | Pvar v => get_gvar wdb gd s.(evm) v
  | Pget al aa ws x e =>
      Let (n, t) := wdb, gd, s.[x] in
      Let i := sem_pexpr s e >>= to_int in
      Let w := WArray.get al aa ws t i in
      ok (Vword w)
  | Psub aa ws len x e =>
    Let (n, t) := wdb, gd, s.[x] in
    Let i := sem_pexpr s e >>= to_int in
    Let t' := WArray.get_sub aa ws len t i in
    ok (Varr t')
  | Pload al sz e =>
    Let w2 := sem_pexpr s e >>= to_pointer in
    Let w  := read s.(emem) al w2 sz in
    ok (@to_val (cword sz) w)
  | Papp1 o e1 =>
    Let v1 := sem_pexpr s e1 in
    sem_sop1 o v1
  | Papp2 o e1 e2 =>
    Let v1 := sem_pexpr s e1 in
    Let v2 := sem_pexpr s e2 in
    sem_sop2 o v1 v2
  | PappN op es =>
    Let vs := mapM (sem_pexpr s) es in
    sem_opN op vs
  | Pif t e e1 e2 =>
    let t := eval_atype t in
    Let b := sem_pexpr s e >>= to_bool in
    Let v1 := sem_pexpr s e1 >>= truncate_val t in
    Let v2 := sem_pexpr s e2 >>= truncate_val t in
    ok (if b then v1 else v2)
  end.

Definition sem_pexprs s := mapM (sem_pexpr s).

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var wdb s.(evm) x v in
  ok (with_vm s vm).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_none (s : estate) ty v :=
  Let _ := assert (truncatable wdb ty v) ErrType in
  Let _ := assert (DB wdb v) ErrAddrUndef in
  ok s.

Definition write_lval (l : lval) (v : value) (s : estate) : exec estate :=
  match l with
  | Lnone _ ty => write_none s (eval_atype ty) v
  | Lvar x => write_var x v s
  | Lmem al sz x e =>
    Let p := sem_pexpr s e >>= to_pointer in
    Let w := to_word sz v in
    Let m := write s.(emem) al p w in
    ok (with_mem s m)
  | Laset al aa ws x i =>
    Let (n,t) := wdb, s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word ws v in
    Let t := WArray.set t al aa i v in
    write_var x (@to_val (carr n) t) s
  | Lasub aa ws len x i =>
    Let (n,t) := wdb, s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let t' := to_arr (arr_size ws len) v in
    Let t := @WArray.set_sub sm n aa ws len t i t' in
    write_var x (@to_val (carr n) t) s
  end.

Definition write_lvals (s : estate) xs vs :=
   fold2 ErrType write_lval xs vs s.

End SEM_PEXPR.

Section SEM_EASSERT.

Context
  {wa:WithAssert}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sm : SemMode}
  (gd : glob_decls).

Fixpoint sem_eassert (s : estate) (e : eassert) : exec bool :=
  match e with
  | Pexpr e => sem_pexpr true gd s e >>= to_bool
  | PappN_safety op es =>
    Let vs := mapM (sem_pexpr true gd s) es in
    sem_opN_safety op vs
  | Pis_var_init x => ok (Vm.is_var_init (evm s) x)
  | Pis_mem_init e1 e2 =>
    Let lo := sem_pexpr true gd s e1 >>= to_pointer in
    Let sz := sem_pexpr true gd s e2 >>= to_int in
    ok (all (fun i => validr s.(emem) Unaligned (lo + wrepr Uptr i)%w U8) (ziota 0 sz))
  | Pand e1 e2 =>
    Let b1 := sem_eassert s e1 in
    Let b2 := sem_eassert s e2 in
    ok (b1 && b2)
  end.

Definition sem_assert (s : estate) (e : assertion) : exec unit :=
  Let _ := assert (assert_allowed) ErrType in
  Let b := sem_eassert s e.2 in
  Let _ := assert b (ErrAssert e.1) in
  ok tt.

End SEM_EASSERT.

Section EXEC_ASM.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asmop : asmOp asm_op}.

Definition exec_sopn {sm : SemMode} (o:sopn) (vs:values) : exec values :=
  Let semi := sopn_sem o in
  Let t := app_sopn _ semi vs in
  ok (list_ltuple t).

(* The total mode of the instructions, as for the operators. *)
Lemma exec_sopn_partialE o vs r :
  exec_sopn (sm := partial) o vs = ok r -> exec_sopn (sm := total) o vs = ok r.
Proof.
rewrite /exec_sopn /sopn_sem; t_xrbindP => semi hv <- t ht <-.
by rewrite hv /=; move: ht; rewrite /sopn_sem_ /semi => /mk_semi_partialE -> /=.
Qed.

Lemma exec_sopn_total_errty o vs e :
  all is_defined vs -> exec_sopn (sm := total) o vs = Error e -> e = ErrType.
Proof.
move=> hvs; rewrite /exec_sopn /sopn_sem /assert; case: (i_valid _) => /=; last by move=> [<-].
rewrite /sopn_sem_ /semi; case h: (app_sopn _ _ vs) => [t|e'] //= [<-].
exact: mk_semi_total_errty hvs h.
Qed.

Definition sem_sopn gd o m lvs args :=
  sem_pexprs true gd m args >>= exec_sopn o >>= write_lvals true gd m lvs.

End EXEC_ASM.

End WSW.

(* Just for extraction *)
Definition syscall_sem__ := @syscall_sem.exec_syscall_u.

Notation "'Let' ( n , t ) ':=' wdb ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_var wdb s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0, right associativity).

Notation "'Let' ( n , t ) ':=' wdb ',' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar wdb gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0, right associativity).

