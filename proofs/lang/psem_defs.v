(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import xseq.
Require Export array type expr gen_map low_memory warray_ sem_type sem_op_typed values varmap low_memory syscall_sem.
Require Export
  flag_combination
  sem_params.
Import Utf8.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Open Scope vm_scope.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Section CATCH.

Context {wc : WithCatch}.

Definition default_val (t: stype) :=
  match t with
  | sbool => Vbool false
  | sint => Vint 0
  | sarr len => Varr (WArray.fill_elem len 0%R)
  | sword sz => @Vword sz 0%R
  end.
  
Definition catch_core {T:Type} (ev : exec T) dfv : exec T :=
  match ev with
  | Ok v => ev
  | Error e => if is_ErrType e then ev else ok dfv
  end.

Notation catch ev dfv := (if with_catch then catch_core ev dfv else ev).
  
Definition sem_sop1 (o: sop1) (v: value) : exec value :=
  let t := type_of_op1 o in
  Let x := of_val _ v in
  Let r := sem_sop1_typed o x in
  ok (to_val r).

Definition sem_sop2 (o: sop2) (v1 v2: value) : exec value :=
  let t := type_of_op2 o in
  Let x1 := of_val _ v1 in
  Let x2 := of_val _ v2 in
  Let r  := sem_sop2_typed o x1 x2 in
  ok (to_val r).

Definition sem_opN
  {wa : WithAssert} {cfcd : FlagCombinationParams} (op: opN) (vs: values) : exec value :=
  Let w := app_sopn _ (sem_opN_typed op) vs in
  ok (to_val w).

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
    if type_of_val v == vtype g then ok v
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
  if is_lvar x then catch (get_var wdb vm x.(gv)) (default_val (vtype x.(gv)))
  else get_global gd x.(gv).

Definition get_var_is wdb vm := mapM (fun x => get_var wdb vm (v_var x)).

Definition on_arr_var A (v:exec value) (f:forall n, WArray.array n -> exec A) :=
  Let v := v  in
  match v with
  | Varr n t => f n t
  | _ => type_error
  end.

(* We don't catch the error here because if the is an error it is only a type error *)
Notation "'Let' ( n , t ) ':=' wdb ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_var wdb s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Notation "'Let' ( n , t ) ':=' wdb ',' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar wdb gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0).

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
  {wa : WithAssert}
  (wdb : bool)
  (gd : glob_decls).

Definition write_var (x:var_i) (v:value) (s:estate) : exec estate :=
  Let vm := set_var wdb s.(evm) x v in
  ok (with_vm s vm).

Fixpoint sem_pexpr (s:estate) (e : pexpr) : exec value :=
  match e with
  | Pconst z => ok (Vint z)
  | Pbool b  => ok (Vbool b)
  | Parr_init n => ok (Varr (WArray.empty n))
  | Pvar v => get_gvar wdb gd s.(evm) v
  | Pget al aa ws x e =>
      Let (n, t) := wdb, gd, s.[x] in
      Let i := sem_pexpr s e >>= to_int in
      Let w := catch (WArray.get al aa ws t i) 0%R in
      ok (Vword w)
  | Psub aa ws len x e =>
    Let (n, t) := wdb, gd, s.[x] in
    Let i := sem_pexpr s e >>= to_int in
    Let t' := catch (WArray.get_sub aa ws len t i) (WArray.fill_elem _ 0%R) in
    ok (Varr t')
  | Pload al sz e =>
    Let w2 := sem_pexpr s e >>= to_pointer in
    Let w  := catch (read s.(emem) al w2 sz) 0%R in
    ok (@to_val (sword sz) w)
  | Papp1 o e1 =>
    Let v1 := sem_pexpr s e1 in
    catch (sem_sop1 o v1) (default_val (type_of_op1 o).2)
  | Papp2 o e1 e2 =>
    Let v1 := sem_pexpr s e1 in
    Let v2 := sem_pexpr s e2 in
    catch (sem_sop2 o v1 v2) (default_val (type_of_op2 o).2)
  | PappN op es =>
    Let vs := mapM (sem_pexpr s) es in
    catch (sem_opN op vs) (default_val (type_of_opN op).2)
  | Pif t e e1 e2 =>
    Let b := sem_pexpr s e >>= to_bool in
    Let v1 := sem_pexpr s e1 >>= truncate_val t in
    Let v2 := sem_pexpr s e2 >>= truncate_val t in
    ok (if b then v1 else v2)
  | Pbig idx op x body start len =>
    Let _ := assert (assert_allowed) ErrType in
    Let vs   := sem_pexpr s start >>= to_int in
    Let vlen := sem_pexpr s len >>= to_int in
    Let vidx := sem_pexpr s idx >>= truncate_val ((type_of_op2 op).2) in
    let l := ziota vs vlen in
    foldM (fun i acc =>
               Let s := write_var x (Vint i) s in
               Let vb := sem_pexpr s body in
               catch (sem_sop2 op acc vb) (default_val (type_of_op2 op).2))
      vidx l
  | Pis_var_init x =>
    Let _ := assert (assert_allowed) ErrType in
    let v := (evm s).[x] in
    ok (Vbool (is_defined v))
  | Pis_mem_init e1 e2 =>
    Let _ := assert (assert_allowed) ErrType in
    Let lo := sem_pexpr s e1 >>= to_pointer in
    Let sz := sem_pexpr s e2 >>= to_int in
    let b := all (fun i => is_ok (read s.(emem) Unaligned (lo + (wrepr Uptr i))%R U8)) (ziota 0 sz) in
    ok (Vbool b)
  end.

Definition sem_pexprs s := mapM (sem_pexpr s).

Definition write_vars xs vs s :=
  fold2 ErrType write_var xs vs s.

Definition write_none (s : estate) ty v :=
  Let _ := assert (truncatable wdb ty v) ErrType in
  Let _ := assert (DB wdb v) ErrAddrUndef in
  ok s.

Definition write_lval (l : lval) (v : value) (s : estate) : exec estate :=
  match l with
  | Lnone _ ty => write_none s ty v
  | Lvar x => write_var x v s
  | Lmem al sz x e =>
    Let p := sem_pexpr s e >>= to_pointer in
    Let w := to_word sz v in
    Let m := catch (write s.(emem) al p w) s.(emem) in
    ok (with_mem s m)
  | Laset al aa ws x i =>
    Let (n,t) := wdb, s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word ws v in
    Let t := catch (WArray.set t al aa i v) t in
    write_var x (@to_val (sarr n) t) s
  | Lasub aa ws len x i =>
    Let (n,t) := wdb, s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let t' := to_arr (Z.to_pos (arr_size ws len)) v in
    Let t := catch (@WArray.set_sub n aa ws len t i t') t in
    write_var x (@to_val (sarr n) t) s
  end.

Definition write_lvals (s : estate) xs vs :=
   fold2 ErrType write_lval xs vs s.

End SEM_PEXPR.

Section EXEC_ASM.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {wa : WithAssert}
  {asmop : asmOp asm_op}.

Definition exec_sopn (o:sopn) (vs:values) : exec values :=
  catch (
    Let semi := sopn_sem o in
    Let t := app_sopn _ semi vs in
    ok (list_ltuple t))
[::].

Definition sem_sopn gd o m lvs args :=
  sem_pexprs true gd m args >>= exec_sopn o >>= write_lvals true gd m lvs.

End EXEC_ASM.

Section CONTRA.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {wa : WithAssert}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}.

Definition sem_cond (gd : glob_decls) (e : pexpr) (s : estate) : exec bool :=
  (sem_pexpr true gd s e >>= to_bool)%result.

Definition sem_assert (gd : glob_decls) (s : estate) (e : assertion) : exec unit :=
  Let _ := assert (assert_allowed) ErrType in
  Let b := sem_cond gd e.2 s in
  Let _ := assert b (ErrAssert e.1) in
  ok tt.

Record fstate := { fscs : syscall_state_t; fmem : mem; fvals : values }.

(** Switch for the semantics of function calls:
  - when false, arguments and returned values are truncated to the declared type of the called function;
  - when true, arguments and returned values are allowed to be undefined.

Informally, “direct call” means that passing arguments and returned value does not go through an assignment;
indeed, assignments truncate and fail on undefined values.
*)
Class DirectCall := {
  direct_call : bool;
}.

Definition indirect_c : DirectCall := {| direct_call := false |}.
Definition direct_c : DirectCall := {| direct_call := true |}.

Definition dc_truncate_val {dc:DirectCall} t v :=
  if direct_call then ok v
  else truncate_val t v.

Definition sem_pre {dc: DirectCall} (P : prog) (fn:funname) (fs: fstate) :=
  if ~~assert_allowed then ok tt
  else if get_fundef (p_funcs P) fn is Some f then
    match f.(f_contra) with
    | Some ci =>
      Let vargs := mapM2 ErrType dc_truncate_val f.(f_tyin) fs.(fvals) in
      Let s := write_vars (~~direct_call) ci.(f_iparams) vargs (Estate fs.(fscs) fs.(fmem) Vm.init) in
      Let _ := mapM (sem_assert (p_globs P) s) ci.(f_pre) in
      ok tt
    | None => ok tt
    end
  else Error ErrUnknowFun.

Definition sem_post {dc: DirectCall} (P : prog) (fn:funname) (vargs' : values) (fs: fstate) :=
  if ~~assert_allowed then ok tt
  else if get_fundef (p_funcs P) fn is Some f then
    match f.(f_contra) with
    | Some ci =>
      Let _ := assert (assert_allowed) ErrType in
      Let vargs := mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' in
      Let s := write_vars (~~direct_call) ci.(f_iparams) vargs (Estate fs.(fscs) fs.(fmem) Vm.init) in
      Let s :=  write_vars (~~direct_call) ci.(f_ires) fs.(fvals) s in
      Let _ := mapM (sem_assert (p_globs P) s) ci.(f_post) in
      ok tt
    | None => ok tt
    end
  else Error ErrUnknowFun.

End CONTRA.

End WSW.

End CATCH.

(* Just for extraction *)
Definition syscall_sem__ := @syscall_sem.exec_syscall_u.

Notation catch ev dfv := (if with_catch then catch_core ev dfv else ev).

Notation "'Let' ( n , t ) ':=' wdb ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_var wdb s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Notation "'Let' ( n , t ) ':=' wdb ',' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar wdb gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0).

