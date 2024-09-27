(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
Require Import xseq.
Require Export array type expr gen_map low_memory warray_ sem_type sem_op_typed values varmap low_memory syscall_sem.
Require Export
  flag_combination
  sem_params.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Local Open Scope seq_scope.
Open Scope vm_scope.

(* ** Parameter expressions
 * -------------------------------------------------------------------- *)

Section SEM_OP.
Context {abst: Tabstract}.

Definition sem_sop1 (o: sop1) (v: value) : exec value :=
  let t := type_of_op1 o in
  Let x := of_val _ v in
  ok (to_val (sem_sop1_typed o x)).

Definition sem_sop2 (o: sop2) (v1 v2: value) : exec value :=
  let t := type_of_op2 o in
  Let x1 := of_val _ v1 in
  Let x2 := of_val _ v2 in
  Let r  := sem_sop2_typed o x1 x2 in
  ok (to_val r).

Definition sem_opN
  {cfcd : FlagCombinationParams} (op: opN) (vs: values) : exec value :=
  Let w := app_sopn (@sem_opN_typed _ cfcd op) vs in
  ok (to_val w).

Definition sem_opNA
  {cfcd : FlagCombinationParams} {absp: Prabstract} (op: opNA) (vs: values) : exec value :=
  Let w := app_sopn (@sem_opNA_typed _ cfcd _ op) vs in
  ok (to_val w).

End SEM_OP.

(* ** Global access
 * -------------------------------------------------------------------- *)

Section GLOBAL_ACCESS.
Context {abst: Tabstract}.

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

End GLOBAL_ACCESS.

Section WSW.
Context {abst: Tabstract}.
Context {wsw:WithSubWord}.

(* ** State
 * ------------------------------------------------------------------------- *)

Definition contracts_trace := seq (annotation_kind * bool).

Record estate
  {syscall_state : Type}
  {ep : EstateParams syscall_state} := Estate
  {
    escs : syscall_state;
    emem : mem;
    evm  : Vm.t;
    eassert : contracts_trace; (* assertion in reverse order *)
  }.

Arguments Estate {syscall_state}%type_scope {ep} _ _ _%vm_scope.

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
  (@on_arr_var _ (get_var wdb s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Notation "'Let' ( n , t ) ':=' wdb ',' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar wdb gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0).

Section ESTATE_UTILS.

Context
  {syscall_state : Type}
  {ep : EstateParams syscall_state}.

Definition with_vm (s:estate) vm :=
  {| escs := s.(escs); emem := s.(emem); evm := vm; eassert := s.(eassert) |}.

Definition with_mem (s:estate) m :=
  {| escs := s.(escs); emem := m; evm := s.(evm); eassert := s.(eassert) |}.

Definition with_scs (s:estate) scs :=
  {| escs := scs; emem := s.(emem); evm := s.(evm); eassert := s.(eassert) |}.

Definition with_eassert (s:estate) (a:contracts_trace) :=
   {| escs := s.(escs); emem := s.(emem); evm := s.(evm); eassert := a |}.

Definition add_contract (s:estate) (a:annotation_kind * bool) :=
  with_eassert s (a::s.(eassert)).

Definition add_contracts (s:estate) (a:contracts_trace) :=
  with_eassert s (a ++ s.(eassert)).

Definition add_asserts (s:estate) (bs:seq bool) := add_contracts s [seq (Assert,b) | b <- bs].
Definition add_assumes (s:estate) (bs:seq bool) := add_contracts s [seq (Assume,b) | b <- bs].

End ESTATE_UTILS.

Section SEM_PEXPR.

Context
  {absp: Prabstract}
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
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
      Let w := WArray.get al aa ws t i in
      ok (Vword w)
  | Psub aa ws len x e =>
    Let (n, t) := wdb, gd, s.[x] in
    Let i := sem_pexpr s e >>= to_int in
    Let t' := WArray.get_sub aa ws len t i in
    ok (Varr t')
  | Pload al sz x e =>
    Let w1 := get_var wdb s.(evm) x >>= to_pointer in
    Let w2 := sem_pexpr s e >>= to_pointer in
    Let w  := read s.(emem) al (w1 + w2)%R sz in
    ok (@to_val _ (sword sz) w)
  | Papp1 o e1 =>
    Let v1 := sem_pexpr s e1 in
    sem_sop1 o v1
  | Papp2 o e1 e2 =>
    Let v1 := sem_pexpr s e1 in
    Let v2 := sem_pexpr s e2 in
    sem_sop2 o v1 v2
  | PappN op es =>
    Let vs := mapM (sem_pexpr s) es in
    sem_opNA op vs
  | Pif t e e1 e2 =>
    Let b  := sem_pexpr s e >>= to_bool in
    Let v1 := sem_pexpr s e1 >>= truncate_val t in
    Let v2 := sem_pexpr s e2 >>= truncate_val t in
                                    ok (if b then v1 else v2)
  | Pbig idx op x body start len =>
    Let vs   := sem_pexpr s start >>= to_int in
    Let vlen := sem_pexpr s len >>= to_int in
    Let vidx := sem_pexpr s idx in
    let l := ziota vs vlen in
    foldM (fun i acc =>
               Let s := write_var x (Vint i) s in
               Let vb := sem_pexpr s body in
               sem_sop2 op acc vb)
      vidx l
  end.

Definition sem_pexprs s :=  mapM (sem_pexpr s).

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
    Let vx := get_var wdb (evm s) x >>= to_pointer in
    Let ve := sem_pexpr s e >>= to_pointer in
    let p := (vx + ve)%R in (* should we add the size of value, i.e vx + sz * se *)
    Let w := to_word sz v in
    Let m := write s.(emem) al p w in
    ok (with_mem s m)
  | Laset al aa ws x i =>
    Let (n,t) := wdb, s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let v := to_word ws v in
    Let t := WArray.set t al aa i v in
    write_var x (@to_val _ (sarr n) t) s
  | Lasub aa ws len x i =>
    Let (n,t) := wdb, s.[x] in
    Let i := sem_pexpr s i >>= to_int in
    Let t' := to_arr (Z.to_pos (arr_size ws len)) v in
    Let t := @WArray.set_sub n aa ws len t i t' in
    write_var x (@to_val _ (sarr n) t) s
  end.

Definition write_lvals (s : estate) xs vs :=
   fold2 ErrType write_lval xs vs s.

End SEM_PEXPR.

Section EXEC_ASM.

Context {absp: Prabstract}.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {asmop : asmOp asm_op}.

Definition exec_sopn (o:sopn) (vs:values) : exec values :=
  let semi := @sopn_sem _ _ _ _ o in
  Let t := @app_sopn _ _ _ semi vs in
  ok (list_ltuple t).

Definition sem_sopn gd o m lvs args :=
  sem_pexprs true gd m args >>= exec_sopn o >>= write_lvals true gd m lvs.

End EXEC_ASM.

End WSW.

Section CONTRA.

Context
  {tabstract : Tabstract}
  {wsw:WithSubWord}
  {asm_op syscall_state : Type}
  {absp : Prabstract}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  (P : prog).

Notation gd := (p_globs P).

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

Definition dc_truncate_val {dc: DirectCall} t v :=
  if direct_call then ok v
  else truncate_val t v.

Definition sem_pre {dc: DirectCall} (scs: syscall_state) (m:mem) (fn:funname) (vargs' : values) :=
  if get_fundef (p_funcs P) fn is Some f then
    Let vargs := mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' in
    Let s := write_vars (~~direct_call) f.(f_params) vargs (Estate scs m Vm.init [::]) in
    mapM (fun (p:_ * _) => sem_pexpr true gd s p.2 >>= to_bool) f.(f_contra).(f_pre)
  else Error ErrUnknowFun.

Definition sem_post {dc: DirectCall} (scs: syscall_state) (m:mem) (fn:funname) (vargs' : values) (vres : values) :=
 if get_fundef (p_funcs P) fn is Some f then
    Let vargs := mapM2 ErrType dc_truncate_val f.(f_tyin) vargs' in
    Let s := write_vars (~~direct_call) f.(f_contra).(f_iparams) vargs (Estate scs m Vm.init [::]) in
    Let s :=  write_vars (~~direct_call) f.(f_res) vres s in
    mapM (fun (p:_ * _) => sem_pexpr true gd s p.2 >>= to_bool) f.(f_contra).(f_post)
  else Error ErrUnknowFun.

End CONTRA.

(* Just for extraction *)
Definition syscall_sem__ := @syscall_sem.exec_syscall_u.

Notation "'Let' ( n , t ) ':=' wdb ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_var wdb s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, s at level 0).

Notation "'Let' ( n , t ) ':=' wdb ',' gd ',' s '.[' v ']' 'in' body" :=
  (@on_arr_var _ (get_gvar wdb gd s.(evm) v) (fun n (t:WArray.array n) => body)) (at level 25, gd at level 0, s at level 0).

