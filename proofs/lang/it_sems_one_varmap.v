(** Semantics of the “one-varmap” intermediate language.
*)
From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState.
Import Basics.Monads.

Require psem one_varmap sem_one_varmap it_sems_core.
Import Utf8.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Export one_varmap sem_one_varmap.
Import psem it_sems_core var.
Import low_memory.

Local Unset Elimination Schemes.

Import MonadNotation.
Local Open Scope monad_scope.

(** Semantics of programs in which there is a single scope for local variables.
Function arguments and returns are passed by name:
the caller puts the arguments in the right variables and read them from the right variables.

Also the instructions may be annotated with variables that are known to be free:
this semantics explicitly kills these variables before executing the corresponding instruction.

The semantics also ensures some properties:

 - No for loop
 - Calls to “rastack” functions are annotated with free variables
 - The sp_rsp local variable always hold the pointer to the top of the stack
 - The sp_rip local variable is assumed to hold the pointer to the static global data
 - The var_tmp a set of local variables free at the beginning of export functions

The semantic predicates are indexed by a set of variables which is *precisely* the set of variables that are written during the execution.
 *)

#[local] Existing Instance withsubword.
#[local] Existing Instance progStack.
#[local] Existing Instance noassert.

Section SEM.

Context
  {asm_op syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {ovm_i : one_varmap_info}.

Section SEM_C.

Context {E E0} {wE : with_Error E E0}
        (sem_i: sprog -> instr -> estate -> itree E (Sv.t * estate))
        (p : prog).

(* folding instruction semantics on commands *)

(*
Definition isem_foldr (c: cmd) : estate -> itree E (Sv.t * estate) :=
  foldr (fun i k s => s' <- sem_i p ev i s.2 ;; k (Sv.union s.1 s'.1, s'.2))
        (fun s => Ret (Sv.empty, s)) c.
*)
(*
Fixpoint isem_cmd_ (c: cmd) : estate -> itree E (Sv.t * estate) :=
  fun s =>
   match c with
   | [::] => Ret (Sv.empty, s)
   | i :: c => ks <- sem_i p ev i s;; ks' <- isem_cmd_ c ks.2;; Ret (Sv.union ks.1 ks'.1, ks'.2)
   end.
*)

Fixpoint isem_cmd_ (c: cmd) : Sv.t * estate -> itree E (Sv.t * estate) :=
  fun ks =>
   match c with
   | [::] => Ret ks
   | i :: c => ks' <- sem_i p i ks.2;; isem_cmd_ c (Sv.union ks.1 ks'.1, ks'.2)
   end.

(* Make global definition *)
Local Notation continue_loop s := (ret (inl s)).
Local Notation exit_loop s := (ret (inr s)).

Definition isem_while_round (c1 : cmd) (e : pexpr) (c2 : cmd) (s : Sv.t * estate) :
    itree E (Sv.t * estate + Sv.t * estate) :=
  s <- isem_cmd_ c1 s;;
  b <- isem_cond p e s.2;;
  if b then s <- isem_cmd_ c2 s;; continue_loop s
  else exit_loop s.

Definition isem_while_loop (c1 : cmd) (e:pexpr) (c2: cmd) (s : Sv.t * estate) :
    itree E (Sv.t * estate) :=
  ITree.iter (isem_while_round c1 e c2) s.

End SEM_C.

Definition sem_syscall (p : prog) (o : syscall_t) (s : estate) :=
  Let ves := get_vars true s.(evm) (syscall_sig o).(scs_vin) in
  Let fs := fexec_syscall (scP:= sCP_stack) o (mk_fstate ves s) in
  let s:= with_vm s (vm_after_syscall s.(evm)) in
  upd_estate true (p_globs p) (to_lvals (syscall_sig o).(scs_vout)) fs s.

Notation add_fv fv :=
  (Result.map (aT:=estate) (rT:=Sv.t * estate) (fun (s:estate) => (fv, s))).

(* semantics of instructions, abstracting on function calls (through
   sem_fun) *)

Variant recCallK : Type -> Type :=
 | RecCallK (f:funname) (fs: estate) : recCallK (Sv.t * estate).

Class sem_FunK (E : Type -> Type) :=
  { sem_funK : sprog -> funname -> estate -> itree E (Sv.t * estate) }.

(* recCall trigger *)
Definition rec_callK {E : Type -> Type} (f : funname) (fs : estate) :
   itree (recCallK +' E) (Sv.t * estate) :=
  trigger_inl1 (RecCallK f fs).

#[global]
Instance sem_funK_rec (E : Type -> Type) : sem_FunK (recCallK +' E) | 0 :=
  {| sem_funK := fun _ => rec_callK (E:=E) |}.

Context (var_tmp : Sv.t).

Section SEM_I.

Context {E E0} {wE : with_Error E E0} {sem_F : sem_FunK E}.

Fixpoint isem_i(p : sprog) (i : instr) (s : estate) :
    itree E (Sv.t * estate) :=
  let: (MkI ii i) := i in
  ks <- isem_ir p i s;;
  _ <- iresult (ks.2) (assert (is_stack_stable (emem s) (emem ks.2) && disjoint ks.1 (magic_variables p)) ErrSemUndef);;
  Ret ks
with isem_ir (p : sprog) (i : instr_r) (s : estate) : itree E (Sv.t * estate) :=
  match i with
  | Cassgn x tg ty e => iresult s (add_fv (vrv x) (sem_assgn p x tg ty e s))

  | Copn xs tg o es => iresult s (add_fv (vrvs xs) (sem_sopn (p_globs p) o s xs es))

  | Csyscall xs o es =>
    let fv := Sv.union syscall_kill (vrvs (to_lvals (syscall_sig o).(scs_vout))) in
    iresult s (add_fv fv (sem_syscall p o s))

  | Cif e c1 c2 =>
    b <- isem_cond p e s;;
    isem_cmd_ isem_i p (if b then c1 else c2) (Sv.empty, s)

  | Cwhile a c1 e i c2 =>
    isem_while_loop isem_i p c1 e c2 (Sv.empty, s)

  | Ccall xs fn args =>
    let fi := s in
    fs <- sem_funK p fn fi;;
    Ret (Sv.union fs.1 (fd_tmp_call p fn), kill_tmp_call p fn fs.2)

  | Cassert _ => Exception.throw (ErrSemUndef, tt)
  | Cfor _ _ _ => Exception.throw (ErrSemUndef, tt)
  end.

Definition isem_cmd (p:sprog) c s :=
  isem_cmd_ isem_i p c (Sv.empty, s).

Let vrsp (p:sprog) : var := vid p.(p_extra).(sp_rsp).

Definition valid_RSP p m vm :=
  value_eqb vm.[vrsp p] (Vword (top_stack m)).

Definition initialize_funcall (p:sprog) f (fs:estate) :=
 Let _ := assert (top_stack_aligned f fs.(emem) &&
                  valid_RSP p fs.(emem) fs.(evm)) ErrSemUndef in
 Let m1 :=
   alloc_stack fs.(emem)
      f.(f_extra).(sf_align)
      f.(f_extra).(sf_stk_sz)
      f.(f_extra).(sf_stk_ioff)
      f.(f_extra).(sf_stk_extra_sz) in
 let vm1 := ra_undef_vm f fs.(evm) var_tmp in
 ok {| escs := fs.(escs); emem := m1; evm := set_RSP p m1 vm1; |}.

Definition finalize_funcall p f ks2 :=
  let (k, s2') := (ks2.1, ks2.2) in
  Let _ := assert [&& ra_valid p f k
                    , saved_stack_valid p f k
                    & valid_RSP p s2'.(emem) s2'.(evm)] ErrSemUndef in
  let m2 := free_stack s2'.(emem) in
  let vm2 := kill_vars (ra_vm_return f.(f_extra)) s2'.(evm) in
  let s2 := {| escs := s2'.(escs); emem := m2 ; evm := set_RSP p m2 vm2 |} in
  let k' := Sv.union (ra_undef f var_tmp) (ra_vm_return f.(f_extra)) in
  ok (Sv.union k k', s2).

Definition isem_fun_body (p : prog)
   (fn : funname) (fs : estate) :=
   fd <- ioget (ErrType, tt) (get_fundef (p_funcs p) fn);;
   s1 <- iresult fs (initialize_funcall p fd fs);;
   ks2 <- isem_cmd p fd.(f_body) s1;;
   ks3 <- iresult ks2.2 (finalize_funcall p fd ks2);;
   _ <- iresult ks3.2 (assert (is_stack_stable (emem fs) (emem ks3.2)) ErrSemUndef);;
   Ret ks3.

End SEM_I.

(* semantics of instructions parametrized by recCall events *)

Section REC.
Context {E E0} {wE : with_Error E E0}.

Definition isem_ir_rec (p : sprog) (i : instr_r) (s : estate)
  : itree (recCallK +' E) (Sv.t * estate) :=
  isem_ir (sem_F := sem_funK_rec E) p i s.

Definition isem_i_rec (p : sprog) (i : instr) (s : estate)
  : itree (recCallK +' E) (Sv.t * estate) :=
  isem_i (sem_F := sem_funK_rec E) p i s.

(* similar, for commands *)
Definition isem_cmd_rec (p : sprog) (c : cmd) (s : estate)
  : itree (recCallK +' E) (Sv.t * estate) :=
  isem_cmd (sem_F := sem_funK_rec E) p c s.

(* similar, for function calls *)
Definition isem_fun_rec (p : sprog)
   (fn : funname) (fs : estate) : itree (recCallK +' E) (Sv.t * estate) :=
  isem_fun_body (sem_F := sem_funK_rec E) p fn fs.

(* handler of recCallK events *)
Definition handle_recCallK {sem_F : funname -> sem_FunK (recCallK +' E)}
  (p : sprog) :
   recCallK ~> itree (recCallK +' E) :=
 fun T (rc : recCallK T) =>
   match rc with
   | RecCallK fn fs => isem_fun_body (sem_F:=sem_F fn) p fn fs
   end.

(* intepreter of recCall events for functions, giving us the recursive
   semantics of functions *)
Definition isem_fun_def {sem_F : funname -> sem_FunK (recCallK +' E)} (p : sprog) (fn : funname) (fs : estate) : itree E (Sv.t * estate) :=
  mrec (handle_recCallK (sem_F := sem_F) p) (RecCallK fn fs).

Definition isem_fun := isem_fun_def (sem_F := fun _ => sem_funK_rec E).

#[global]
Instance sem_fun_full : sem_FunK E | 100 :=
  {| sem_funK := fun p => isem_fun p |}.

Definition isem_cmd_full (p : prog) (c : cmd) (s : estate) : itree E (Sv.t * estate) :=
  isem_cmd (sem_F := sem_fun_full) p c s.

Definition isem_exportcall (p:sprog) (gd: @extra_val_t progStack) fn (s:estate) :=
  fd <-ioget (ErrType, tt) (get_fundef p.(p_funcs) fn);;
  let vrsp : var := vid p.(p_extra).(sp_rsp) in
  let vgd : var := vid p.(p_extra).(sp_rip) in
  let vm := s.(evm) in
  _ <- iresult s (assert [&& is_RAnone fd.(f_extra).(sf_return_address)
                           , disjoint (sv_of_list fst fd.(f_extra).(sf_to_save)) (sv_of_list v_var fd.(f_res))
                           , ~~ Sv.mem vrsp (sv_of_list v_var fd.(f_res))
                           & value_eqb vm.[vgd] (Vword gd)]
                          ErrSemUndef);;
  ks2 <- isem_fun p fn s;;
  let (k, s2) := (ks2.1, ks2.2) in
  _ <- iresult s2 (assert (Sv.subset (Sv.inter callee_saved (Sv.union k (ra_undef fd var_tmp)))
                                     (sv_of_list fst fd.(f_extra).(sf_to_save)))
                      ErrSemUndef);;
  Ret s2.

End REC.

End SEM.
