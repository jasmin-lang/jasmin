(* ** Imports and settings *)
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrfun ssrbool.
Require Import expr compiler_util allocation.

Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "inlining".

  Definition inline_error msg := {|
    pel_msg := msg;
    pel_fn := None;
    pel_fi := None;
    pel_ii := None;
    pel_vi := None;
    pel_pass := Some pass;
    pel_internal := true
  |}.

End E.

(* ** inlining
 * -------------------------------------------------------------------- *)

Section INLINE.

Context
  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {asmop: asmOp asm_op}
  (rename_fd : instr_info -> funname -> ufundef -> ufundef)
  (dead_vars_fd : ufun_decl -> instr_info -> Sv.t)
.

Definition get_flag (x:lval) flag :=
  match x with
  | Lvar x => if is_inline_var x then AT_inline else flag
  | _      => flag
  end.

Definition assgn_tuple iinfo (xs:lvals) flag (tys:seq stype) (es:pexprs) :=
  let assgn xe := MkI iinfo (Cassgn xe.1 (get_flag xe.1 flag) xe.2.1 xe.2.2) in
  map assgn (zip xs (zip tys es)).

Definition inline_c (inline_i: instr -> Sv.t -> cexec (Sv.t * cmd)) c s :=
  foldr (fun i r =>
    Let r := r in
    Let ri := inline_i i r.1 in
    ok (ri.1, ri.2 ++ r.2)) (ok (s,[::])) c.

Definition sparams (fd:ufundef) :=
  vrvs_rec Sv.empty (map Lvar fd.(f_params)).

Definition locals_p (fd:ufundef) :=
  let s := read_es (map Plvar fd.(f_res)) in
  let w := write_c_rec s fd.(f_body) in
  let r := read_c_rec w fd.(f_body) in
  vrvs_rec r (map Lvar fd.(f_params)).

Definition locals fd :=
  Sv.diff (locals_p fd) (sparams fd).

Definition check_rename f (fd1 fd2:ufundef) (s:Sv.t) :=
  Let _ := check_ufundef dead_vars_fd tt tt (f,fd1) (f,fd2) tt in
  let s2 := locals_p fd2 in
  if disjoint s s2 then ok tt
  else Error (inline_error (pp_s "invalid refreshing in function")).

Definition get_fun (p:ufun_decls) (f:funname) :=
  match get_fundef p f with
  | Some fd => ok fd
  | None    => Error (inline_error (pp_box [::pp_s "Unknown function"; PPEfunname f]))
  end.

Print read_i_rec.

Fixpoint inline_i (px: ufun_decls) (i:instr) (X:Sv.t) : cexec (Sv.t * cmd) :=
  let '(MkI iinfo ir) := i in
  match ir with
  | Cassgn _ _ _ _
  | Copn _ _ _ _
  | Csyscall _ _ _
    => ok (Sv.union (read_i ir) X, [::i])
  | Cif e c1 c2  =>
    Let c1 := inline_c (inline_i px) c1 X in
    Let c2 := inline_c (inline_i px) c2 X in
    ok (read_e_rec (Sv.union c1.1 c2.1) e, [::MkI iinfo (Cif e c1.2 c2.2)])
  | Cfor x (d,lo,hi) c =>
    let X := Sv.union (read_i ir) X in
    Let c := inline_c (inline_i px) c X in
    ok (X, [::MkI iinfo (Cfor x (d, lo, hi) c.2)])
  | Cwhile a c e info c' =>
    let X := Sv.union (read_i ir) X in
    Let c := inline_c (inline_i px) c X in
    Let c' := inline_c (inline_i px) c' X in
    ok (X, [::MkI iinfo (Cwhile a c.2 e info c'.2)])
  | Ccall xs f es =>
    let X := Sv.union (read_i ir) X in
    if ii_is_inline iinfo then
      Let fd := add_iinfo iinfo (get_fun px f) in
      let fd' := rename_fd iinfo f fd in
      Let _ := add_iinfo iinfo (check_rename f fd fd' (Sv.union (vrvs xs) X)) in
      let ii := ii_with_location iinfo in
      let rename_args :=
        assgn_tuple ii (map Lvar fd'.(f_params)) AT_rename fd'.(f_tyin) es
      in
      let rename_res :=
        assgn_tuple ii xs AT_rename fd'.(f_tyout) (map Plvar fd'.(f_res))
      in
      ok (X, rename_args ++ fd'.(f_body) ++ rename_res)
    else ok (X, [::i])
  end.

Definition inline_fd (p:ufun_decls) (fd:ufundef) :=
  match fd with
  | MkFun ii tyin params c tyout res ef =>
    let s := read_es (map Plvar res) in
    Let c := inline_c (inline_i p) c s in
    ok (MkFun ii tyin params c.2 tyout res ef)
  end.

Definition inline_fd_cons (ffd:funname * ufundef) (p:cexec ufun_decls) :=
  Let p := p in
  let f := ffd.1 in
  Let fd := add_funname f (add_finfo ffd.2.(f_info) (inline_fd p ffd.2)) in
  ok ((f,fd):: p).

Definition inline_prog (p:ufun_decls) :=
  foldr inline_fd_cons (ok [::]) p.

Definition inline_prog_err (p:uprog) :=
  if uniq [seq x.1 | x <- p_funcs p] then
    Let fds := inline_prog (p_funcs p) in
    ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := fds |}
  else Error (inline_error (pp_s "two function declarations with the same name")).

End INLINE.

(*******************************************************)

From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState.
Import Basics.Monads.

Require Import it_sems_coreI2.
Require Import inline_lemmaI2.

Require Import expr psem_defs psem_core it_exec tfam_iso.


Section IT_section.

Context
  {asm_op: Type}
  {wsw: WithSubWord}
  {dc: DirectCall}
  {syscall_state : Type}
  {ep : EstateParams syscall_state}
  {spp : SemPexprParams}
  {sip : SemInstrParams asm_op syscall_state}
  {pT : progT}
  {scP : semCallParams}.

Section IT1_section.

Context {E E0} {wE : with_Error E E0}
  (iiT : instr_info -> bool) (p : prog) (ev : extra_val_t).

(*
Context
(*  {wsw : WithSubWord}
  {asm_op syscall_state : Type}
  {asmop:asmOp asm_op} *)
  (rename_fd : instr_info -> funname -> ufundef -> ufundef)
  (de ad_vars_fd : ufun_decl -> instr_info -> Sv.t)
.
*)

Notation recCall A := (callE (A * funname * fstate) fstate).

(* extract the inlining tag from the call *)
Definition inline_RC T (e: recCall bool T) : bool :=
  match e with
  | Call (true, _, _) => true
  | _ => false end.

(* inline call, defined as a sigma type (use a variant instead?) *)
Definition RC1 : Type -> Type :=
  fun T => sigT (fun e: recCall bool T => (inline_RC e = true)).

(* non-inline call *)
Definition RC2 : Type -> Type :=
  fun T => sigT (fun e: recCall bool T => (inline_RC e = false)).

(* conversion of recCall to RC1 + RC2, assuming the tagging is done *)
Lemma split_recCall T : recCall bool T -> (RC1 +' RC2) T.
  intro e.
  destruct e as [[[[ | ] fn] fs]] eqn: was_e.
  - left; exists e.
    inv was_e; auto.
  - right; exists e.
    inv was_e; auto.  
Defined.

(* lifts the splitting to all events *)
Lemma split_Evs {E1: Type -> Type} T :
  (recCall bool +' E1) T -> ((RC1 +' RC2) +' E1) T. 
  intro e.
  destruct e as [d | e].
  - left; eapply split_recCall; auto.
  - right; auto.
Defined.    

(* translate the instruction itree to a split one *)
Definition isem_i_split (iiT: instr_info -> bool)
  (p : prog) (ev : extra_val_t) (i : instr) (s : estate) :
  itree ((RC1 +' RC2) +' E) estate :=
  translate (@split_Evs E) (isem_i_rec iiT p ev i s).

(* translate the command itree to a split one *)
Definition isem_cmd_split (iiT: instr_info -> bool)
  (p : prog) (ev : extra_val_t) (c : cmd) (s : estate) :
  itree ((RC1 +' RC2) +' E) estate :=
  translate (@split_Evs E) (isem_cmd_rec iiT p ev c s).

(* translate the function itree to a split one *)
Definition isem_fun_split (iiT: instr_info -> bool)
  (p : prog) (ev : extra_val_t) (fn : funname) (fs: fstate) :
  itree ((RC1 +' RC2) +' E) fstate :=
  translate (@split_Evs E) (isem_fun_rec iiT p ev fn fs).

Definition rassoc_tr E1 E2 E3 :
  ((E1 +' E2) +' E3) ~> (E1 +' (E2 +' E3)) :=
  @mfun2 (E1 +' (E2 +' E3)) ((E1 +' E2) +' E3) (@FIsoLAssoc E1 E2 E3).

Definition perm_rassoc_tr E1 E2 E3 :
  ((E1 +' E2) +' E3) ~> (E2 +' (E1 +' E3)) :=
  fun T e => match e with 
  | inl1 e12 => match e12 with
                | inl1 e1 => inr1 (inl1 e1)
                | inr1 e2 => inl1 e2 end
  | inr1 e3 => inr1 (inr1 e3) end.                


Definition recCall2RC1 : recCall bool ~> RC1 :=
  fun T e => match e with
             | Call (_, fn, fs) =>
                exist _ (Call (true, fn, fs)) eq_refl end.                

Definition recCall2RC2 : recCall bool ~> RC2 :=
  fun T e => match e with
             | Call (_, fn, fs) =>
                exist _ (Call (false, fn, fs)) eq_refl end.                

Definition transl_ext {E0 E1: Type -> Type} (E2: Type -> Type)
  (f: E0 ~> E1) : E0 +' E2 ~> E1 +' E2 :=
  fun T e => match e with
             | inl1 e1 => inl1 (f _ e1)
             | inr1 e2 => inr1 e2 end.                   

Definition recCall2RC2x E0 : recCall bool +' E0 ~> RC2 +' E0 :=
  transl_ext recCall2RC2.

(* non-recusive inline handler (ctxI) *)
Definition handle_inline_RC1 : RC1 ~> itree (RC2 +' E).
  intros T e.
  destruct e as [e1 e_eq] eqn: was_e.
  destruct e1 as [[[[ | ] fn] fs]]; try discriminate.
  set (it := isem_fun_rec iiT p ev fn fs).  
  exact (translate (@recCall2RC2x E) it).
Defined.  

Definition handle_inline_recCall_ext :
  (RC1 +' (RC2 +' E)) ~> itree (RC2 +' E) :=
  fun T e => ext_handler handle_inline_RC1 e.
(*  fun T e => match e with
             | inl1 e1 => handle_inline_RC1 e1
             | inr1 e2 => trigger e2 end.                  
*)  

Definition inlining T (it: itree ((RC1 +' RC2) +' E) T) :
  itree (RC2 +' E) T := D1_ext_interp handle_inline_RC1 it.

Definition inlining_ext T (it: itree ((RC1 +' RC2) +' E) T) :
  itree ((RC1 +' RC2) +' E) T :=
  translate (@lw_la RC1 RC2 E) (@inlining T it).

(* old ctxR *)
Definition ctxR : (* (p : prog) (ev : extra_val_t) : *)
  RC2 ~> itree (RC2 +' (RC1 +' E)).
  intros T e.
  destruct e as [e2 e_eq] eqn: was_e.
  destruct e2 as [[[b fn] fs]].
  exact (translate (@perm_rassoc_tr _ _ _) (isem_fun_split iiT p ev fn fs)).
Defined.

(* new ctxR *)
Definition handle_rec_RC2 : (* (p : prog) (ev : extra_val_t) : *)
  RC2 ~> itree (RC2 +' E).
  intros T e.
  destruct e as [e2 e_eq] eqn: was_e.
  destruct e2 as [[[b fn] fs]].
  set (it := isem_fun_rec iiT p ev fn fs).
  exact (translate (@recCall2RC2x E) it).
Defined.  

(* ctxIR *)
Definition RC12_handler : RC1 +' RC2 ~> itree ((RC1 +' RC2) +' E) :=
  fun T e => joint_handler handle_inline_RC1 handle_rec_RC2 e.

(* the split semantics *)
Definition split_isem T (t: itree ((RC1 +' RC2) +' E) T) : itree E T :=
  interp_mrec RC12_handler t.

End IT1_section.

Section IT1_section.

Context {E E0} {wE : with_Error E E0}
  (iiT : instr_info -> bool) (p : prog) (ev : extra_val_t).

Lemma inline_correct T (t: itree ((RC1 +' RC2) +' E) T) :
  eutt eq (split_isem iiT p ev (inlining_ext iiT p ev t))
          (split_isem iiT p ev t).
Proof.
  eapply (@OK_inline_lemma RC1 RC2 E (handle_inline_RC1 iiT p ev)
          (handle_rec_RC2 iiT p ev) _ t).
Qed.


(** TO PROVE *)

Notation recCall A := (callE (A * funname * fstate) fstate).

Definition faithful_recCall_split (f: recCall bool ~> RC1 +' RC2) :=
  forall T (e: recCall bool T),
    (f T e = inl1 (recCall2RC1 e)) \/ (f T e = inr1 (recCall2RC2 e)).   

Lemma split_correct f (F: faithful_recCall_split f)
    T (t: itree (recCall bool +' E) T) :
  eutt eq (interp_mrec (handle_recCall iiT p ev) t)
          (split_isem iiT p ev (translate (transl_ext f) t)).
Admitted. 


(*
TODO

eutt eq (void_sem (inline_pass f)) (inlining_ext iiT p ev t)

*)
  

(*    
  :=
 fun T (rc : RC2 T) =>
   match rc with
   | existT (RecCall _ fn fs) _  =>
       translate (@perm_rassoc_tr _ _ _) (isem_fun_INLN iiT p ev fn fs)
   end.
*)

(**********)



Fixpoint isem_i_body  (err: error_data) (iiT: instr_info -> bool) (p : prog) (ev : extra_val_t)
  (i : instr) (s : estate) : itree (recCall +' E) estate :=
  let: (MkI ii i') := i in
  let ssem := isem_i_rec iiT p ev i s in
  match i' with
  | Ccall xs fn args =>
      match (iiT ii) with
      | false => ssem
      | true =>              
    
  | Cassgn _ _ _ _ => ssem
  | Copn _ _ _ _ => ssem
  | Csyscall _ _ _ => ssem
  | Cif _ _ _ => ssem 
  | 
                                   
   | _ => throw err end.
                               

  | Copn xs tg o es => iresult s (sem_sopn (p_globs p) o s xs es)

  | Csyscall xs o es => iresult s (sem_syscall p xs o es s)

  | _ => throw err end.
                                
  | Cif e c1 c2 => 
    b <- isem_cond p e s;;
    isem_foldr (isem_i_body iiT) p ev (if b then c1 else c2) s

  | Cwhile a c1 e i c2 =>
    isem_while_loop (isem_i_body iiT) p ev c1 e c2 s

  | Cfor i (d, lo, hi) c =>
    bounds <- isem_bound p lo hi s;;
    isem_for_loop (isem_i_body iiT) p ev i c (wrange d bounds.1 bounds.2) s

  | Ccall xs fn args =>
    vargs <- isem_pexprs  (~~direct_call) (p_globs p) args s;;
    fs <- sem_fun p ev (iiT ii) fn (mk_fstate vargs s) ;;
    iresult s (upd_estate (~~direct_call) (p_globs p) xs fs s)
  end.




Definition RC1 : Type -> Type := fun T (e: recCall T) => match e with
                                                         | RecCall true _ _ => True
                                                         | _ => False end.                        


Definition mark_inline (p : prog) (ev : extra_val_t) (i : instr) (s : estate) 


Fixpoint mark_inline (px: ufun_decls) (i: instr) (s: estate) :
  itree E cmd :=
  let '(MkI iinfo ir) := i in
  | Cassign _ _ _ _ => isem_i p ev i s 




Fixpoint mark_inline (px: ufun_decls) (i: instr) (X: Sv.t) :
  itree E (Sv.t * cmd)%type :=
  let '(MkI iinfo ir) := i in
  match ir with
  | Cassgn _ _ _ _
  | Copn _ _ _ _
  | Csyscall _ _ _
    => Ret (Sv.union (read_i ir) X, [::i])
  | Cif e c1 c2  =>
    Let c1 := inline_c (inline_i px) c1 X in
    Let c2 := inline_c (inline_i px) c2 X in
    ok (read_e_rec (Sv.union c1.1 c2.1) e, [::MkI iinfo (Cif e c1.2 c2.2)])
  | Cfor x (d,lo,hi) c =>
    let X := Sv.union (read_i ir) X in
    Let c := inline_c (inline_i px) c X in
    ok (X, [::MkI iinfo (Cfor x (d, lo, hi) c.2)])
  | Cwhile a c e info c' =>
    let X := Sv.union (read_i ir) X in
    Let c := inline_c (inline_i px) c X in
    Let c' := inline_c (inline_i px) c' X in
    ok (X, [::MkI iinfo (Cwhile a c.2 e info c'.2)])
  | Ccall xs f es =>
    let X := Sv.union (read_i ir) X in
    if ii_is_inline iinfo then
      Let fd := add_iinfo iinfo (get_fun px f) in
      let fd' := rename_fd iinfo f fd in
      Let _ := add_iinfo iinfo (check_rename f fd fd' (Sv.union (vrvs xs) X)) in
      let ii := ii_with_location iinfo in
      let rename_args :=
        assgn_tuple ii (map Lvar fd'.(f_params)) AT_rename fd'.(f_tyin) es
      in
      let rename_res :=
        assgn_tuple ii xs AT_rename fd'.(f_tyout) (map Plvar fd'.(f_res))
      in
      ok (X, rename_args ++ fd'.(f_body) ++ rename_res)
    else ok (X, [::i])
  end.
  


End IT_section.
  
End INLINE.
