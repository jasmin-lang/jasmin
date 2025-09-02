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

From Paco Require Import paco.

From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState
     Eq.Paco2.

Import Basics.Monads.

Require Import it_sems_coreP xrutt xrutt_facts rutt_extras core_logics.
 (* relational_logic. *)

Require Import inline_lemmaI2.

Require Import expr psem_defs psem_core it_exec tfam_iso.

Require Import Equality.

From ITree Require Import HeterogeneousRelations.

Definition inl_ext {F1 F2} F3 (X: F1 -< F2) : F1 -< F2 +' F3 :=
  fun T y => inl1 (X T y).

Definition inr_ext {F1 F2} F3 (X: F1 -< F2) : F1 -< F3 +' F2 :=
  fun T y => inr1 (X T y).


Variant ResultSim T1 T2 (RR: T1 -> T2 -> Prop) :
    result error T1 -> result error T2 -> Type :=
  | ResultSim_error : forall e, ResultSim (Error e) (Error e)
  | ResultSim_ok : forall t1 t2, RR t1 t2 -> ResultSim (ok t1) (ok t2).            
Lemma err_result_forget_eqit b1 b2 (D1 E1: Type -> Type) (X: ErrEvent -< E1)
  (Err : error -> error_data) T1 T2 (RR: T1 -> T2 -> Prop)
  (t1: result error T1) (t2: result error T2) (H: ResultSim RR t1 t2) : 
  eqit RR b1 b2 (translate (@forget_f D1 E1)
             (@err_result ((D1 +' D1) +' E1) (inr_ext _ X) Err T1 t1))
          (@err_result (D1 +' E1) (inr_ext _ X) Err T2 t2).
Proof.
  destruct H; simpl.
  - pstep; red; simpl.
    econstructor; intro v. destruct v.
  - pstep; red; simpl.
    econstructor; auto.
Qed.    

Lemma err_result_rassoc_eqit b1 b2 (D1 E1: Type -> Type) (X: ErrEvent -< E1)
  (Err : error -> error_data) (hh: D1 ~> itree (D1 +' E1)) T1 T2 (RR: T1 -> T2 -> Prop)
  (t1: result error T1) (t2: result error T2) (H: ResultSim RR t1 t2) : 
  eqit RR b1 b2 (interp (ext_handler hh) (translate (@rassoc_tr D1 D1 E1)
          (@err_result ((D1 +' D1) +' E1) (inr_ext _ X) Err T1 t1)))
    (@err_result (D1 +' E1) (inr_ext _ X) Err T2 t2).
Proof.
  destruct H; simpl.
  - pstep; red; simpl.
    econstructor. intros v; destruct v.
  - pstep; red; simpl.
    econstructor; eauto.
Qed.    


Section REL_LOGIC.

(* pre-relation and postrelation associated with an event type *)
Class EventRels (E1 E2 : Type -> Type) :=
  { EPreRel0  : prerel E1 E2
  ; EPostRel0 : postrel E1 E2 }.

Instance EventRels_Sum {E1 E2 E3 E4: Type -> Type}
  (X1: EventRels E1 E2) (X2: EventRels E3 E4) :
  EventRels (E1 +' E3) (E2 +' E4) :=
  {| EPreRel0 := sum_prerelF EPreRel0 EPreRel0 ;
     EPostRel0 := sum_postrelF EPostRel0 EPostRel0 |}.

Definition fiso_prerel {E1 E1' E2 E2': Type -> Type}
  (X1: FIso E1' E1) (X2: FIso E2' E2) (p: prerel E1 E2) :
  prerel E1' E2' :=
     fun T1 T2 (e1 : E1' T1) (e2 : E2' T2) => p _ _ (mfun1 e1) (mfun1 e2).

Definition fiso_postrel {E1 E1' E2 E2': Type -> Type}
   (X1: FIso E1' E1) (X2: FIso E2' E2) (p: postrel E1 E2) :
  postrel E1' E2' :=
  fun T1 T2 (e1 : E1' T1) (t1: T1) (e2 : E2' T2) (t2: T2) =>
    p _ _ (mfun1 e1) t1 (mfun1 e2) t2.

Instance EventRels_FIso {E1 E1' E2 E2': Type -> Type}
   (X1: FIso E1' E1) (X2: FIso E2' E2) (Y: EventRels E1 E2) :
  EventRels E1' E2' :=
  {| EPreRel0 := fiso_prerel X1 X2 (@EPreRel0 _ _ Y) ;
     EPostRel0 := fiso_postrel X1 X2 (@EPostRel0 _ _ Y)                         
  |}.

Notation EventRels1 E := (EventRels E E).

Definition error_prerel : prerel ErrEvent ErrEvent :=
  fun _ _ _ _ => True.

Definition error_postrel : postrel ErrEvent ErrEvent :=
  fun _ _ _ _ _ _ => True.

Definition EventRels_Err : EventRels1 ErrEvent :=
  {| EPreRel0  := error_prerel ;
     EPostRel0 := error_postrel
  |}.

Definition error_x_prerel {E1 E2} (p: prerel E1 E2) :
  prerel (ErrEvent +' E1) (ErrEvent +' E2) :=
  sum_prerelF error_prerel p.

Definition error_x_postrel {E1 E2} (p: postrel E1 E2) :
  postrel (ErrEvent +' E1) (ErrEvent +' E2) :=
  sum_postrelF error_postrel p.

Instance EventRels_ErrX {E0} (X: EventRels1 E0) :
  EventRels1 (ErrEvent +' E0) :=
  {| EPreRel0  := error_x_prerel EPreRel0 ;
     EPostRel0 := error_x_postrel EPostRel0 
  |}.

Definition error_fiso_prerel {E1 E2 E3 E4}
  (X1: with_Error E1 E3) (X2: with_Error E2 E4) 
  (p: prerel E3 E4) : prerel E1 E2 :=
  fiso_prerel X1 X2 (error_x_prerel p).
  
Definition error_fiso_postrel {E1 E2 E3 E4}
  (X1: with_Error E1 E3) (X2: with_Error E2 E4) 
  (p: postrel E3 E4) : postrel E1 E2 :=
  fiso_postrel X1 X2 (error_x_postrel p).

Instance EventRels_WithError {E E0} (X: with_Error E E0) (Y: EventRels1 E0) :
  EventRels1 E :=
  {| EPreRel0  := error_fiso_prerel X X EPreRel0 ;
     EPostRel0 := error_fiso_postrel X X EPostRel0 ; 
  |}.

(*
Record Cutoff (E: Type -> Type) := {
    cut_fun : forall T, E T -> bool
  }.
*)

(*
Definition CutFun {E: Type -> Type} {T} := E T -> bool.

Class CutClass {E E1 E2: Type -> Type} := {
  fiso_eq : FIso E (E1 +' E2)) ;
  cut_fun :             

Definition cut_fun {E1 E2 : Type -> Type} {T} (e : (E1 +' E2) T) : bool :=
  match e with
  | inl1 _ => true
  | inr1 _ => false
  end.

Class WithCut (E E1 E2: Type -> Type) 


Definition CutoffSplit (E1 E2: Type -> Type) := {
   cut_fun :  
*)
                                 
End REL_LOGIC.  

Notation EventRels1 E := (EventRels E E).

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

Notation recCall := (callE (funname * fstate) fstate).

(* from relational_logic.v *)

Definition relPreF := funname -> funname -> fstate -> fstate -> Prop.
Definition relPostF :=
  funname -> funname -> fstate -> fstate -> fstate -> fstate -> Prop.

Class EquivSpec :=
  { rpreF  : relPreF
  ; rpostF : relPostF }.

Definition eq_spec : EquivSpec :=
  {| rpreF := fun (fn1 fn2 : funname) (fs1 fs2 : fstate) =>
                 fn1 = fn2 /\ fs1 = fs2
  ; rpostF := fun (fn1 fn2 : funname) (fs1 fs2 fr1 fr2: fstate) =>
                 fr1 = fr2 |}.

Section MutRec.

Context (spec : EquivSpec) {E0: Type -> Type}. 

Definition RPreD {T1 T2} (d1 : recCall T1)
                         (d2 : recCall T2) : Prop :=
  match d1, d2 with
  | Call (fn1, fs1), Call (fn2, fs2) => rpreF fn1 fn2 fs1 fs2
  end.

Definition RPostD {T1 T2} (d1 : recCall T1) (t1: T1) (d2 : recCall T2) (t2: T2) : Prop :=
  match d1 in callE _ _ T1_ return T1_ -> T2 -> Prop with
  | Call (fn1, fs1) =>
    match d2 in callE _ _ T2_ return fstate -> T2_ -> Prop with
    | Call (fn2, fs2) => rpostF fn1 fn2 fs1 fs2
    end
  end t1 t2.

Instance EventRels_recCall : EventRels1 recCall :=
  {| EPreRel0  := @RPreD
   ; EPostRel0 := @RPostD
  |}.

Instance EventRels_recCallX {E0} (Y: EventRels1 E0) :
  EventRels1 (recCall +' E0) :=
  {| EPreRel0  :=  sum_prerelF (@RPreD) EPreRel0 ; 
     EPostRel0 :=  sum_postrelF (@RPostD) EPostRel0
  |}.

Instance EventRels_recCallE {E E0} (X: with_Error E E0) (Y: EventRels1 E0) :
  EventRels1 (recCall +' E) :=
  {| EPreRel0  :=  sum_prerelF (@RPreD) (error_fiso_prerel X X EPreRel0) ;
     EPostRel0 :=  sum_postrelF (@RPostD) (error_fiso_postrel X X EPostRel0) 
  |}.

End MutRec.

(*
Definition rel_e := rel pexpr pexpr.
Definition rel_v := rel value value.
Definition rel_vs := rel values values.
Definition rel_c := rel estate1 estate2.
*)


Section IT_section2_xrutt_error.

  (*
Context {E E0} {wE : with_Error E E0}               
    (p : prog) (ev : extra_val_t).

Context {rE0 : EventRels1 E0} {spec : EquivSpec}.

Notation EPreRel_E := (@EPreRel0 E E (EventRels_WithError wE rE0)).

Notation EPostRel_E := (@EPostRel0 E E (EventRels_WithError wE rE0)).
*)

Lemma xrutt_match_option {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RR : R1 -> R2 -> Prop}
(*  {X1: ErrEvent -< E1} {X2: ErrEvent -< E2} *)
  (obj1: option R1) (obj2: option R2) 
  T (e1: E1 T) (k1: T -> itree E1 R1)
  (H: EE1 _ (subevent _ e1) = true) (t1: itree E1 R1) (t2: itree E2 R2)
  (H0: eutt eq t1 (Vis e1 k1))
  (A: forall v1, obj1 = Some v1 -> exists v2, obj2 = Some v2 /\ RR v1 v2) :   
  xrutt EE1 EE2 REv RAns RR
    match obj1 with
    | Some v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | None => t1
    end
    match obj2 with
    | Some v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | None => t2
    end.
Proof.
  destruct obj1 as [r1 | ].
  - destruct obj2 as [r2 | ] ; try auto with *.
    + specialize (A r1 erefl).
      destruct A as [v2 [A1 A2]].
      inversion A1; subst.
      eapply xrutt_Ret; auto.
    + specialize (A r1 erefl).
      destruct A as [v2 [A1 A2]]; inversion A1.
  - rewrite H0.
    pstep; red. econstructor; eauto.  
Qed.

Lemma xrutt_match_option_with_eq {E1 E2 R}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
(*  {X1: ErrEvent -< E1} {X2: ErrEvent -< E2} *)
  (obj1 obj2: option R) 
  T (e1: E1 T) (k1: T -> itree E1 R)
  (H: EE1 _ (subevent _ e1) = true) (t1: itree E1 R) (t2: itree E2 R)
  (H0: eutt eq t1 (Vis e1 k1))
  (A: forall v, obj1 = Some v -> obj2 = Some v) :      
  xrutt EE1 EE2 REv RAns eq
    match obj1 with
    | Some v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | None => t1
    end
    match obj2 with
    | Some v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | None => t2
    end.
Proof.
  eapply xrutt_match_option; eauto.
Qed.

Print exec.

Lemma xrutt_match_exec {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RR : R1 -> R2 -> Prop}
(*  {X1: ErrEvent -< E1} {X2: ErrEvent -< E2} *)
  (obj1: exec R1) (obj2: exec R2)
  T (lf: error -> E1 T) (k1: T -> itree E1 R1)
  (H: forall e, EE1 _ (subevent _ (lf e)) = true)
  (t2: error -> itree E2 R2)
(*  (H0: forall e, eutt eq (t1 e) (Vis e1 k1)) *)
  (A: forall v1, obj1 = ok v1 -> exists v2, obj2 = ok v2 /\ RR v1 v2) :   
  xrutt EE1 EE2 REv RAns RR
    match obj1 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => Vis (lf e) k1 
    end
    match obj2 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => t2 e
    end.
Proof.
  destruct obj1 as [r1 | ].
  - destruct obj2 as [r2 | ] ; try auto with *.
    + specialize (A r1 erefl); destruct A as [v2 [A1 A2]].
      inversion A1; subst; auto.
      eapply xrutt_Ret; auto.
    + specialize (A r1 erefl); destruct A as [v2 [A1 A2]]; inversion A1.
  - pstep; red. econstructor; eauto.
Qed.

(*
Lemma xrutt_match_exec0 {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RR : R1 -> R2 -> Prop}
(*  {X1: ErrEvent -< E1} {X2: ErrEvent -< E2} *)
  (obj1: exec R1) (obj2: exec R2) 
  T (e1: E1 T) (k1: T -> itree E1 R1)
  (H: EE1 _ (subevent _ e1) = true)
  (t1: error -> itree E1 R1) (t2: error -> itree E2 R2)
  (H0: forall e, eutt eq (t1 e) (Vis e1 k1))
  (A: forall v1, obj1 = ok v1 -> exists v2, obj2 = ok v2 /\ RR v1 v2) :   
  xrutt EE1 EE2 REv RAns RR
    match obj1 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => t1 e
    end
    match obj2 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => t2 e
    end.
Proof.
  destruct obj1 as [r1 | ].
  - destruct obj2 as [r2 | ] ; try auto with *.
    + specialize (A r1 erefl); destruct A as [v2 [A1 A2]].
      inversion A1; subst; auto.
      eapply xrutt_Ret; auto.
    + specialize (A r1 erefl); destruct A as [v2 [A1 A2]]; inversion A1.
  - rewrite H0. pstep; red. econstructor; eauto.
Qed.
*)

Lemma xrutt_match_exec1 {E1 E2 R1 R2}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
  {RR : R1 -> R2 -> Prop}
(*  {X1: ErrEvent -< E1} {X2: ErrEvent -< E2} *)
  (obj1: exec R1) (obj2: exec R2) 
  T (e1: E1 T) (k1: T -> itree E1 R1) (f: error -> E1 T)
  (H: forall e, EE1 _ (subevent _ (f e)) = true) (t2: itree E2 R2)
(*  (H0: forall e, eutt eq (t1 e) (Vis e1 k1)) *)
  (A: forall v1, obj1 = ok v1 -> exists v2, obj2 = ok v2 /\ RR v1 v2) :   
  xrutt EE1 EE2 REv RAns RR
    match obj1 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => Vis (f e) k1
    end
    match obj2 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => t2
    end.
Proof.
  destruct obj1 as [r1 | ].
  - destruct obj2 as [r2 | ] ; try auto with *.
    + specialize (A r1 erefl); destruct A as [v2 [A1 A2]].
      inversion A1; subst; auto.
      eapply xrutt_Ret; auto.
    + specialize (A r1 erefl); destruct A as [v2 [A1 A2]]; inversion A1.
  - pstep; red. econstructor; eauto.
Qed.

Lemma xrutt_match_exec_with_eq {E1 E2 R}
  (EE1: forall X, E1 X -> bool)
  (EE2: forall X, E2 X -> bool)
  (REv : forall A B, E1 A -> E2 B -> Prop)
  (RAns : forall A B, E1 A -> A -> E2 B -> B -> Prop )
(*  {X1: ErrEvent -< E1} {X2: ErrEvent -< E2} *)
  (obj1 obj2: exec R) 
  T (lf: error -> E1 T) (k1: T -> itree E1 R)
  (H: forall e, EE1 _ (subevent _ (lf e)) = true)
  (t2: error -> itree E2 R)
  (A: forall v, obj1 = ok v -> obj2 = ok v) :   
  xrutt EE1 EE2 REv RAns eq
    match obj1 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => Vis (lf e) k1
    end
    match obj2 with
    | ok _ v => {| ITreeDefinition._observe := ITreeDefinition.RetF v |}
    | Error e => t2 e
    end.
Proof.
  eapply xrutt_match_exec; eauto.
Qed.  

End IT_section2_xrutt_error.


Section IT_section1.

(*
Context
  (rename_fd : instr_info -> funname -> ufundef -> ufundef)
  (dead_vars_fd : ufun_decl -> instr_info -> Sv.t).
*)  
(* {sem_F : sem_Fun E } *)
  
Context {E E0} {wE : with_Error E E0}               
    (p : prog) (ev : extra_val_t).

Definition flat_i_sem (i: instr) (s: estate) :
  itree (recCall +' E) estate :=
  isem_i_body p ev i s.

Definition flat_cmd_sem (c: cmd) (s: estate) :
  itree (recCall +' E) estate :=
  isem_cmd_rec p ev c s.

Definition flat_fun_sem (fn: funname) (fs: fstate) :
  itree (recCall +' E) fstate :=
  isem_fun_body p ev fn fs.

Definition flat_fundef_sem (fd: fundef) (fs: fstate) :
  itree (recCall +' E) fstate :=
  isem_fundef_body p ev fd fs.

Notation sem_inline it :=
  (interp (ext_handler (handle_recCall p ev)) it).

Notation RA_tr it :=
  (translate (@rassoc_tr recCall recCall E) it).

Definition handle_2recCall :
  (recCall +' recCall) ~> itree ((recCall +' recCall) +' E) :=
  joint_handler (handle_recCall p ev) (handle_recCall p ev). 



Section IT_section2.

Context {rE0 : EventRels1 E0} {spec : EquivSpec}.
  
Context (NormRel : estate -> estate -> Prop) 
        (InputRel : fstate -> estate -> Prop)
        (CStateRel : estate -> estate -> Prop).

Notation EPreRel_E := (@EPreRel0 E E (EventRels_WithError wE rE0)).

Notation EPostRel_E := (@EPostRel0 E E (EventRels_WithError wE rE0)).

Definition xrutt_wE :=
  xrutt (is_error wE) nocutoff EPreRel_E EPostRel_E NormRel.   

Definition wER := (@FIso_rev_MR recCall E E0 ErrEvent wE).

Notation EPreRel_ER := (@EPreRel0 (recCall +' E) (recCall +' E)
                          (EventRels_recCallE spec wE rE0)).

Notation EPostRel_ER := (@EPostRel0 (recCall +' E) (recCall +' E)
                          (EventRels_recCallE spec wE rE0)).

Definition xrutt_wER := xrutt (is_error wER) nocutoff
                          EPreRel_ER EPostRel_ER NormRel.   

Definition xrutt_wER_eq := xrutt (is_error wER) nocutoff
                          EPreRel_ER EPostRel_ER (@eq estate).   

Lemma wER_is_error (s: estate) (e: error) :
  IsCut_ (is_error wER) void (subevent void (Throw (mk_error_data s e))).
Proof.
  unfold is_error, boolfun_split, mfun1, wER, subevent, resum, fromErr.
  destruct wE; simpl.
  unfold ReSum_sum, case_, resum, ReSum_sum, Case_sum1; simpl.
  unfold resum, case_sum1.
  rewrite mid12; simpl.
  auto.
Qed.  

(* eutt eq is too strong, both for the eutt (there might be errors) and 
   for the eq (the two states are related, not necessarily equal) *)

(* T := (kt s) is the tagged itree

partial semantics of the source program: S := asem_i s

partial semantics of the abstract inlined program: 
AI := (sem_inline (RA_tr T))

partial semantics of the concretely inlined program: 
CI := (asem_c s)

By the high-level lemma, we know the full semantics of AI equals to
the full semantics of T.

So by 2, the full semantics of T equals the full semantics of
CI.

By 1, the full semantics of S equals the full semantics of forgetful T.

The semantics of T equals that of the forgetful T.

So the full semantics of S equals that of CI. 
*)
Definition inline_i_info (i: instr) (c: cmd) : Type :=
  let asem_i := flat_i_sem i in 
  let asem_c := flat_cmd_sem c in
  sig (fun (kt: estate -> itree ((recCall +' recCall) +' E) estate) =>
    (forall s, xrutt_wER_eq (forget_tr (kt s)) (asem_i s)) /\ 
    (forall s1 s2, NormRel s1 s2 ->
          xrutt_wER (sem_inline (RA_tr (kt s1))) (asem_c s2))).

Definition inline_ir_info (ir: instr_r) (ii: instr_info) (c: cmd) : Type :=
  let asem_i := flat_i_sem (MkI ii ir) in 
  let asem_c := flat_cmd_sem c in
  sig (fun (kt: estate -> itree ((recCall +' recCall) +' E) estate) =>
    (forall s, xrutt_wER_eq (forget_tr (kt s)) (asem_i s)) /\
    (forall s1 s2, NormRel s1 s2 ->
          xrutt_wER (sem_inline (RA_tr (kt s1))) (asem_c s2))).

Definition inline_cmd_info (c1 c2: cmd) : Type :=
  let asem_c1 := flat_cmd_sem c1 in 
  let asem_c2 := flat_cmd_sem c2 in
  sig (fun (kt: estate -> itree ((recCall +' recCall) +' E) estate) =>
    (forall s, xrutt_wER_eq (forget_tr (kt s)) (asem_c1 s)) /\
    (forall s1 s2, NormRel s1 s2 ->
          xrutt_wER (sem_inline (RA_tr (kt s1))) (asem_c2 s2))).

(*
Definition PreEq (E': Type -> Type) : prerel E' E' :=
(*  forall T1 T2, E' T1 -> E' T2 -> Prop := *)
  fun T1 T2 e1 e2 => e1 ~= e2.

Definition PostEq (E': Type -> Type) : postrel E' E' := 
(*  forall T1 T2, E' T1 -> T1 -> E' T2 -> T2 -> Prop := *)
  fun T1 T2 e1 v1 e2 v2 => e1 ~= e2 /\ v1 ~= v2.
*)

Section IT_section3.

Context
  (rename_fd : instr_info -> funname -> ufundef -> ufundef)
  (dead_vars_fd : ufun_decl -> instr_info -> Sv.t).


(*
Definition res_opt_compare T (x: option T) (y: cexec T) : Prop :=
  match x with
  | Some x' => y = ok x'
  | None => exists m, y = Error m
  end.                       

Definition c_instr_inline (px: ufun_decls) (i: instr) (sv: Sv.t) :
  cexec (Sv.t * cmd) := inline_i rename_fd dead_vars_fd px i sv.

Definition c_cmd_inline (px: ufun_decls) (c: cmd) (sv: Sv.t) :
  cexec (Sv.t * cmd) :=
   inline_c (inline_i rename_fd dead_vars_fd px) c sv.


Definition Pr_body (px: ufun_decls) := fun ir (ii: instr_info) (sv: Sv.t) =>
          (sigT (fun sv': Sv.t => sigT (fun c2: cmd =>
                       (res_opt_compare (Some (sv', c2))
                         (c_instr_inline px (MkI ii ir) sv))
                       * inline_ir_info ir ii c2)%type )).

Definition Pi_body (px: ufun_decls) := fun i (sv: Sv.t) =>
          (sigT (fun sv': Sv.t => sigT (fun c2: cmd =>
                       (res_opt_compare (Some (sv', c2))
                         (c_instr_inline px i sv))
                       * inline_i_info i c2)%type )).

Definition Pc_body (px: ufun_decls) := fun c1 (sv: Sv.t) =>
          (sigT (fun sv': Sv.t => sigT (fun c2: cmd =>
                       (res_opt_compare (Some (sv', c2))
                         (c_cmd_inline px c1 sv))
                       * inline_cmd_info c1 c2)%type )).

Lemma inline_cmd_x (px: ufun_decls) (c1: cmd) :
  forall (X: Sv.t),
        (sigT (fun sv': Sv.t => sigT (fun c2: cmd =>
                       (res_opt_compare (Some (sv', c2))
                         (inline_c (inline_i rename_fd dead_vars_fd px) c1 X))
                       * inline_cmd_info c1 c2)%type )).
Proof.
  set (Pr := fun ir => forall (ii: instr_info) (sv: Sv.t),
         Pr_body px ir ii sv).       
  set (Pi := fun i => forall (sv: Sv.t),
         Pi_body px i sv).
  set (Pc := fun c1 => forall (sv: Sv.t),
         Pc_body px c1 sv).        
  set (CR := cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)).       
  eapply CR.

  { subst Pi Pr. unfold Pr_body.
    intros ir ii H sv0.
    specialize (H ii sv0).
    destruct (H ii sv0) as [[sv [c2 H0]] | ].       
    2: { exact None. }
    unfold inline_ir_info in H0.
    econstructor 1; split.
    exact sv.
    exists c2.
    unfold inline_i_info.
    exact H0.
  }
*)  
  

Lemma inline_cmd_x (px: ufun_decls) (c1: cmd) :
  forall (X: Sv.t),
  option (Sv.t * sigT (fun c2: cmd => inline_cmd_info c1 c2)).
Proof.
  set (Pr := fun ir => forall (ii: instr_info) (sv: Sv.t),
               option (Sv.t * sigT (fun c2: cmd => inline_ir_info ir ii c2))).
  set (Pi := fun i => forall (sv: Sv.t),
                 option (Sv.t * sigT (fun c2: cmd => inline_i_info i c2))).
  set (Pc := fun c1 => forall (sv: Sv.t),
               option (Sv.t * sigT (fun c2: cmd => inline_cmd_info c1 c2))).  
  set (CR := cmd_rect (Pr := Pr) (Pi := Pi) (Pc := Pc)).       
  eapply CR.
  
  { intros ir ii H sv0; subst Pr Pi; simpl in *. 
    destruct (H ii sv0) as [[sv [c2 H0]] | ].       
    2: { exact None. }
    unfold inline_ir_info in H0.
    econstructor 1; split.
    exact sv.
    exists c2.
    unfold inline_i_info.
    exact H0.
  }
  
  { intros sv0.
    set C := inline_c (inline_i rename_fd dead_vars_fd px) [::] sv0.
    simpl in *.                  
    destruct C as [[sv c2] | ] eqn: was_C.
    2: { exact None. }
    inv was_C.
    subst Pc; simpl.
    econstructor 1; split.
    exact sv.
    exists [::].
    unfold inline_cmd_info.
    exists (fun s => Ret s); split; simpl; intro s.
    { unfold forget_tr.
      eapply rutt_xrutt.
      eapply gen_eutt_rutt.
      
      intros; eauto.
      admit.
      intros; eauto.
      admit.
      rewrite translate_ret; reflexivity. 
    }
    { intros s2 H1.
      eapply rutt_xrutt.
      eapply gen_eutt_rutt.
      
      intros; eauto.
      admit.
      intros; eauto.
      admit.
      rewrite translate_ret.
      rewrite interp_ret.
      pstep; red. econstructor; auto.
    }
  }

  { intros i c Hi Hc sv0.
    destruct (Hi sv0) as [[sv_i [c2_i Hi1]] | ].
    2: { exact None. }
    destruct (Hc sv_i) as [[sv_c [c2_c Hc1]] | ]. 
    2: { exact None. }
    econstructor 1.
    split.
    exact sv_c.
    exists (c2_i ++ c2_c).
    unfold inline_i_info, inline_cmd_info in Hi1, Hc1.
    unfold inline_cmd_info. 
    destruct Hi1 as [kt1 [Hi1 Hi2]].
    destruct Hc1 as [kt2 [Hc1 Hc2]].

    set kt := (fun s => bind (kt1 s) kt2).
    exists kt; split; simpl; intro s; subst kt; unfold forget_tr.

    { (* eapply rutt_xrutt.
      eapply gen_eutt_rutt.

      intros; eauto.
      admit.
      intros; eauto.
      admit.
       *)
      unfold xrutt_wER_eq.
      setoid_rewrite translate_bind at 1.
      eapply xrutt_bind; eauto.
      eapply Hi1.
      intros s1 s2 H.
      inv H.
      unfold xrutt_wER_eq in Hc1.
      eapply Hc1.
    }
    { intros s2 H.
      unfold xrutt_wER.
      setoid_rewrite translate_bind.
      setoid_rewrite isem_cmd_cat; simpl.
      setoid_rewrite interp_bind.
      eapply xrutt_bind; eauto.
      eapply Hi2; auto.
    }
  }

  { intros x tg ty e.
    subst Pr; simpl; intros ii sv0.
    econstructor 1; split.
    exact sv0.
    exists ( [:: (MkI ii (Cassgn x tg ty e))] ).
    unfold inline_ir_info.

    set kt := (fun s => @free_tr recCall recCall E _
                          (flat_i_sem (MkI ii (Cassgn x tg ty e)) s)).
    exists kt; split; subst kt; simpl; intro s.
    { unfold xrutt_wER_eq.
      rewrite <- forget_free_inv_lemma.
      unfold flat_i_sem.
      unfold isem_i_body.
      unfold iresult.
      unfold err_result.
      remember (sem_assgn p x tg ty e s) as obj.
      destruct obj.
      - eapply xrutt_Ret; auto.
      - eapply xrutt_CutL; eauto.
        eapply wER_is_error.
    } 
    { intros s2 H.
      unfold xrutt_wER.
      setoid_rewrite <- rassoc_free_interp_lemma at 1.
      setoid_rewrite bind_ret_r.
      unfold flat_i_sem; simpl.
      unfold iresult.
      unfold err_result.

      remember (sem_assgn p x tg ty e s) as obj1.
      remember (sem_assgn p x tg ty e s2) as obj2.

      assert (forall v1, obj1 = ok v1 ->
                         exists v2, obj2 = ok v2 /\ NormRel v1 v2) as A.
      admit.

      destruct obj1 as [r1 | ].
      - destruct obj2 as [r2 | ] ; try auto with *.
        + specialize (A r1 erefl).
          destruct A as [v2 [A1 A2]].
          inversion A1; subst.
          eapply xrutt_Ret; auto.
        + specialize (A r1 erefl).
          destruct A as [v2 [A1 A2]]; inversion A1.
      - pstep; red. econstructor; eauto.  
        eapply wER_is_error.
    }
  }
  
  { intros xs t o es.
    subst Pr; simpl; intros ii sv0.  
    econstructor 1; split.
    exact sv0.
    exists ( [:: (MkI ii (Copn xs t o es))] ).
    unfold inline_ir_info.

    set kt := (fun s => @free_tr recCall recCall E _
                          (flat_i_sem (MkI ii (Copn xs t o es)) s)).
    exists kt; split; subst kt; simpl; intro s.
    { unfold xrutt_wER_eq, flat_i_sem.
      setoid_rewrite <- forget_free_inv_lemma.      
      remember (MkI ii (Copn xs t o es)) as obj.
      remember (isem_i_body p ev obj s) as obj1.
      eapply rutt_xrutt.
      admit.
      (* reflexivity of (rutt eq) *)
    }
    { intros s2 H.
      unfold xrutt_wER.
      setoid_rewrite <- rassoc_free_interp_lemma at 1.
      setoid_rewrite bind_ret_r.
      unfold flat_i_sem; simpl.
      unfold iresult; simpl.

      remember (sem_sopn (p_globs p) o s xs es) as obj1.
      remember (sem_sopn (p_globs p) o s2 xs es) as obj2.

      assert (forall v1, obj1 = ok v1 ->
                         exists v2, obj2 = ok v2 /\ NormRel v1 v2) as A.
      admit.

      destruct obj1 as [r1 | ].
      - destruct obj2 as [r2 | ] ; try auto with *.
        + specialize (A r1 erefl).
          destruct A as [v2 [A1 A2]].
          inversion A1; subst.
          eapply xrutt_Ret; auto.
        + specialize (A r1 erefl).
          destruct A as [v2 [A1 A2]]; inversion A1.
      - pstep; red. econstructor; eauto.  
        eapply wER_is_error.
    }
  }

  { intros xs o es.
    subst Pr; simpl; intros ii sv0.
    econstructor 1; split.
    exact sv0.
    exists ( [:: (MkI ii (Csyscall xs o es))] ).
    unfold inline_ir_info.

    set kt := (fun s => @free_tr recCall recCall E _
                          (flat_i_sem (MkI ii (Csyscall xs o es)) s)).
    exists kt; split; subst kt; simpl; intro s.
    { unfold xrutt_wER_eq.
      rewrite <- forget_free_inv_lemma.
      admit.
      (* reflexivity. *)
    }
    { intros s2 H.
      unfold xrutt_wER.
      setoid_rewrite <- rassoc_free_interp_lemma at 1.
      setoid_rewrite bind_ret_r.
      unfold flat_i_sem; simpl.
      unfold iresult; simpl.

      remember (it_sems_coreP.sem_syscall p xs o es s) as obj1.
      remember (it_sems_coreP.sem_syscall p xs o es s2) as obj2.

      assert (forall v1, obj1 = ok v1 ->
                         exists v2, obj2 = ok v2 /\ NormRel v1 v2) as A.
      admit.

      destruct obj1 as [r1 | ].
      - destruct obj2 as [r2 | ] ; try auto with *.
        + specialize (A r1 erefl).
          destruct A as [v2 [A1 A2]].
          inversion A1; subst.
          eapply xrutt_Ret; auto.
        + specialize (A r1 erefl).
          destruct A as [v2 [A1 A2]]; inversion A1.
      - pstep; red. econstructor; eauto.  
        eapply wER_is_error.
    }
  }

  { rename c1 into c0.
    intros e c1 c2 Hc1 Hc2.
    subst Pr; simpl; intros ii sv0.
    unfold Pc in Hc1, Hc2.
    
    destruct (Hc1 sv0) as [[sv1 [c1R [kt1 [Hc1A Hc1B]]]] | ].
    2: { exact None. }
    destruct (Hc2 sv0) as [[sv2 [c2R [kt2 [Hc2A Hc2B]]]] | ].
    2: { exact None. }

    set svR := (read_e_rec (Sv.union sv1 sv2) e).
    econstructor 1; split.
    exact svR.

    exists ([::MkI ii (Cif e c1R c2R)]).
    unfold inline_ir_info.

    set kt := (isem_ifP p e kt1 kt2).
    exists kt.

    subst kt; split; simpl; intro s.

    { unfold xrutt_wER_eq.
      unfold forget_tr, flat_i_sem, isem_ifP; simpl.
      repeat (rewrite translate_bind).
      eapply xrutt_bind with (RR:= eq); eauto; try reflexivity.

      setoid_rewrite err_result_forget_eqit; simpl.

      2: { instantiate (1:= (sem_cond (p_globs p) e s)).
           unfold sem_cond.
           simpl.
           destruct (sem_pexpr true (p_globs p) s e); simpl.
           destruct (to_bool v); simpl; econstructor; auto.
           econstructor.
      }

      unfold isem_cond, sem_cond, iresult; simpl.
           
      (* reflexivity *)
      admit.
      
      intros b1 b2 H.
      inv H.
      destruct b2; simpl.
      eapply Hc1A.
      eapply Hc2A.
    }
    
    { intros s2 H.
      unfold xrutt_wER.
      unfold isem_ifP; simpl.
      rewrite bind_bind.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply xrutt_bind with (RR:= eq); try reflexivity.


Admitted.      
      
(*********************************************************)

(*
      eapply err_result_rassoc_eqit.
      destruct (sem_cond (p_globs p) e s) eqn: was_t;
        econstructor; eauto.
       
      unfold pointwise_relation; intro b.
      rewrite bind_ret_r.
      destruct b; eauto.
      eapply Hc1B.
      eapply Hc2B.
    } 
  }

  { rename c1 into c0.
    intros x dir lo hi c Hc.
    subst Pr; simpl; intros ii sv0.
    unfold Pc in Hc.
    
    destruct (Hc sv0) as [[sv1 [c1R [kt0 [Hc1A Hc1B]]]] | ].
    2: { exact None. }

    set ir := (Cfor x (dir, lo, hi) c0).
    
    set svR := Sv.union (read_i ir) sv0.
    econstructor 1; split.
    exact svR.

    exists ([::MkI ii (Cfor x (dir, lo, hi) c1R)]).
    unfold inline_ir_info.

    set kt := (isem_forP p x (dir, lo, hi) kt0).
    exists kt.

    subst kt; split; simpl; intro s.

    { unfold forget_tr, flat_i_sem. simpl.
      rewrite translate_bind.
      eapply eqit_bind.

      eapply err_result_forget_eqit.
      destruct (sem_bound (p_globs p) lo hi s) eqn: was_t;
        econstructor; eauto.
      
      unfold pointwise_relation; intros [z1 z2]; simpl.
      unfold isem_for_loopP; simpl.

      revert s.
      induction (wrange dir z1 z2); simpl.
      intro s.
      rewrite translate_ret. reflexivity.

      intros s; simpl.
      unfold isem_for_roundP; simpl.
      rewrite translate_bind.
      eapply eqit_bind.

      eapply err_result_forget_eqit.
      destruct (write_var true x a s) eqn: was_t;
        econstructor; eauto.
      
      unfold pointwise_relation; intro s1.
      rewrite translate_bind.
      eapply eqit_bind.

      eapply Hc1A.
      
      unfold pointwise_relation; intro s2.
      eapply IHl.
    }      
    
    { rewrite bind_ret_r.
      unfold isem_for_loopP, isem_for_roundP; simpl.
      rewrite translate_bind; simpl.
      unfold isem_for_loop, isem_for_round; simpl.
      rewrite interp_bind.
      eapply eqit_bind.

      eapply err_result_rassoc_eqit.
      destruct (sem_bound (p_globs p) lo hi s) eqn: was_t;
        econstructor; eauto.
      
      unfold pointwise_relation; intros [z1 z2]; simpl.
      revert s.

      induction (wrange dir z1 z2); simpl.

      intro s.
      rewrite translate_ret; simpl.
      unfold sem_inline; simpl.
      pstep; red. simpl. econstructor; auto.

      intro s.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply eqit_bind.

      eapply err_result_rassoc_eqit.
      destruct (write_var true x a s) eqn: was_t;
        econstructor; eauto.
       
      intro s1.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply eqit_bind.
      eapply Hc1B.

      intro s2; simpl.
      eapply IHl.
    }  
  }

  { rename c1 into c0.
    intros a c1 e ii2 c2 Hc1 Hc2.
    subst Pr; simpl; intros ii sv0.
    unfold Pc in Hc1, Hc2.
    
    destruct (Hc1 sv0) as [[sv1 [c1R [kt1 [Hc1A Hc1B]]]] | ].
    2: { exact None. }
    destruct (Hc2 sv0) as [[sv2 [c2R [kt2 [Hc2A Hc2B]]]] | ].
    2: { exact None. }

    econstructor 1; split.
    exact sv0.

    exists ([::MkI ii (Cwhile a c1R e ii2 c2R)]).
    unfold inline_ir_info.

    set kt := (isem_while_loopP p kt1 e kt2).
    exists kt.

    subst kt; split; simpl; intro s.

    { unfold forget_tr, flat_i_sem, isem_while_loopP; simpl.
      rewrite translate_iter.
      eapply eutt_iter'; eauto; try reflexivity.
      intros s1 s2 H.
      inv H.
      unfold isem_while_roundP, isem_while_round.
      rewrite translate_bind.
      
      eapply eqit_bind' with (RR := eq).
      eapply Hc1A.

      intros r1 r2 H.
      inv H; simpl.

      rewrite translate_bind.
      eapply eqit_bind' with (RR:= eq).

      eapply err_result_forget_eqit; simpl.
      destruct (sem_cond (p_globs p) e r2) eqn: was_t;
        econstructor; eauto.
      
      intros b1 b2 H.
      inv H; simpl.
      destruct b2; simpl.

      rewrite translate_bind.
      eapply eqit_bind' with (RR:= eq).
      eapply Hc2A.

      intros x1 x2 H.
      inv H; simpl.
      pstep; red; simpl. econstructor; auto.
      pstep; red; simpl. econstructor; auto.
    }      
      
    { rewrite bind_ret_r.
      unfold isem_while_loopP, isem_while_loop.
      unfold isem_while_roundP, isem_while_round; simpl.
      rewrite translate_iter.
      rewrite interp_iter.
      unfold CategoryOps.iter.
      unfold Iter_Kleisli.
      unfold Basics.iter.
      unfold MonadIter_itree.
      eapply eutt_iter.
      unfold pointwise_relation; intro s0.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply eqit_bind.
      eapply Hc1B.
      unfold pointwise_relation; intro s1.
      rewrite translate_bind.
      rewrite interp_bind.
      eapply eqit_bind.

      eapply err_result_rassoc_eqit.
      destruct (sem_cond (p_globs p) e s1) eqn: was_t;
        econstructor; eauto.
      
      unfold pointwise_relation; intro b.
      destruct b; simpl.
      { rewrite translate_bind.
        rewrite interp_bind.
        eapply eqit_bind.
        eapply Hc2B.
        unfold RA_tr.
        setoid_rewrite interp_translate.
        unfold pointwise_relation; intro s2; simpl.
        rewrite interp_ret.
        pstep; red. econstructor; auto.
      }
      { setoid_rewrite interp_translate.
        rewrite interp_ret.
        pstep; red. econstructor; auto.
      }
    }  
  }

  { rename c1 into c0.
    intros xs fn es.
    subst Pr; simpl; intros ii sv0.

    set ir := (Ccall xs fn es).
    
    set sv1 := Sv.union (read_i ir) sv0.

    set isin := ii_is_inline ii.

    destruct isin eqn: was_isin.

    2: { econstructor 1; split.
         exact sv1.
         exists [::(MkI ii ir)].

         unfold inline_ir_info.

         set kt := (fun s => @free_tr recCall recCall E _
                                    (flat_i_sem (MkI ii ir) s)).
         exists kt.

         subst kt; split; simpl; intro s.

         { rewrite <- forget_free_inv_lemma; reflexivity. }
         { setoid_rewrite <- rassoc_free_interp_lemma at 1.
           setoid_rewrite bind_ret_r.
           reflexivity.
         }  
    }

    set fdR := add_iinfo ii (get_fun px fn).

    destruct fdR as [fd | ] eqn: was_fdR.
    2: { econstructor 2. }.

    set fd' := rename_fd ii fn fd.

    set Ai := add_iinfo ii
                  (check_rename dead_vars_fd fn fd fd'
                     (Sv.union (vrvs xs) sv1)).
    destruct Ai as [Ai_ok | ] eqn: was_Ai.
    2 :{ econstructor 2. }

    set ii1 := ii_with_location ii.

    set rename_args :=
      assgn_tuple ii1 (map Lvar fd'.(f_params)) AT_rename fd'.(f_tyin) es.

    set rename_res :=
      assgn_tuple ii1 xs AT_rename fd'.(f_tyout) (map Plvar fd'.(f_res)).

    set cR := rename_args ++ fd'.(f_body) ++ rename_res.

    constructor 1; split.
    exact sv1.
    exists cR.

    unfold inline_ir_info.
    
    set kt := (fun s => @free_right_tr recCall recCall E _
                                    (flat_i_sem (MkI ii ir) s)).
    exists kt.

    subst kt; split; simpl; intro s.

    { rewrite <- forget_free_right_inv_lemma.
      reflexivity.
    }  
    { unfold RA_tr, free_right_tr.
      setoid_rewrite <- translate_cmpE.
      unfold CategoryOps.cat, Cat_IFun.
      rewrite interp_translate.
      subst cR.
      unfold flat_i_sem; simpl.

      set Exp_ev := (isem_pexprs (~~ direct_call) (p_globs p) es s).

      set Post_pr := (fun fs : fstate =>
                        iresult s (upd_estate (~~ direct_call) (p_globs p)
                                     xs fs s)).

      unfold isem_pexprs in Exp_ev.
      unfold iresult in Exp_ev, Post_pr.

      (* pre-processing *)
      destruct (sem_pexprs (~~ direct_call) (p_globs p) s es) eqn: was_exp.

      (* we need xrutt *)
      2: { admit. }

      subst Exp_ev; simpl.
      rewrite bind_ret_l.

      setoid_rewrite isem_cmd_cat at 1.
      rewrite interp_bind; simpl.

      set Ren_args := (isem_cmd_ p ev rename_args s).
      unfold rename_args in Ren_args.

      (* idea: renaming either terminates, or there's an error.
         termining case. *)
      assert (exists s1, eutt eq Ren_args (Ret s1)) as H0.
      admit.

      destruct H0 as [s1 H0].
      rewrite H0.
      rewrite bind_ret_l.

      (* the actual call *)
      setoid_rewrite isem_cmd_cat at 1.

      eapply eqit_bind' with (RR:= InputRel).
      (* given arg_eval succeds, InputRel must relate the input fstate
         on the left, with a state after rename_args on the right
         (both from state s) *)
      
      setoid_rewrite interp_trigger; simpl.
      unfold isem_fun_rec, isem_fun_body.
      unfold kget_fundef, ioget.

      destruct (get_fundef (p_funcs p) fn) as [fd1 | ] eqn: was_ffd.
      (* we need xrutt *)
      2: { admit. }

      rewrite was_ffd.
      setoid_rewrite bind_ret_l; simpl.

      set init_fc := (initialize_funcall p ev fd1 (mk_fstate l s)).
      destruct init_fc as [s2 |] eqn: was_init.
      (* we need xrutt *)
      2: { admit. }

      unfold iresult; simpl.
      rewrite bind_ret_l; simpl.

      unfold isem_cmd_.

      (* finalize_funcall still standing in the way *)
      setoid_rewrite <- bind_ret_r at 4.

      eapply eqit_bind' with (RR := CStateRel).
      (* need to relate fd1 and fd', as well as s1 and s2 *)
      admit.

      intros s3 s4 H1.
      (* CStateRel needs to be chosen smartly *)
      admit. 
      
      (* post-processing *)
      intros fsF sF H1.

      (* InputRel needs to have been chosen smartly *)
      admit.
    }
  }

Admitted.
*)

(*********************************************************)
      
End IT_section3.

End IT_section2.

End IT_section1.
    
End IT_section.



(*      
      eapply eqit_bind' with (RR:= InputRel).

      admit.

      intros fs1 s1 H.

      setoid_rewrite isem_cmd_cat at 1.

      unfold interp.

 (interp
       (fun (T : Type) (e : (recCall +' E) T) =>
        ext_handler (handle_recCall p ev) (rassoc_tr (rw_la e))) 
       (Post_pr fs1))

      
      setoid_rewrite isem_cmd_cat at 1.
      rewrite unfold_interp. simpl.
      
      eapply eqit_bind. with (RR:= InputRel).
      
      

      
      destruct (upd_estate (~~ direct_call) (p_globs p) xs fs s) eqn: was_post.
           
                
      unfold handle_recCall.
      unfold isem_fun_rec; simpl.
      unfold isem_fun_body; simpl.
      unfold flat_cmd_sem.
      unfold isem_cmd_rec.
      unfold isem_cmd_.
      unfold isem_foldr.

      unfold interp; simpl.
      
      setoid_rewrite isem_cmd_cat at 1.
      rewrite interp_bind.
      eapply eqit_bind' with (RR:= InputRel).
      admit.

      intros v1 s1 H.
      setoid_rewrite isem_cmd_cat at 1.
      rewrite interp_bind.
      eapply eqit_bind' with (RR:= FStateRel).
      simpl.
      unfold ext_handler, rec_call; simpl.
      setoid_rewrite interp_trigger.
      unfold rassoc_tr, rw_la; simpl.
(*  unfold isem_fun_rec, isem_cmd_.
      unfold isem_fun_body. *)          
      admit.

      intros fs1 s2 H0.
      admit.
    }
  }

Admitted.



End IT_section1.
    
End IT_section.
  
*)
