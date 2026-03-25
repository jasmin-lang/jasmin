From ITree Require Import
     Basics
     ITree
     ITreeFacts
     Events.Exception
     Interp.Recursion
     MonadState
     State
     StateFacts.
Import Basics.Monads.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat ssralg. 
From Coq Require Import ZArith Utf8.

Require Import expr fexpr label sopn.
Require Import fexpr_sem compiler_util label one_varmap
               linear sem_one_varmap linear_sem label
               psem_defs psem_core it_exec it_exec_sem tfam_iso
               eutt_extras rec_facts it_cflow_sem it_effect_sem.
Require Import linearization_ext.

Require Import it_cflow_sem it_effect_sem equiv_extras rutt_extras.

From ITree Require Import Rutt RuttFacts.
From ITree Require Import CategorySub.

Import Memory.
Require oseq.
Require Import Relations.
Require Import List.

Import ListNotations. 
Import MonadNotation.
Local Open Scope monad_scope.

(** some is GENERAL -> move elsewhere *)

From Paco Require Import paco.

Lemma bind_iterX {E A B C D} (f : A -> itree E (A + B))
  (g : D -> itree E (D + C)) (h: B -> D)
  : forall x,
    (ITree.bind (ITree.iter f x) (fun b => (ITree.iter g) (h b)))
      ≈ 
      ITree.iter (fun ad =>
       match ad with
       | inl a => ITree.map inl
                    (ITree.map (fun ab => match ab with
                                  | inl a => inl a
                                  | inr b => inr (h b) end) (f a))
       | inr d => ITree.map (bimap inr (id_ _)) (g d)
       end) (inl x).
Proof.
  einit. ecofix CIH. intros.
  rewrite !unfold_iter.
  rewrite bind_map bind_bind.
  ebind; econstructor.
  instantiate (1:= fun (ab: A + B) (ad: A + D) =>
                     match (ab, ad) with
                     | (inl a1, inl a2) => eq a1 a2
                     | (inr b, inr d) => eq (h b) d
                     | _ => False
                     end).
  { generalize (f x).
    clear x.
    unfold ITree.map; simpl.
    ginit; gcofix CIH.
    intro t.
    rewrite (itree_eta t); simpl.
    remember (observe t) as ofx.
    destruct ofx; simpl.
    rewrite bind_ret_l.
    { destruct r0; try reflexivity.
      gstep; red.
      econstructor; auto.
      gstep; red.
      econstructor; auto.
    }
    { rewrite bind_tau.
      gstep; red. econstructor.
      gfinal. left.
      eapply CIH.
    }
    { rewrite bind_vis; simpl.
      gstep; red. econstructor.
      intros v; unfold Datatypes.id; simpl.
      gfinal. left.
      eapply CIH.
    }  
  }
  intros [a1 | b] [a2 | d] hh.
  inversion hh; subst. clear H.
  - rewrite bind_tau. etau.
  - intuition.
  - intuition.
  - rewrite bind_ret_l; setoid_rewrite tau_euttge.
    rewrite hh.
    clear hh.
    revert d. ecofix CIH'. intros.
    rewrite !unfold_iter.
    rewrite bind_map.
    ebind; econstructor; try reflexivity.
    intros [d' | c] _ []; cbn. 
    + etau. 
    + reflexivity.  
Qed.


Definition err_def_option {E: Type -> Type} `{ErrEvent -< E} {V}
  (o: option V) : itree E V := err_option (ErrType, tt) o.

Definition conv_obj T1 T2 (ee: T1 = T2) (u: T1) : T2 :=
  eq_rect T1 (fun T : Type => T) u T2 ee.

(* point in the linear code of a function *)
Definition lpoint : Type := (funname * nat)%type.

Definition incr_lpoint (l: lpoint) : lpoint :=
  match l with (fn, pt) => (fn, S pt) end.

(* the program point is in the interval *)
Definition lcp_in_interval (nS nE: nat) (l1: lpoint) : bool :=
  match l1 with
  | (_, n0) => (nS <= n0) && (n0 < nE) end. 


(***** EVENTS *)

(* FindLabel is interpreted in Linear, but GLFEnvAx makes this agree
   with Intermediate. *)
Variant LFindE : Type -> Type :=
  | FindLabelE (lbl: remote_label) : LFindE lpoint. 

(* events mainly used to intstrument the Linear semantics (though
   EvalLoc and EvalExp play a role also in Intermediate) *)
Variant LEvalE : Type -> Type :=
  | RA_readE : LEvalE lpoint
  | RA_isE (x: lpoint) : LEvalE unit                    
  | PC_isE (x: lpoint) : LEvalE unit
  | EvalLocE (e: rexpr) : LEvalE remote_label
  | EvalExpE (e: fexpr) : LEvalE bool. 
                              

Section Asm1.  

Notation plinfo := (nat * label)%type.

Context  {asm_op: Type}
         {syscall_state : Type}
         {sip : SemInstrParams asm_op syscall_state}.  
Context {err: error_data}. 
(* | _ => throw err end. *) 
(* Context {asm_op: Type} {asmop: asmOp asm_op}. *)
(*
Context
  {asm_op: Type}
  {syscall_state : Type}
  {sip : SemInstrParams asm_op syscall_state}.  
  {wsw: WithSubWord} 
  {dc: DirectCall} 
  {ep : EstateParams syscall_state} 
  {spp : SemPexprParams} 
  {pT : progT}
  {scP : semCallParams}.
Context {err: error_data}. 
*)

Definition find_linstr (lc: lcmd) (pt: nat) : option linstr :=
  oseq.onth lc pt.

Definition is_final (lc: lcmd) (pt: nat) : bool :=
  pt =? (length lc).


Section ICMD_RECT.

Variable (fn0: funname).

Variable (Pt : forall pl0 pl1, LTree fn0 pl0 pl1 -> Type).
Variable (Ptl : forall pl0 pl1, LTreeList fn0 pl0 pl1 -> Type).
Variable (Pf : LTreeFun fn0 -> Type).

Hypothesis HErr : forall pl : plinfo, Pt (LErrLeaf fn0 pl). 
Hypothesis HLeaf : forall (pl : plinfo) (l : linstr), Pt (LLeaf fn0 pl l). 
Hypothesis HIf1 : forall (pl0 pl1 : plinfo) (la_cond1 : linstr)
                         (lcm1 : LTreeList fn0 (incrP1 pl0) pl1),
    Ptl lcm1 -> forall la_lbl1 : linstr,
      Pt (LIf1Node la_cond1 lcm1 la_lbl1).
Hypothesis HIf : forall (pl0 pl1 pl2 : plinfo) (la_cond3 : linstr) 
          (lcm2 : LTreeList fn0 (incrP1 pl0) pl1),
          Ptl lcm2
          -> forall (la_goto2 la_lbl3 : linstr)
                    (lcm1 : LTreeList fn0 (incrP2 pl1) pl2),
              Ptl lcm1
              -> forall la_lbl2 : linstr,
                  Pt (LIfNode la_cond3 lcm2 la_goto2 la_lbl3 lcm1 la_lbl2).
Hypothesis HWhileT : forall (pl0 pl1 pl2 : plinfo) (la_align : bool) 
          (ii : instr_info) (n0 := pl0.1) (lbl0 := pl0.2) 
          (n00 := if la_align then n0.+1 else n0) (la_lbl1 : linstr) 
          (lcm1 : LTreeList fn0 (n00.+1, lbl0) pl1),
          Ptl lcm1
          -> forall lcm2 : LTreeList fn0 pl1 pl2,
              Ptl lcm2
              -> forall la_goto1 : linstr,
                  Pt (LWhileTNode ii la_lbl1 lcm1 lcm2 la_goto1).
Hypothesis HWhileF : forall (pl0 pl1 : plinfo)
                            (lcm1 : LTreeList fn0 pl0 pl1),
          Ptl lcm1 → Pt (LWhileFNode lcm1).
Hypothesis HWhile1 : forall (pl0 pl1 : plinfo) (la_align : bool)
       (ii : instr_info) (n0 := pl0.1) (lbl0 := pl0.2)
       (n00 := if la_align then n0.+1 else n0) 
       (la_lbl1 : linstr) (lcm1 : LTreeList fn0 (n00.+1, lbl0) pl1),
    Ptl lcm1 -> forall la_cond1 : linstr,
      Pt (LWhile1Node ii la_lbl1 lcm1 la_cond1).
Hypothesis HWhile : forall (pl0 pl1 pl2 : plinfo) (la_align : bool) 
          (ii : instr_info) (n0 := pl0.1) (lbl0 := pl0.2) 
          (n00 := if la_align then n0.+1 else n0) (la_goto2 la_lbl3 : linstr) 
          (lcm2 : LTreeList fn0 (n00.+2, lbl0) pl1),
          Ptl lcm2
          -> forall (la_lbl2 : linstr) (lcm1 : LTreeList fn0 (incrP1 pl1) pl2),
              Ptl lcm1
              -> forall la_cond3 : linstr,
               Pt (LWhileNode ii la_goto2 la_lbl3 lcm2 la_lbl2 lcm1 la_cond3).
Hypothesis HCall : forall (pl0 : plinfo) (nb na : nat) (n0 := pl0.1) 
          (lbl0 := pl0.2) (n1 := n0 + nb + na.+2) (fn' : funname) 
          (la_before la_after : lcmd) (la_call la_ret : linstr),
          Pt (LCallNode fn0 pl0 nb na fn' la_before la_after la_call la_ret).
Hypothesis HLNil : forall pl : plinfo, Ptl (LListNil fn0 pl).
Hypothesis HLCons : forall (pl0 pl1 pl2 : plinfo) (l : LTree fn0 pl0 pl1),
    Pt l -> forall l0 : LTreeList fn0 pl1 pl2,
      Ptl l0 -> Ptl (LListCons l l0).

Hypothesis HLFun : forall (lbl : label) (pl1 : plinfo) (lc1 lc2 : lcmd) 
          (n1 := Datatypes.length lc1) (lt : LTreeList fn0 (n1, lbl) pl1),
          Pf (LTFun lc2 lt).

(*
Hypothesis HH : forall 

Check (@LTree_mut asm_op _ fn0 Pt Ptl HErr HLeaf HIf1 HIf HWhileT
         HWhileF HWhile1 HWhile HCall HLNil HLCons).

Check (@LTreeList_mut asm_op _ fn0 Pt Ptl HErr HLeaf HIf1 HIf HWhileT
         HWhileF HWhile1 HWhile HCall HLNil HLCons).

Check (@LTreeFun_rect  asm_op _ fn0 Pf).

Hypothesis HLFun : forall (lbl : label) (pl1 : plinfo) (lc1 lc2 : lcmd) 
          (n1 := Datatypes.length lc1) (lt : LTreeList fn0 (n1, lbl) pl1),
          Pf (LTFun lc2 lt).


Definition LTreeFun_Rect 

Check LTreeFun_Rect.


Search LTreeFun.
About LTreeFun.
Search "Fun_ind".

Check @LTreeFun_ind.

Variables (Pr: )
*)
  
End ICMD_RECT.  


Section LinSemClass.

Context (S: Type).

(* We use this class on S to abstract over the paramters required by
   lstate. *)
Class LinSem : Type := {
  Lopn_sem (xs: seq.seq lexpr) (o: sopn) (es: seq.seq rexpr) (s1: S) : exec S ;

  Lsyscall_sem (o: syscall_t) (s1: S) : exec S ;

  Lcall_sem (ov: option var_i) (d: remote_label) (s1: S) : exec S ;

  Lret_sem (s1: S) : exec S ;

  Lalign_sem (s1: S) : exec S ;

  Llabel_sem (k: label_kind) (lbl: label) (s1: S) : exec S ;

  Lgoto_sem (d: remote_label) (s1: S) : exec S ;

  Ligoto_sem (e: rexpr) (s1: S) : exec S ;

  Lstorelabel_sem (x: var) (lbl: label) (s1: S) : exec S ;

  Lcond_sem (e: fexpr) (lbl: label) (s1: S) : exec S ; }.

(* basically, same as eval_instr (in the old semantics, with S =
   lstate) *)
Definition linstr_sem {LS_I : LinSem} (i : linstr_r)
  (s1: S) : exec S := match i with
  | Lopn xs o es => Lopn_sem xs o es s1
  | Lsyscall o => Lsyscall_sem o s1
  | Lcall o d => Lcall_sem o d s1
  | Lret => Lret_sem s1
  | Lalign => Lalign_sem s1
  | Llabel x y => Llabel_sem x y s1
  | Lgoto d => Lgoto_sem d s1
  | Ligoto e => Ligoto_sem e s1
  | LstoreLabel x lbl => Lstorelabel_sem x lbl s1
  | Lcond e lbl => Lcond_sem e lbl s1
  end.

End LinSemClass.


Section LinSemContext.
  
Context (LState: Type) (LS_I : LinSem LState).

(* the output of the linearization pass; lfenv should be defined using
   linear_l2r_fd and imed_fun. then the axiom holds by
   forget_imed_fun_ok. *)
Notation GLFEnv :=
    (forall fn: funname, option (plinfo * lfundef * LTreeFun fn)). 
Context (glfenv: GLFEnv).
Context (GLFEnvAx : forall (fn: funname) pl fd lt,
            glfenv fn = Some (pl, fd, lt) ->
            forget_imed_fun lt = (pl, lfd_body fd)).

Notation LFEnv := (funname -> option lcmd).
Notation IFEnv := (forall fn: funname, option (LTreeFun fn)).

Definition lfenv : LFEnv := fun fn => match glfenv fn with
                       | Some (_, fd, _) => Some (lfd_body fd)
                       | _ => None end.                              

Definition ifenv : IFEnv := fun fn => match glfenv fn with
                       | Some (_, _, lt) => Some lt
                       | _ => None end.                              


Section LinSem.

Context {E} {XE: ErrEvent -< E}.

Definition aloop :=
  @loop Type (ktree E) sum
    (@Id_Kleisli (itree E) (@Monad_itree E))
    (@Cat_Kleisli (itree E) (@Monad_itree E))
    (@Case_Kleisli (itree E))
    (@Inl_Kleisli (itree E) (@Monad_itree E))
    (@Inr_Kleisli (itree E) (@Monad_itree E))
    (@Iter_Kleisli (itree E) (@MonadIter_itree E)).

Definition abimap := (@bimap Type (ktree E) sum
                        (Bimap_Coproduct
                           (Kleisli (itree E)) Cat_Kleisli sum
                           Case_Kleisli Inl_Kleisli Inr_Kleisli)).

Definition acat := @Cat_Kleisli (itree E) (@Monad_itree E).
(*  (λ (a b c : Type) (u : ktree E a b) (v : ktree E b c) (x : a),
     ITree.bind (u x) [eta v]) *)


Section AbsIterators.
(***** ABSTRACT ITERATORS *)
Context {L: Type}.

(* basic iteration intuition; however, it seems better to make the
   exit check BEFORE executing the body. *)
Definition Cntr_basic (Sem: L -> itree E L) (Init InRange Final: L -> bool)
  (l0: L) : itree E (L + L) :=
  match ((Init l0) || (InRange l0)) with
  | true => l1 <- Sem l0 ;; Ret (inl l1)
  | false => match (Final l0) with
             | true => Ret (inr l0)
             | false => throw err
             end
  end.             

(* lift a semantics to the body of a loop. note: Init, Final and
   InRange are not necessarily disjoint. *)
Definition BKT (Sem: L -> itree E L) (Init Final InRange: L -> bool)
  (pe: L + L) : itree E (L + L) :=
  match pe with
  | inl l0 => match Final l0 with
              | true => Ret (inr l0)
              | false => match InRange l0 with
                         | true => l1 <- Sem l0 ;; Ret (inl l1)  
                         | false => throw err
                         end
                   end
  | inr l0 => match Final l0 with
              | true => Ret (inr l0)
              | false => match (Init l0) with
                         | true => l1 <- Sem l0 ;; Ret (inl l1)  
                         | false => throw err
                         end
                   end
  end.                   

Notation BKT_loop Sem Init Final InRange :=
  (aloop (BKT Sem Init Final InRange)).

(*
Definition BKT_loop (Sem: L -> itree E L) (Init Final InRange: L -> bool)
  (l0: L) : itree E L := aloop (BKT Sem Init Final InRange) l0.
*)

Lemma BKT_vanishing (Sem: L -> itree E L)
  (Init Final InRange1 InRange2: L -> bool) (l0: L) :
  eutt eq (ITree.bind (BKT_loop Sem (fun x => (InRange2 x) || (Init x))
                           (fun x => (InRange2 x) || (Final x))
                            InRange1 l0) 
                      (BKT_loop Sem Init Final InRange2))
          (BKT_loop Sem Init Final
                  (fun x => (InRange1 x) || (InRange2 x)) l0).
Proof.
Admitted. 


(* alternative: lift a semantics to the body of an iter. *)
Definition MKT (Sem: L -> itree E L) (Final InRange: L -> bool)
  (l0: L) : itree E (L + L) :=
  match Final l0 with
  | true => Ret (inr l0)
  | false => match InRange l0 with
             | true => l1 <- Sem l0 ;; Ret (inl l1)  
             | false => throw err
             end
  end.

Notation MKT_iter Sem Final InRange :=
  (ITree.iter (MKT Sem Final InRange)).

(*
Definition MKT_iter (Sem: L -> itree E L) (Final InRange: L -> bool)
  (l0: L) : itree E L := ITree.iter (MKT Sem Final InRange) l0.
*)

Lemma MKT_vanishing (Sem: L -> itree E L)
  (Final InRange1 InRange2: L -> bool) (l0: L) :
  eutt eq (ITree.bind (MKT_iter Sem (fun x => (InRange2 x) || (Final x))
                            InRange1 l0) 
                      (MKT_iter Sem Final InRange2))
          (MKT_iter Sem Final
                  (fun x => (InRange1 x) || (InRange2 x)) l0).
Proof.
  unfold aloop; simpl.
  unfold MKT at 1 3; simpl.
  setoid_rewrite bind_iterX.
  unfold MKT; simpl.
  unfold bimap, Bimap_Coproduct; simpl.
    unfold CategoryOps.cat, case_, inl_; simpl.
  unfold Case_Kleisli, case_sum, Cat_Fun, sum_inl, inr_, id_,
      sum_inr, Id_Fun; simpl.

  (* refactor the goal to make it more readable *)
  assert (ITree.iter
    (λ ad : L + L,
       match ad with
       | inl a =>
           ITree.map inl
                (if InRange2 a || Final a
                 then Ret (inr a) (* inl a -> inl (inr a) *)
                 else if InRange1 a
                      then ITree.bind (Sem a) (λ l1 : L, Ret (inl l1))
                                    (* inl a -> inl (inl a) *)  
                      else throw err)
       | inr d => ITree.map (λ x : L + L, match x with
                                   | inl a => inl (inr a)
                                   | inr b => inr b
                                   end)
             (if Final d
              then Ret (inr d) (* inr d -> inr d *)
              else if InRange2 d
                   then ITree.bind (Sem d) (λ l1 : L, Ret (inl l1))
                       (* inr d -> inl (inr d) *)             
                   else throw err)               
       end) (inl l0)
  ≈ ITree.iter
      (λ l1 : L,
         if Final l1
         then Ret (inr l1)
         else if InRange1 l1 || InRange2 l1
              then ITree.bind (Sem l1) (λ l2 : L, Ret (inl l2))
              else throw err) l0
         ) as W.
  { eapply eutt_iter' with  
    (RI := fun (x: L + L) (y: L) =>
             (match x with
             | inl l1 => l1 = y 
             | inr l1 => l1 = y 
             end)); simpl; try reflexivity.

  intros j1 j2 H.
  clear l0.
  destruct j1 as [j1 | j1]; simpl.
  { inversion H; subst; simpl. clear H0.    
    destruct (Final j2) eqn: was_e0; simpl.
    { destruct (InRange2 j2 || true) eqn: was_e1; simpl; try congruence.
      2: { compute in was_e1.
         destruct (InRange2 j2); try congruence.
      }      
      setoid_rewrite bind_ret_l; simpl.
      pstep; red; econstructor.
      (* PROBLEM: what is wrong? *)
      (* econstructor *)
      admit.
    }
      
    destruct (InRange2 j2) eqn: was_e3; simpl.    
    { destruct (InRange1 j2 || true) eqn: was_e4; simpl.
      2: { compute in was_e4.
           destruct (InRange1 j2); try congruence.
      }
      unfold ITree.map; setoid_rewrite bind_ret_l.
      (* actually, PROBLEM: extra step on the right *)
      admit.
    }
      
    { destruct (InRange1 j2) eqn: was_e5; simpl.    
      - unfold ITree.map; setoid_rewrite bind_bind.
        eapply eqit_bind'; try reflexivity.
        intros r1 r2 H.
        inversion H; subst.
        rewrite bind_ret_l.
        pstep; red; econstructor.
        econstructor; auto.
      - setoid_rewrite bind_vis.
        eapply eqit_Vis.
        intro u. destruct u.
    } 
  }  
Abort.    
    
Lemma MKT_vanishing (Sem: L -> itree E L)
  (Final InRange1 InRange2: L -> bool) (l0: L) :
  eutt eq (ITree.bind (MKT_iter Sem (fun x => (InRange2 x) || (Final x))
                            InRange1 l0) 
                      (MKT_iter Sem Final InRange2))
          (MKT_iter Sem Final
                  (fun x => (InRange1 x) || (InRange2 x)) l0).
Proof.
  unfold aloop; simpl.
  unfold MKT at 1 3; simpl.
  setoid_rewrite bind_iterX.
  unfold MKT; simpl.
  unfold bimap, Bimap_Coproduct; simpl.
    unfold CategoryOps.cat, case_, inl_; simpl.
  unfold Case_Kleisli, case_sum, Cat_Fun, sum_inl, inr_, id_,
      sum_inr, Id_Fun; simpl.

  (* refactor the goal to make it more readable *)
  assert (ITree.iter
    (λ ad : L + L,
       match ad with
       | inl a =>
           ITree.map inl
                (if InRange2 a || Final a
                 then Ret (inr a) (* inl a -> inl (inr a) *)
                 else if InRange1 a
                      then ITree.bind (Sem a) (λ l1 : L, Ret (inl l1))
                                    (* inl a -> inl (inl a) *)  
                      else throw err)
       | inr d => ITree.map (λ x : L + L, match x with
                                   | inl a => inl (inr a)
                                   | inr b => inr b
                                   end)
             (if Final d
              then Ret (inr d) (* inr d -> inr d *)
              else if InRange2 d
                   then ITree.bind (Sem d) (λ l1 : L, Ret (inl l1))
                       (* inr d -> inl (inr d) *)             
                   else throw err)               
       end) (inl l0)
  ≈ ITree.iter
      (λ l1 : L,
         if Final l1
         then Ret (inr l1)
         else if InRange1 l1 || InRange2 l1
              then ITree.bind (Sem l1) (λ l2 : L, Ret (inl l2))
              else throw err) l0
         ) as W.
  { setoid_rewrite unfold_iter.

    destruct (Final l0) eqn: was_e0; simpl.
    { destruct (InRange2 l0 || true) eqn: was_e1; simpl.
      2: { compute in was_e1.
           destruct (InRange2 l0); try congruence.
      }   
      rewrite bind_bind.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite bind_ret_l; simpl.
      setoid_rewrite tau_euttge.
      admit.
    }
    { destruct (InRange2 l0) eqn: was_e2; simpl.
      { destruct (InRange1 l0 || true) eqn: was_e3; simpl.
        2: { compute in was_e3.
             destruct (InRange1 l0); try congruence.
        }
        rewrite bind_bind.
        setoid_rewrite bind_ret_l; simpl.
        setoid_rewrite bind_ret_l; simpl.
        setoid_rewrite tau_euttge; simpl.
        admit.
      }
      { destruct (InRange1 l0) eqn: was_e4; simpl.
        { setoid_rewrite bind_bind.  
          setoid_rewrite bind_bind.  
          setoid_rewrite bind_ret_l; simpl.
          setoid_rewrite bind_ret_l; simpl.
          eapply eqit_bind; try reflexivity.
          intros l1.
          admit.
        }
        { rewrite bind_bind.
          setoid_rewrite bind_vis.
          eapply eqit_Vis.
          intro u. destruct u.
        }
     }
    }
  }
  { rewrite <- W.
    eapply eutt_iter.
    intros [l | l]; try reflexivity.
    eapply eqit_bind; try reflexivity.
    unfold ITree.map; destruct (InRange2 l || Final l); simpl; try reflexivity.
    { rewrite bind_ret_l; simpl; try reflexivity. }
    { destruct (InRange1 l); try reflexivity.
      - rewrite bind_bind; simpl.
        eapply eqit_bind; try reflexivity.
        intro pe; setoid_rewrite bind_ret_l; try reflexivity.
      - setoid_rewrite bind_vis.
        eapply eqit_Vis.
        intro u. destruct u.
    } 
  } 
Admitted.                 


(* interesting; the left reduces to a 'deep' nesting on iters, 
   while the right to a top-level iter (using bind_iterX) *)
Lemma BKT_vanishing_aux1 (Sem: L -> itree E L)
  (Init Final InRange1 InRange2: L -> bool) (l0: L) :  
  eutt eq (BKT_loop (BKT_loop Sem Init Final InRange2)
                 (fun x => (InRange2 x) || (Init x))
                 (fun x => (InRange2 x) || (Final x))
                 InRange1 l0)
          (ITree.bind (BKT_loop Sem (fun x => (InRange2 x) || (Init x))
                           (fun x => (InRange2 x) || (Final x))
                            InRange1 l0) 
                      (BKT_loop Sem Init Final InRange2)).
Proof.
  unfold aloop; simpl.
  unfold BKT at 1 3; simpl.
  unfold loop.
  rewrite bind_bind; simpl.
  eapply eqit_bind; try reflexivity.
  intros pe.
  unfold CategoryOps.iter.
  unfold Iter_Kleisli, Basics.iter, MonadIter_itree; simpl.
  unfold CategoryOps.cat; simpl.
  unfold Cat_Kleisli; simpl.
  setoid_rewrite bind_ret_l.
  setoid_rewrite bind_iterX.
  unfold BKT; simpl.
Admitted.

(*
Variable (P1 : (L + L + (L + L)) -> (L + L) -> bool).
Variable (P2 : (L + L + (L + L)) -> (L + L) -> bool).
Variable (P3 : (L + L + (L + L)) -> (L + L) -> bool).
Variable (P4 : (L + L + (L + L)) -> (L + L) -> bool).

End AbsIterators.

Notation L:= nat.

Lemma BKT_vanishing_aux2 (Sem: L -> itree E L)
  (Init Final InRange1 InRange2: L -> bool) (l0: L) :
  eutt eq (ITree.bind (BKT_L Sem (fun x => (InRange2 x) || (Init x))
                                (fun x => (InRange2 x) || (Final x))
                                 InRange1 l0) 
                      (BKT_L Sem Init Final InRange2))
          (BKT_L Sem Init Final 
                    (fun x => (InRange1 x) || (InRange2 x)) l0).
Proof.
  unfold BKT_L, aloop; simpl.
  unfold BKT at 1 3; simpl.
  unfold loop.
  rewrite bind_bind; simpl.
  eapply eqit_bind; try reflexivity.
  intros pe.
  unfold CategoryOps.iter.
  unfold Iter_Kleisli, Basics.iter, MonadIter_itree; simpl.
  unfold CategoryOps.cat; simpl.
  unfold Cat_Kleisli; simpl.
  setoid_rewrite bind_ret_l.
  setoid_rewrite bind_iterX.
  unfold BKT; simpl.
  unfold ITree.map; simpl.
  set LB := (fun ad : L + L + (L + L) => _).
  set RB := (fun x : L + L => _).
  set LT := (ITree.iter LB _).
  set RT := (ITree.iter RB _).

  destruct pe as [l1 | l1]; simpl.
    
(*  set X := (fun (x: L + L + (L + L)) (y: L + L) =>
             (match (x, y) return bool with
             | (inr (inr l1), inr l2) => (l1 == l2) 
          
             | (inl (inl l1), inl l2) => (l1 == l2) 
             | (inl (inr l1), inr l2) => (l1 == l2) 
             | _ => false
             end)).
*)  

  eapply eutt_iter' with  
    (RI := fun (x: L + L + (L + L)) (y: L + L) =>
             (match (x, y) with
             | (inr (inl l1), inl l2) => l1 = l2 
             | (inr (inr l1), inr l2) => l1 = l2 
             | (inl (inl l1), inl l2) => l1 = l2 
             | (inl (inr l1), inr l2) => l1 = l2 
             | _ => True
             end)); simpl; try reflexivity.

  intros j1 j2 H.
  clear l0.
  (*
  rewrite H; simpl.
  clear H.
  clear j1.
   *)
  destruct j1 as [[j1 | j1] | [j1 | j1]]; try congruence; 
  destruct j2 as [j2 | j2]; try congruence.
  
  { inversion H; subst; simpl.
    
    subst LB RB.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_bind.
    destruct (Final j2) eqn: was_e0; simpl.
    destruct (InRange2 j2 || true) eqn: was_e1; simpl; try congruence.
    2: { compute in was_e1.
         destruct (InRange2 j2); try congruence.
       }      
    setoid_rewrite bind_ret_l; simpl.
    unfold bimap, Bimap_Coproduct; simpl.
    unfold CategoryOps.cat, case_, inl_; simpl.
    
    rewrite bind_bind; unfold id_; simpl.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l.
    pstep; red; econstructor; simpl.
    unfold Datatypes.id; simpl.
    econstructor.

    econstructor.
    unfold LB; simpl.
    unfold Datatypes.id; simpl.
    reflexivity.
    


  
Lemma BKT_vanishing_aux2 (Sem: L -> itree E L)
  (Init Final InRange1 InRange2: L -> bool) (l0: L) :
  eutt eq (ITree.bind (BKT_L Sem (fun x => (InRange2 x) || (Init x))
                                (fun x => (InRange2 x) || (Final x))
                                 InRange1 l0) 
                      (BKT_L Sem Init Final InRange2))
          (BKT_L Sem Init Final 
                    (fun x => (InRange1 x) || (InRange2 x)) l0).
Proof.
  unfold BKT_L, aloop; simpl.
  unfold BKT at 1 3; simpl.
  unfold loop.
  rewrite bind_bind; simpl.
  eapply eqit_bind; try reflexivity.
  intros pe.
  unfold CategoryOps.iter.
  unfold Iter_Kleisli, Basics.iter, MonadIter_itree; simpl.
  unfold CategoryOps.cat; simpl.
  unfold Cat_Kleisli; simpl.
  setoid_rewrite bind_ret_l.
  setoid_rewrite bind_iterX.
  unfold BKT; simpl.
  unfold ITree.map; simpl.
  set LB := (fun ad : L + L + (L + L) => _).
  set RB := (fun x : L + L => _).

(*  
  eapply eutt_iter' with
    (RI := fun (x: L + L + (L + L)) (y: L + L) => eq x (inl y));
    simpl; try reflexivity.
 *)

  eapply eutt_iter' with
    (RI := fun (x: L + L + (L + L)) (y: L + L) =>
             match (x, y) with
             | (inr (inr l1), inr l2) => l1 == l2 
          
             | (inl (inl l1), inl l2) => l1 == l2 
             | (inl (inr l1), inr l2) => l1 == l2 
             | _ => false
             end) ;
    simpl; try reflexivity.

(*  
  eapply eutt_iter' with
    (RI := fun (x: L + L + (L + L)) (y: L + L) => P1 x y);
    simpl; try reflexivity.
*)  

  intros j1 j2 H.
  clear l0.
  clear pe.
  (*
  rewrite H; simpl.
  clear H.
  clear j1.
   *)
  destruct j1 as [[j1 | j1] | [j1 | j1]]; try congruence; 
  destruct j2 as [j2 | j2]; try congruence.
  
  { inversion H; subst; simpl.
    
    subst LB RB.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_bind.
    destruct (Final j2) eqn: was_e0; simpl.
    destruct (InRange2 j2 || true) eqn: was_e1; simpl; try congruence.
    2: { compute in was_e1.
         destruct (InRange2 j2); try congruence.
       }      
    setoid_rewrite bind_ret_l; simpl.
    unfold bimap, Bimap_Coproduct; simpl.
    unfold CategoryOps.cat, case_, inl_; simpl.
    rewrite bind_bind; unfold id_; simpl.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l.
    pstep; red; econstructor; simpl.
    unfold Datatypes.id; simpl.
    econstructor.

    econstructor.
    unfold LB; simpl.
    unfold Datatypes.id; simpl.
    reflexivity.
    

       
  destruct j2; simpl.

  { destruct (Final l) eqn: was_e0; simpl.
    destruct (InRange2 l || true) eqn: was_e1; simpl; try congruence.
    2: { compute in was_e1.
         destruct (InRange2 l); try congruence.
       }  
    setoid_rewrite bind_ret_l; simpl.
    unfold bimap, Bimap_Coproduct; simpl.
    unfold CategoryOps.cat, case_, inl_; simpl.
    rewrite bind_bind; unfold id_; simpl.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l.
    setoid_rewrite bind_ret_l.
    pstep; red; econstructor; simpl.
    unfold LB; simpl.
    unfold Datatypes.id; simpl.
    reflexivity.
    
  
  
  set RB := (fun x : L + L => _).

  
  
  
  destruct pe; simpl.

  { 
  eapply eutt_iter'.
  instantiate (1 := fun x y => eq x (inl y)).
  { simpl; intros j1 j2 H.
    subst LB RB; simpl.
    rewrite H; simpl.
    unfold ITree.map; simpl.
    setoid_rewrite bind_bind.
    setoid_rewrite bind_bind.
    clear H. clear j1.
    destruct j2; simpl; try reflexivity.
    
    
  
  set XL := (ITree.iter _).
  set XR := (ITree.iter _).
  
  
Admitted. 



Lemma BKT_vanishing2a (Sem: L -> itree E L)
  (Init Final InRange1 InRange2: L -> bool) (l0: L) :
  eutt eq (acat (BKT_L Sem (fun x => (InRange2 x) || (Init x))
                           (fun x => (InRange2 x) || (Final x))
                            InRange1) 
                (BKT_L Sem Init Final InRange2) l0)
         (BKT_L Sem Init Final
                  (fun x => (InRange1 x) || (InRange2 x)) l0).
Proof.
  unfold BKT_L, aloop; simpl.
  unfold BKT at 1 3; simpl.
  unfold acat; simpl.
  set W := (@loop_natural_right Type (ktree E) _ _  
    (@Id_Kleisli (itree E) (@Monad_itree E))
    (@Cat_Kleisli (itree E) (@Monad_itree E))
     _ sum (@Case_Kleisli (itree E))
    (@Inl_Kleisli (itree E) (@Monad_itree E))
    (@Inr_Kleisli (itree E) (@Monad_itree E)) _ 
    (@Iter_Kleisli (itree E) (@MonadIter_itree E)) _
    lpoint lpoint lpoint lpoint).


  loop; simpl.
  unfold CategoryOps.cat; simpl.
  rewrite bind_bind.
  eapply eqit_bind; try reflexivity.
  set X := iter_natural.
  unfold eq2 in X; simpl in X.
  unfold Eq2_Handler in X; simpl in X.
  unfold eutt_Handler in X; simpl in X.
  unfold Relation.i_pointwise in X; simpl in X.
  unfold Handler in X; simpl in X.
(*  unfold CategoryOps.cat in X; simpl in X.
  unfold Cat_Handler in X; simpl in X.
  unfold Handler.cat in X; simpl in X.
  unfold interp in X; simpl in X.
 *)
    set W := (@loop_natural_right Type (ktree E) _ _  
    (@Id_Kleisli (itree E) (@Monad_itree E))
    (@Cat_Kleisli (itree E) (@Monad_itree E))
     _ sum (@Case_Kleisli (itree E))
    (@Inl_Kleisli (itree E) (@Monad_itree E))
    (@Inr_Kleisli (itree E) (@Monad_itree E)) _ 
    (@Iter_Kleisli (itree E) (@MonadIter_itree E)) _
    lpoint lpoint lpoint lpoint).
    unfold loop in W; simpl.

  
  set Y := loop_natural_right.
  
  intros pe; simpl.  
*)

(*
Lemma BKT_vanishing2r (Sem: L -> itree E L)
  (Init Final InRange1 InRange2: L -> bool) (l0: L) :
  eutt eq (BKT_L (BKT_L Sem Init Final InRange2)
                 (fun x => (InRange2 x) || (Init x))
                 (fun x => (InRange2 x) || (Final x))
                 InRange1 l0)
          (BKT_L Sem Init Final
                 (fun x => (InRange1 x) || (InRange2 x)) l0).
Proof.
  unfold BKT_L, aloop; simpl.
  unfold BKT at 1 3; simpl.
  unfold loop; simpl.
  unfold CategoryOps.cat; simpl.
  eapply eqit_bind; try reflexivity.
  intros pe; simpl.
  clear l0.
  Check @iter_natural.
  
  iter (f >>> case_ (inl_ >>> inl_) inr_) >>> case_ (inl_ >>> inl_) inr_
  ⩯ iter (f >>> case_ (inl_ >>> inl_) (case_ (inl_ >>> inl_) inr_ >>> inr_))

Admitted.

*)

(* reversing: exit check after sem step *)
Definition RACntr (Sem: L -> itree E L) (NoExit: L -> bool)
  (l0: L) : itree E (L + L) :=
  l1 <- Sem l0 ;; if NoExit l1 then Ret (inl l1) else Ret (inr l0).


(* the generic iteration body used to define the semantics (with
   ITree.iter) *)
Definition ACntr (Sem: L -> itree E L) (NoExit: L -> bool)
  (l0: L) : itree E (L + L) :=
  (* check whether the exit condition is satisfied *)
  if NoExit l0 then l1 <- Sem l0 ;; Ret (inl l1) else Ret (inr l0).

(* the generic iteration body used to define the semantics (with
   loop). *)
Definition ACntr2 (Sem: L -> itree E L) (NoExit: L -> bool)
  (pe: L + L) : itree E (L + L) :=
  case_sum _ _ _ (ACntr Sem NoExit) (ACntr Sem NoExit) pe.

(* iterates ACntr *)
Definition ACntrI (Sem: L -> itree E L) (NoExit: L -> bool) :
  L -> itree E L :=
  fun l0 => ITree.iter (ACntr Sem NoExit) l0.

(* loops ACntr2 *)
Definition ACntrL (Sem: L -> itree E L) (NoExit: L -> bool) :
  L -> itree E L :=
  fun l0 => aloop (ACntr2 Sem NoExit) l0.

(* 'abstract' semantics of linear instruction *)
Definition ALSem (Sem: linstr -> L -> itree E L)
  (TryFnd: L -> option linstr) : L -> itree E L :=
  fun l => match TryFnd l with
           | Some i => Sem i l
           | None => throw err                                         
           end.  

(* generic iterator specialized to a semantics of instructions. used
   for Linear Core Semantics *)
Definition SCntr
  (Sem: linstr -> L -> itree E L) (TryFnd: L -> option linstr)
  (NoExit: L -> bool) (pe: L + L) : itree E (L + L) :=
  ACntr2 (ALSem Sem TryFnd) NoExit pe.
         
(* iterates SCntr *)
Definition SCntrI
  (Sem: linstr -> L -> itree E L) (TryFnd: L -> option linstr)
  (NoExit: L -> bool) (l0: L) : itree E L :=
  aloop (@SCntr Sem TryFnd NoExit) l0.

End AbsIterators.


Definition halt_pred (l: lpoint) : option bool :=
  let fn := fst l in
  let lbl := snd l in
  let plc := lfenv fn in
  match plc with
  | Some lc => Some (is_final lc lbl) 
  | _ => None
  end.             

Definition not_possible (fn: funname) (n: nat) : bool :=
  let lc := lfenv fn in
  match lc with
  | Some lc => if (length lc < n) then true else false 
  | _ => true
  end.             

Definition not_locally_possible (fn fn0: funname) (n: nat) : bool :=
  ((fn == fn0) == false) || 
  let lc := lfenv fn in
  match lc with
  | Some lc => if (length lc < n) then true else false 
  | _ => true
  end.             

Definition loc_possible (fn fn0: funname) (n: nat) : bool :=
  (fn == fn0) && 
  let lc := lfenv fn in
  match lc with
  | Some lc => length lc < n
  | _ => false 
  end.             

Definition find_linstr_in_fun (lp : lpoint) : option linstr :=
  match lfenv (fst lp) with
  | Some lc => find_linstr lc (snd lp)
  | _ => None
  end.                         

(***** LOCAL ITERATORS *)

(* the 'local' iteration body for the Intermediate semantics. nS and
   nE are the start and end points in the fn linear code wrt to which
   execution is contextual. *)
Definition LACntr_weak (Sem: lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) :
  (lpoint + lpoint) -> itree E (lpoint + lpoint) :=
  ACntr2 Sem
    (* exit condition: whenever either it jumps to another function,
       it gets out of range, or it makes a recursive call (n0 = 0).
       note: the last disjunct should cover recursive calls, as 0 is
       the entry point in every function; and it actually makes the
       funname check redundant. *)
    (fun '(fn0, n0) =>
       (fn == fn0) && (nS <= n0) && (n0 < nE) && (0 < n0)).

Definition LACntr (Sem: lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) :
  (lpoint + lpoint) -> itree E (lpoint + lpoint) :=
  ACntr2 Sem
    (* exit condition: whenever either it jumps to another function,
       it gets out of range, or it makes a recursive call (n0 = 0).
       note: the last disjunct should cover recursive calls, as 0 is
       the entry point in every function; and it actually makes the
       funname check redundant. *)
    (fun '(fn0, n0) =>
       (loc_possible fn fn0 nE) && (nS <= n0) && (n0 < nE) && (0 < n0)).

(* iterates LACntr *)
Definition LACntrI (Sem: lpoint -> itree E lpoint)   
  (fn: funname) (nS nE: nat) (lp0: lpoint) : itree E lpoint :=
  aloop (@LACntr Sem fn nS nE) lp0. (* (fn, nS). *)

(* specialized version, using ALSem. used for Instrumented
    Function-Localised Linear Semantics. *)
Definition LCntr (Sem: linstr -> lpoint -> itree E lpoint)
  (fn: funname) (nS nE: nat) :
  (lpoint + lpoint) -> itree E (lpoint + lpoint) :=
  LACntr (ALSem Sem find_linstr_in_fun) fn nS nE.

(* iterate LCntr *)
Definition LCntrI (Sem: linstr -> lpoint -> itree E lpoint) 
  (fn: funname) (nS nE: nat) (lp0: lpoint) : itree E lpoint :=
  aloop (@LCntr Sem fn nS nE) lp0. (* (fn, nS). *)


(***** GLOBAL ITERATORS *)

(* the 'global' iteration body for the Linear semantics. used for
   Instrumented Global Linear Semantics *)
Definition GCntr (Sem: linstr -> lpoint -> itree E lpoint) :
  (lpoint + lpoint) -> itree E (lpoint + lpoint) :=
  SCntr Sem find_linstr_in_fun halt_pred.

(* iterate GCntr *)
Definition GCntrI (Sem: linstr -> lpoint -> itree E lpoint)
  (lp0: lpoint) : itree E lpoint :=
  aloop (@GCntr Sem) lp0.

(* the core semantics of linear instructions, based on linstr_sem *)
Definition isem_li_core (i : linstr) (s: LState) : itree E LState :=
  match i with (MkLI _ ir) => iresult (linstr_sem ir s) s end.


Section CoreLinSem.
Context {readPC: LState -> option lpoint}.

Definition state_find_linstr (st: LState) : option linstr :=
  match (readPC st) with
  | Some l => find_linstr_in_fun l
  | None => None
  end.            

Definition halt_state_pred (st: LState) : option bool :=
  match (readPC st) with
  | Some l => halt_pred l
  | _ => None
  end.         

(* LINEAR CORE SEMANTICS (with explicit state) *)
(* iterative core semantics body, relying on Hlt (halting condition)
   and readPC (to find the next instruction from the state) *)
Definition isem_lcmd_core_body :
  (LState + LState) -> itree E (LState + LState) :=
  SCntr isem_li_core state_find_linstr halt_state_pred.

(* iterative core semantics of a linear program, from any state *)
Definition isem_lcmd_core (st: LState) : itree E LState :=
  aloop isem_lcmd_core_body st.

End CoreLinSem.


Section InstrumentedSem.

Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}.

Context {code_length: funname -> nat}.

(* abstract core semantics of linear instructions, hiding the state *)
Definition isem_li_acore (i : linstr) : itree E unit :=
  s1 <- trigger (@Get LState) ;;
  s2 <- isem_li_core i s1 ;;
  trigger (@Put LState s2).

Notation RA_read := (trigger RA_readE).
Notation RA_is x := (trigger (RA_isE x)).
Notation PC_is x := (trigger (PC_isE x)).
Notation PC_ret x := (PC_is x ;; Ret x).
Notation EvalLoc x := (trigger (EvalLocE x)).
Notation EvalExp x := (trigger (EvalExpE x)).
Notation FindLabel x := (trigger (FindLabelE x)).

(* instrumented semantics, used to highlight control flow information
   on top of the core semantics *)
Definition lflow_abs (t: itree E unit)
  (i : linstr) (l0 : lpoint) : itree E lpoint :=
  let: (MkLI ii ir) := i in
  match ir with
  | Lopn xs o es => t ;; PC_ret (incr_lpoint l0)
  | Lsyscall o => t ;; PC_ret (incr_lpoint l0)
  | Lcall o d => x <- FindLabel d ;; t ;;
                 RA_is (incr_lpoint l0) ;; PC_ret x 
  | Lret => x <- RA_read ;; t ;; PC_ret x 
  | Lalign => t ;; PC_ret (incr_lpoint l0)
  | Llabel x y => t ;; PC_ret (incr_lpoint l0)
  | Lgoto d => x <- FindLabel d ;; t ;; PC_ret x
  | Ligoto e => d <- EvalLoc e ;; x <- FindLabel d ;;
                t ;; PC_ret x 
  | LstoreLabel x lbl => t ;; PC_ret (incr_lpoint l0)
  | Lcond e lbl => b <- EvalExp e ;;
                   if b then x <- FindLabel (fst l0, lbl) ;; t ;; PC_ret x
                   else t ;; PC_ret (incr_lpoint l0)
end.

(* semantics of linear instruction, instrumented with control-flow
   abstraction *)
Definition isem_li_flow (i : linstr) (l0: lpoint) : itree E lpoint :=
  PC_is l0 ;; lflow_abs (isem_li_acore i) i l0.

(* instrumented semantics of linear instruction abstracted from
   instructions *)
Definition isem_li_aflow (l0: lpoint) : itree E lpoint :=
  ALSem isem_li_flow find_linstr_in_fun l0.

(* combinator for sequential linear commands; only meaningful when
   lcmd is straightline code (used in Intermediate) *)
Fixpoint lcmd_seq {T} (S: linstr -> T -> itree E T)
  (lc: lcmd) (l0: T) : itree E T :=
  match lc with
  | nil => Ret l0
  | i :: lc0 =>
      l1 <- S i l0 ;; lcmd_seq S lc0 l1
  end.             

(* only meaningful when lcmd is straightline code *)
Definition isem_lcmd_seq_flow (lc: lcmd) (l0: lpoint) : itree E lpoint :=
  lcmd_seq isem_li_flow lc l0.

(* only meaningful when lcmd is straightline code *)
Definition isem_lcmd_seq_acore (lc: lcmd) : itree E unit :=
  lcmd_seq (fun li _ => isem_li_acore li) lc tt.

(* only meaningful when lcmd is straightline code *)
Definition isem_lcmd_seq_inl_flow (lc: lcmd) (l0: lpoint) :
  itree E (lpoint + lpoint) :=
  lcmd_seq (fun li pp =>
              match pp with
              | inl l1 => l2 <- isem_li_flow li l1 ;; Ret (inl l2)
              | _ => throw err end) lc 
    (inl l0).


(***** INSTRUMENTED GLOBAL LINEAR SEMANTICS *)

(* iterative flow semantics body *)
Definition isem_lcmd_flow_body :
  (lpoint + lpoint) -> itree E (lpoint + lpoint) := GCntr isem_li_flow.

(* iterative flow semantics of a linear program, from any starting point *)
Definition isem_lcmd_flow (lp : lpoint) : itree E lpoint :=
  aloop isem_lcmd_flow_body lp.

(* iterative flow semantics of a linear function from its entry point
*)
Definition isem_lfun_flow (fn: funname) : itree E lpoint :=
  isem_lcmd_flow (fn, 0).


(***** INSTRUMENTED FUNCTION-LOCALISED LINEAR SEMANTICS *)

(* note: the exit condition is the local one, defined in LACntr; so it
   covers all function calls (inclusive of recursive ones to fn) *)
Definition isem_lfun_lfloc_body (fn: funname) :
  (lpoint + lpoint) -> itree E (lpoint + lpoint) :=
  LCntr isem_li_flow fn 0 (code_length fn).

(* iterates over all internal jumps *)
Definition isem_lfun_lfloc (fn: funname) (lp0: lpoint) :
  itree E lpoint := aloop (isem_lfun_lfloc_body fn) lp0.

Definition llp2funname (pe: lpoint + lpoint) : funname :=
  match pe with | inl l => fst l | inr l => fst l end.

(* note: here the exit condition is the global one *)
Definition isem_lfloc_body :
  (lpoint + lpoint) -> itree E (lpoint + lpoint) :=
  fun pe => let fn := llp2funname pe in
      ACntr2 (isem_lfun_lfloc fn) halt_pred pe.                

(* iterates on the function calls *)
Definition isem_lfloc (lp0: lpoint) :
  itree E lpoint := aloop isem_lfloc_body lp0.
                    
End InstrumentedSem.

End LinSem. 

  
(***** HANDLERS *)

(* LFindE handling (defined wrt lfenv ) *)
  Definition handle_LFind {E0} {XE: ErrEvent -< E0}
    {T} (e: LFindE T) : itree E0 T :=
  match e with    
  | FindLabelE rlbl =>
      match lfenv (fst rlbl) with
      | Some lc =>
          n <- err_result (fun _ => err) (find_label (snd rlbl) lc) ;;
          Ret (fst rlbl, n)
      | _ => throw err
      end             
  end.   

Definition interp_LFind {E0} {XE: ErrEvent -< E0}
    {T} (t: itree (LFindE +' E0) T) : itree E0 T :=
  interp (ext_handler (@handle_LFind _ _)) t.
(*  interp (case_ (@handle_LFind) id_) t.   *)                          


Section HandleLEval.
  
Context {readRA : LState -> option lpoint}
        {readPC: LState -> option lpoint}
        {evalLoc : LState -> rexpr -> option remote_label}
        {evalExp : LState -> fexpr -> option bool}.

(* LEvalE handling for Linear and Intermediate *)
Definition handle_LEval {E0} {XE: ErrEvent -< E0} {XSl: @stateE LState -< E0}
  {T} (e: LEvalE T) : itree E0 T :=
  match e with    
  | RA_readE => st <- trigger (@Get LState) ;;
                err_option err (readRA st) 
  | RA_isE l => st <- trigger (@Get LState) ;;
                match (readRA st == Some l) with
                | true => Ret tt 
                | _ => throw err 
                end
  | PC_isE l => st <- trigger (@Get LState) ;;
                match (readPC st == Some l) with
                | true => Ret tt
                | _ => throw err
                end       
  | EvalLocE e => st <- trigger (@Get LState) ;;
                  err_option err (evalLoc st e)            
  | EvalExpE e => st <- trigger (@Get LState) ;;
                  err_option err (evalExp st e)            
  end.   

Definition interp_LEval {E0} {XE: ErrEvent -< E0}
  {XSl: @stateE LState -< E0} {T}
  (t: itree (LEvalE +' E0) T) : itree E0 T :=
  interp (ext_handler (@handle_LEval _ _ _)) t.

Definition interp_LInstr {E0} {XE: ErrEvent -< E0}
  {XSl: @stateE LState -< E0} {T}
  (t: itree (LEvalE +' LFindE +' E0) T) : itree E0 T :=
  interp_LFind (interp_LEval t).

End HandleLEval.


Definition LLeaf_ok (li: linstr) : bool :=
  match li with
  | MkLI ii (Lopn xs o es) => true 
  | MkLI ii (Lsyscall o) => true      
  | _ => false
  end.   

Definition LIf1Node_ok (li1 li2: linstr) : bool :=
  match (li1, li2) with
  | (MkLI ii (Lcond e lbl), MkLI ii' (Llabel InternalLabel lbl')) =>
      lbl == lbl'
  | _ => false
  end.         

Definition LIfNode_ok (li1 li2 li3 li4: linstr) : bool :=
  match (li1, li2, li3, li4) with
  | (MkLI _ (Lcond e lbl),
     MkLI _ (Lgoto (fn, lbl1)),
     MkLI _ (Llabel InternalLabel lbl'),  
     MkLI _ (Llabel InternalLabel lbl1')) =>
           (lbl == lbl') && (lbl1 == lbl1')
  | _ => false
  end.         

Definition LWhileTNode_ok (li1 li2: linstr) : bool :=
  match (li1, li2) with
  | (MkLI _ (Llabel InternalLabel lbl1), MkLI _ (Lgoto (fn, lbl2))) =>
      lbl1 == lbl2 
  | _ => false
  end.         

Definition LWhileNode_ok (li1 li2 li3 li4: linstr) : bool :=
  match (li1, li2, li3, li4) with
  | (MkLI _ (Lgoto (fn, lbl)),
     MkLI _ (Llabel InternalLabel lbl1),
     MkLI _ (Llabel InternalLabel lbl'),
     MkLI _ (Lcond e lbl1')) =>
           (lbl == lbl') && (lbl1 == lbl1')
  | _ => false
  end.         
      
Definition LWhile1Node_ok (li1 li2: linstr) : bool :=
  match (li1, li2) with
  | (MkLI _ (Llabel InternalLabel lbl1), MkLI _ (Lcond e lbl2)) =>
      lbl1 == lbl2 
  | _ => false
  end.         

Definition LCallNode_ok (nb na: nat) (fn: funname)
  (lcb lca: lcmd) (li1 li2: linstr) :
  bool :=
  if (length lcb == nb)
  then if (length lca == na)   
       then match (li1, li2) with
       | (MkLI ii0 (Lcall _ (fn0, xH)),
           MkLI ii1 (Llabel ExternalLabel _)) => fn == fn0
       | _ => false
       end         
       else false
  else false.            


Section IntermediateSem.

(* the return value is not really used; it is the instruction after
   the call, but interpretation inlines the function code. *)  
Notation LCall := (callE funname lpoint).

Context {code_length: funname -> nat}.
Context {E} {XE: ErrEvent -< E}.

Definition in_btw (n1 n2 n3: nat) : bool :=
  (n1 <= n3) && (n3 < n2). 

Definition at_start (n1 _ n3: nat) : bool :=
  n3 == n1.

Definition Bind_cmb : (lpoint -> itree (LCall +' E) lpoint) ->
        (lpoint -> itree (LCall +' E) lpoint) ->
        nat -> nat -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint :=
  fun f g _ _ _ _ x => ITree.bind (f x) g.

Definition Switch_cmb : (lpoint -> itree (LCall +' E) lpoint) ->
        (lpoint -> itree (LCall +' E) lpoint) ->
        nat -> nat -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint :=
  fun f g n1 n2 n3 n4 '(fn0, n0) =>
       if in_btw n1 n2 n0 then f (fn0, n0)
       else if in_btw n3 n4 n0 then g (fn0, n0)
       else throw err.

Definition Id_cmb {E0} : (lpoint -> itree E0 lpoint) ->
  funname -> nat -> nat -> lpoint -> itree E0 lpoint :=
  fun f _ _ _ => f.

(* parameterized semantics of intermediate instructions and commands *)
(* IBT -> (L) at_start (F) in_btw
   CNT -> (L) LACntrI (F) id    
   CNN -> (L) bind (G) switch 
   LC -> isem_lcmd_seq_flow (in principle, isem_lcmd_acore could also do).  
   LSI -> isem_li_aflow 
 *)
Fixpoint lsem_i_imedA 
  (IBT: nat -> nat -> nat -> bool)
  (CNT: (lpoint -> itree (LCall +' E) lpoint) ->
         funname -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (CNN: (lpoint -> itree (LCall +' E) lpoint) ->
        (lpoint -> itree (LCall +' E) lpoint) ->
        nat -> nat -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  let '(pS, _) := plS in 
  let '(pE, _) := plE in 
  CNT 
  (fun lpA =>
  let '(fnA, pA) := lpA in
  let LRec := @lsem_cmd_imedA IBT CNT CNN LSC LSI in
(*  if fn == fst lpA then *)
  match lt with
  | LErrLeaf _ => throw err
  | LLeaf _ (MkLI ii ir) => match LLeaf_ok (MkLI ii ir) with 
                            | false => throw err
                            | true => LSI lpA end                        
  | LIf1Node _ (p1, _) li1 lc li2 =>
      (* note: fst plE = S p1 *)
      match LIf1Node_ok li1 li2 with
      | false => throw err
      | true => 
             if (pA == pS) || (pA == p1) then LSI lpA
             else if IBT (S pS) p1 pA then LRec _ _ _ lc lpA
             else throw err 
      end
  | LIfNode _ (p1, _) (p2, _) li1 lc2 li2 li3 lc1 li4 => 
      (* note: fst plE = S p2 *)
      match LIfNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true => 
            if (pA == pS) || (pA == p1) ||
               (pA == S p1) || (pA == p2) then LSI lpA
            else if IBT (S pS) p1 pA then LRec _ _ _ lc2 lpA
            else if IBT (S (S p1)) p2 pA then LRec _ _ _ lc1 lpA
            else throw err 
      end     
  | LWhileTNode _ (p1, _) (p2, _) b ii li1 lc1 lc2 li2 =>
      (* note: fst plE = S p2 *)
      match LWhileTNode_ok li1 li2 with
      | false => throw err
      | true => 
            let bn := if b then 1 else 0 in  
            if (pA == pS) || (pA == pS + bn) || (pA == p2) then LSI lpA
            else if IBT (S (pS + bn)) p1 pA then LRec _ _ _ lc1 lpA
            else if IBT p1 p2 pA then LRec _ _ _ lc2 lpA
            else throw err 
      end
  | LWhileFNode _ _ lc => LRec _ _ _ lc lpA
  | LWhile1Node _ (p1, _) b ii li1 lc li2 =>
      (* note: fst plE = S p1 *)
      match LWhile1Node_ok li1 li2 with
      | false => throw err
      | true => 
            let bn := if b then 1 else 0 in   
            if (pA == pS) || (pA == pS + bn) || (pA == p1) then LSI lpA
            else if IBT (S (pS + bn)) p1 pA then LRec _ _ _ lc lpA
            else throw err 
      end
  | LWhileNode _ (p1, _) (p2, _) b ii li1 li2 lc2 li3 lc1 li4 =>
      (* note: fst plE = S p2 *)
      match LWhileNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true =>
            let bn := if b then 1 else 0 in
            let pS1 := pS + bn in  
            if (pA == pS) || (pA == pS1) || (pA == S pS1)
               || (pA == p1) || (pA == p2) then LSI lpA
            else if IBT (S (S (pS1))) p1 pA then LRec _ _ _ lc2 lpA
            else if IBT (S p1) p2 pA then LRec _ _ _ lc1 lpA
            else throw err 
      end        
  | LCallNode _ nb na fn' lc_bef lc_aft li1 li2 =>
      match LCallNode_ok nb na fn' lc_bef lc_aft li1 li2 with
      | false => throw err  
      | true => LSC (lc_bef ++ [li1]) lpA ;;
                l1 <- (trigger_inl1 (Call fn')) ;;
                LSC (li2 :: lc_aft) l1 ;;
                Ret (fn, pS + nb + S (S na))            
      end 
  end) fn pS pE    
with lsem_cmd_imedA 
  (IBT: nat -> nat -> nat -> bool)
  (CNT: (lpoint -> itree (LCall +' E) lpoint) ->
         funname -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (CNN: (lpoint -> itree (LCall +' E) lpoint) ->
        (lpoint -> itree (LCall +' E) lpoint) ->
        nat -> nat -> nat -> nat -> lpoint -> itree (LCall +' E) lpoint)
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
   fun lpA =>      
   match lt with
   | LListNil pl0 => if snd lpA == fst pl0 then Ret (fn, fst pl0)
                     else throw err                               
   | LListCons _ (p1, _) (p2, _) lt ltl =>
       CNN (@lsem_i_imedA IBT CNT CNN LSC LSI _ _ _ lt)
         (@lsem_cmd_imedA IBT CNT CNN LSC LSI _ _ _ ltl)
         (fst plS) p1 p1 p2 lpA 
   end.                   

(* parameterized intermediate local semantics of
   instructions. NOTE: here at_start can replace in_btw. *)
Definition lsem_i_imedAL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  lsem_i_imedA in_btw LACntrI Bind_cmb LSC LSI lt.

(* parameterized intermediate local semantics of
   commands. NOTE: here at_start can replace in_btw. *)
Definition lsem_cmd_imedAL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  lsem_cmd_imedA in_btw LACntrI Bind_cmb LSC LSI lt.

Definition lsem_fun_imed_auxAL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | @LTFun _ _ _ lbl pl1 lc1 lc2 n1 lt =>
    let clen := code_length fn in
    let pre_l := List.length lc1 in
    if (n1 == pre_l) && (fst pl1 == (pre_l + clen)) then
      lp0 <- LSC lc1 (fn, 0) ;;
      lp1 <- @lsem_cmd_imedAL LSC LSI _ _ _ lt lp0 ;; LSC lc2 lp1 
    else throw err                                               
  end.                   

(* alternative version, without checks *)
Definition lsem_fun_imed_auxAL0
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | LTFun lbl pl1 lc1 lc2 lt =>
      lp0 <- LSC lc1 (fn, 0) ;;
      lp1 <- @lsem_cmd_imedAL LSC LSI _ _ _ lt lp0 ;; LSC lc2 lp1 
  end.                   

(* parameterized intermediate local semantics of functions. *)
Definition lsem_fun_imedAL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) : itree (LCall +' E) lpoint :=
  fd <- err_def_option (ifenv fn) ;;
  lsem_fun_imed_auxAL LSC LSI fd.

(* parameterized intermediate function-globablized semantics of
   instructions. *)
Definition lsem_i_imedAF 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  lsem_i_imedA in_btw Id_cmb Switch_cmb LSC LSI lt.

(* parameterized intermediate function-globablized semantics of
   commands. *)
Definition lsem_cmd_imedAF  
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  lsem_cmd_imedA in_btw Id_cmb Switch_cmb LSC LSI lt.

(* currently preferred version *)
Definition lsem_fun_imed_auxAF 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | @LTFun _ _ _ lbl pl1 lc1 lc2 n1 lt =>
    let clen := code_length fn in
    let pre_l := List.length lc1 in
    if (n1 == pre_l) && (fst pl1 == (pre_l + clen)) then
       lp0 <- LSC lc1 (fn, 0) ;;
       lp1 <- LACntrI (@lsem_cmd_imedAF LSC LSI fn (n1, lbl) pl1 lt)
                fn pre_l (fst pl1) lp0 ;; LSC lc2 lp1
    else throw err                                               
  end.                   

(* alternative version *)
Definition lsem_fun_imed_auxAF0 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | @LTFun _ _ _ lbl pl1 lc1 lc2 n1 lt =>
    let clen := code_length fn in 
    let pre_l := List.length lc1 in
    let epi_l := List.length lc2 in
    let nE := clen + List.length lc1 + List.length lc2 in  
    LACntrI (fun lpA => lp0 <- LSC lc1 lpA ;;
       lp1 <- @lsem_cmd_imedAF LSC LSI fn (n1, lbl) pl1 lt lp0 ;; LSC lc2 lp1)
       fn 0 nE (fn, 0) 
  end.                   

(* parameterized intermediate function-globablised semantics of functions. *)
Definition lsem_fun_imedAF 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) : itree (LCall +' E) lpoint :=
  fd <- err_def_option (ifenv fn) ;;
  lsem_fun_imed_auxAF LSC LSI fd.


(***** INTERMEDIATE LOCAL SEMANTICS *)
(* introduce an iteration for each Intermediate instruction *)

Section LInterSemDef.
Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}.
  
Definition lsem_i_imedL  
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  @lsem_i_imedAL isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.
               
Definition lsem_cmd_imedL  
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  @lsem_cmd_imedAL isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.

Definition lsem_fun_imedL  
  (fn: funname) : itree (LCall +' E) lpoint :=
  lsem_fun_imedAL isem_lcmd_seq_flow isem_li_aflow fn.

Definition handle_LRecL : LCall ~> itree (LCall +' E) :=
  fun T  (rc : callE _ _ T) =>
   match rc with
   | Call fn => lsem_fun_imedL fn
   end.                            

(* LRec interpretation *)
Definition lsem_imed_recL (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) (lp0: lpoint) : itree E lpoint := 
  interp_mrec handle_LRecL (lsem_cmd_imedL lt lp0).

End LInterSemDef.


(***** INTERMEDIATE FUNCTION-GLOBALISED SEMANTICS *)
(* introduces an iteration for each function *)

Section FInterSemDef.
Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}.
  
Definition lsem_i_imedF  
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  @lsem_i_imedAF 
    isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.
               
Definition lsem_cmd_imedF  
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : lpoint -> itree (LCall +' E) lpoint :=
  @lsem_cmd_imedAF
    isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.

Definition lsem_fun_imedF  
  (fn: funname) : itree (LCall +' E) lpoint :=
  lsem_fun_imedAF 
    isem_lcmd_seq_flow isem_li_aflow fn.

Definition handle_LRecF : LCall ~> itree (LCall +' E) :=
  fun T  (rc : callE _ _ T) =>
   match rc with
   | Call fn => lsem_fun_imedF fn
   end.                            

(* LRec interpretation *)
Definition lsem_imed_recF (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) (lp0: lpoint) : itree E lpoint := 
  interp_mrec handle_LRecF (lsem_cmd_imedF lt lp0).

End FInterSemDef.


Section Lemmas.
  (* TODO: The points to prove *) 
Context {readRA : LState -> option lpoint}
        {readPC: LState -> option lpoint}
        {evalLoc : LState -> rexpr -> option remote_label}
        {evalExp : LState -> fexpr -> option bool}.

(* equivalence between core and instrumented global semantics; where
   most of the low-level effort will go. notice that in Instrumented
   events LEval and LFind need to be handled first, even if they do
   not actually change the state. *)
Lemma core2instrumented_global_lfun (fn: funname) (st: LState) :
  readPC st = Some (fn, 0) ->
  eutt (fun x y => x = fst y) (@isem_lcmd_core E _ readPC st)
    (run_state (@interp_LInstr readRA readPC evalLoc evalExp _ _ _ _
    (@isem_lfun_flow (LEvalE +' LFindE +' @stateE LState +' E) _ _ _ _ fn)) st).
Admitted.


Section Lemmas1.
Context {XF: LFindE -< E} {XL: LEvalE -< E }.

(* equivalence between instrumented global and function-localised
   semantics; se we can semantically distinguish between internal
   jumps, controlled by a function-level iterations, and external
   jumps, controlled by the global iteration. *)
Lemma instrumented_local2instrumented_funloc_lfun {XS: stateE LState -< E}
  (fn: funname) :
  eutt eq (@isem_lfun_flow E _ _ _ _ fn)
    (@isem_lfloc E _ _ _ _ code_length (fn, 0)).  
Admitted. 
  
(*******************************************************************)

(*
Lemma LACntrI_cond_error 
  (body: lpoint -> itree E lpoint) (fn : funname)
  (n0 n1: nat) (lp0: lpoint)
  (A1: (loc_possible fn (lp0.1) n1) = false) :
  aloop (LACntr body fn n0 n1) lp0 ≈ throw err.
Proof.
  destruct lp0 as [fn0 n2]; simpl in *.
  unfold aloop, loop, CategoryOps.cat, Cat_Kleisli; simpl.
  unfold inr_; simpl.
  rewrite bind_ret_l.
  unfold CategoryOps.iter, Iter_Kleisli, Basics.iter, MonadIter_itree; simpl.
  rewrite unfold_iter.
  rewrite bind_bind.
  unfold LACntr; simpl.
  unfold ACntr; simpl.
  rewrite A1. simpl.
  (**)
  rewrite bind_vis.
  eapply eqit_Vis.
  intro u. destruct u.
Qed.  
*)

Lemma LACntrI_match_error {XS: stateE LState -< E}
  (body1 body2: lpoint -> itree E lpoint) (cond: bool)
  (fn : funname) (n0 n1: nat) (lp0: lpoint)
  (A1: cond = false) :
  aloop (LACntr (λ (lpA: lpoint),
          if cond then body1 lpA else throw err) fn n0 n1) lp0 
   ≈ aloop (LACntr (λ (lpA: lpoint),
          if cond then body2 lpA else throw err) fn n0 n1) lp0. 
Proof.
  destruct lp0 as [fn0 n2]; simpl in *. 
  unfold aloop, loop, CategoryOps.cat, Cat_Kleisli; simpl.
  unfold inr_; simpl.
  setoid_rewrite bind_ret_l.
  unfold CategoryOps.iter, Iter_Kleisli, Basics.iter, MonadIter_itree; simpl.
  setoid_rewrite unfold_iter.
  setoid_rewrite bind_bind.
  unfold LACntr; simpl.
  unfold ACntr; simpl.
  destruct (not_locally_possible fn fn0 n1) eqn: was_e; simpl.
  { destruct (loc_possible fn fn0 n1 && (n0 <= n2)
              && (n2 < n1) && (0 < n2)) eqn: was_e1; simpl;
      try reflexivity.
    - setoid_rewrite A1; simpl.
      setoid_rewrite bind_bind.
      setoid_rewrite bind_vis.
      eapply eqit_Vis.
      intro u. destruct u.
    - setoid_rewrite bind_ret_l; simpl.
      unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
        CategoryOps.cat; simpl.
      setoid_rewrite bind_bind.
      setoid_rewrite bind_ret_l; simpl; try reflexivity.    
      setoid_rewrite bind_ret_l; simpl; try reflexivity.    
  }
  { destruct (loc_possible fn fn0 n1 && (n0 <= n2)
              && (n2 < n1) && (0 < n2)) eqn: was_e1; simpl;
      try reflexivity.
    - setoid_rewrite A1; simpl.
      setoid_rewrite bind_bind.
      setoid_rewrite bind_vis.
      eapply eqit_Vis.
      intro u. destruct u.
    - setoid_rewrite bind_ret_l; simpl.
      unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
        CategoryOps.cat; simpl.
      setoid_rewrite bind_bind.
      setoid_rewrite bind_ret_l; simpl; try reflexivity.    
      setoid_rewrite bind_ret_l; simpl; try reflexivity.    
  }
Qed.


(* this is A1. similar to loop_vanishing_2 *)
Lemma aloop_aux1 {XS: stateE LState -< E}
  (fn fn0 : funname) (n0 n1 n2: nat) (l0 l1: label)
  (lcm1: LTreeList fn (incrP1 (n0, l0)) (n1, l1)) :
 let lp0 := (fn0, n2) in  
 (* PO2 *)
  aloop
     (LACntr
        (aloop
          (LACntr
             (λ '((_, pA) as lpA),
                  if (pA == n0) || (pA == n1)
                  then isem_li_aflow lpA
                  else if in_btw n0.+1 n1 pA
                       then lsem_cmd_imedF lcm1 lpA
                       else throw err)
             fn n0 n1.+1)) fn n0 n1.+1) lp0 ≈
  (* PO1 *)  
  aloop
      (LACntr
         (λ '((_, pA) as lpA),
              if (pA == n0) || (pA == n1)
              then isem_li_aflow lpA
              else
                if in_btw n0.+1 n1 pA
                then lsem_cmd_imedF lcm1 lpA
                else throw err) fn n0 n1.+1) lp0.
Proof.
  unfold LACntr at 1.
  set LAL := (ACntr2 (aloop _)).
  unfold aloop in LAL.
  unfold ACntr2, ACntr in LAL.
  
  unfold aloop.
(*  
  unfold LACntr at 1 3.
  unfold ACntr2, ACntr; simpl.
  unfold case_sum; simpl.
*)  
Admitted. 

(* this is A2. should work either on the right-hand side, pushing the
   inner loop inwards, or on the left-hand side, pushing the local
   loop outwards. *)
Lemma aloop_aux2 {XS: stateE LState -< E}
  (fn fn0 : funname) (n0 n1 n2: nat) (l0 l1: label)
  (lcm1: LTreeList fn (incrP1 (n0, l0)) (n1, l1))
(*  (A1: not_locally_possible fn fn0 n1 == false) *) :
 let lp0 := (fn0, n2) in  
 (* PO2 *)
  aloop
     (LACntr
        (aloop
          (LACntr
             (λ '((_, pA) as lpA),
                  if (pA == n0) || (pA == n1)
                  then isem_li_aflow lpA
                  else if in_btw n0.+1 n1 pA
                       then lsem_cmd_imedF lcm1 lpA else throw err)
             fn n0 n1.+1)) fn n0 n1.+1) lp0 ≈
  (* PI0 *)  
  aloop
      (LACntr
         (λ '((_, pA) as lpA),
              if (pA == n0) || (pA == n1)
              then isem_li_aflow lpA
              else
                if in_btw n0.+1 n1 pA
                then aloop (LACntr (lsem_cmd_imedF lcm1) fn n0.+1 n1) lpA
                else throw err) fn n0 n1.+1) lp0.
Proof.
  unfold LACntr, ACntr; simpl.
Admitted. 


(* equivalence for commands. but NOTE: this would not hold without the
   top-level iteration on the left *)
Lemma intemediate_local2intermediate_funglobal_lcmd_aux
  {XS: stateE LState -< E} (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) (lp0: lpoint) :
  eutt eq (lsem_cmd_imedL lt lp0)
          (LACntrI (lsem_cmd_imedF lt) fn (fst plS) (fst plE) lp0).
Proof.
(*  unfold lsem_imed_recL, isem_lcmd_flow, lsem_imed_recF; simpl. *)
  revert lp0.
  revert lt.
  revert plS plE.
  
  set (Pt := fun plS plE (lt0: LTree fn plS plE) =>
             forall lp0, eutt eq (lsem_i_imedL lt0 lp0)
                 (LACntrI (lsem_i_imedF lt0)
                    fn (fst plS) (fst plE) lp0)). 
  set (Ptl := fun plS plE (lts: LTreeList fn plS plE) =>
             forall lp0, eutt eq (lsem_cmd_imedL lts lp0)
                 (LACntrI (lsem_cmd_imedF lts)
                    fn (fst plS) (fst plE) lp0)). 
  eapply (@LTreeList_mut asm_op _ fn Pt Ptl). 
  { intros; subst Pt; simpl; intros.
    unfold lsem_i_imedL, lsem_i_imedF; simpl.
    unfold lsem_i_imedAL, lsem_i_imedAF; simpl.
    destruct pl eqn: was_pl ; simpl.
    unfold Id_cmb; simpl.
    reflexivity.
  }
  { intros; subst Pt; simpl; intros.
    unfold lsem_i_imedL, lsem_i_imedF; simpl.
    unfold lsem_i_imedAL, lsem_i_imedAF; simpl.
    destruct pl eqn: was_pl ; simpl.
    unfold Id_cmb; simpl.
    reflexivity.
  }
  { intros; subst Pt; simpl; intros.
    unfold Ptl in *.
    unfold lsem_i_imedL, lsem_i_imedAL; simpl.
    unfold lsem_i_imedF, lsem_i_imedAF; simpl. 
    destruct pl0 as [n0 l0] eqn: was_pl0 ; simpl.
    unfold Id_cmb at 1; simpl.
    unfold LACntrI at 1 3; simpl.
    unfold aloop.
    unfold lsem_cmd_imedL, lsem_cmd_imedAL in H; simpl in *.
    unfold lsem_cmd_imedF, lsem_cmd_imedAF in H; simpl in *.
    unfold LACntrI in H at 2; unfold aloop in H; simpl in *.
    destruct pl1 as [n1 l1] eqn: was_pl1; simpl.
    simpl in *.
    destruct lp0 as [fn0 nA] eqn: was_lp0; simpl in *.
  
    destruct (LIf1Node_ok la_cond1 la_lbl1) eqn: was_E1;
      try reflexivity.

    (* strategy: double the outer loop on the left, 
                 push the inner loop inward on the left, 
                 apply the inductive hyp H to the right, 
                 reflexivity. *)
    
    set PL := (fun '((_, pA) as lpA) => _).
    set PO := (fun '((_, pA) as lpA) => _).
  (*  set PO0 := aloop (LACntr PO fn n n0.+1). *)
    set PO1 := aloop (LACntr PO fn n0 n1.+1).
    set PO2 := aloop (LACntr PO1 fn n0 n1.+1).

    (* we want transform the right-hand side tree (PO, the non-local
       one) to get it into a shape where the induction hyp is
       usable. first we introduce a (redundant) inner loop. should be
       similar to loop_vanishing_2. *)
    assert (eutt eq (PO2 lp0) (PO1 lp0)) as A1.
    { subst PO2 PO1 PO; simpl.
      subst lp0; eapply aloop_aux1.
    }
    
    set PI := (λ '((_, pA) as lpA),
                  if (pA == n0) || (pA == n1)
                  then isem_li_aflow lpA
                  else
                   if in_btw n0.+1 n1 pA
                   then aloop (LACntr (lsem_cmd_imedA in_btw Id_cmb
                                    Switch_cmb isem_lcmd_seq_flow
                                    isem_li_aflow lcm1)
                                 fn n0.+1 n1) lpA
                   else throw err).
    set PI0 := aloop (LACntr PI fn n0 n1.+1).

    (* we now want to push this loop further inward, to match a local
       one. maybe could just prove PO1 ~~ PI? probably not. *)
    assert (eutt eq (PO2 lp0) (PI0 lp0)) as A2.
    { subst PO2 PO1 PO PI0 PI; simpl.
      clear A1. subst PL.
      subst lp0; eapply aloop_aux2.
    }
    
    (* now we can apply these two lemmas to ge the right-hand side in
    the right shape. *)
    rewrite A1 in A2.
    subst PO1 PI0.
    subst lp0. unfold aloop in A2.
    rewrite A2.
    subst PO PO2 PL PI; simpl in *.
    clear A1 A2.
    
    unfold aloop, loop, CategoryOps.cat, Cat_Kleisli; simpl.
    eapply eqit_bind; try reflexivity.
    intros pe0.
    unfold CategoryOps.iter, Iter_Kleisli, Basics.iter, MonadIter_itree;
      simpl.
    eapply eutt_iter.
    intros pe.
    unfold LACntr at 1 2; unfold ACntr, ACntr2; simpl.
    unfold ACntr; simpl.
    clear pe0.
    (* annoying duplication. to be fixed somehow *)
    destruct pe as [[fn1 nB] | [fn1 nB]] eqn: was_e0; simpl.
    { destruct (loc_possible fn fn1 n1.+1 && (n0 <= nB)
                && (nB < n1.+1) && (0 < nB)) eqn: was_e1;
        try reflexivity.

      setoid_rewrite bind_bind.
      destruct ((nB == n0) || (nB == n1)) eqn: was_e2; try reflexivity.
      destruct (in_btw n0.+1 n1 nB) eqn: was_e3; try reflexivity.
      setoid_rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      rewrite H.
      eapply eqit_bind; try reflexivity.
      unfold aloop, loop, CategoryOps.cat, Cat_Kleisli; simpl.
      setoid_rewrite bind_ret_l; reflexivity.      
      intros pl3.
      setoid_rewrite bind_ret_l.
      unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
        CategoryOps.cat; simpl.
      setoid_rewrite bind_ret_l; reflexivity.
    }
    { destruct (loc_possible fn fn1 n1.+1 && (n0 <= nB)
                && (nB < n1.+1) && (0 < nB)) eqn: was_e1;
        try reflexivity.

      setoid_rewrite bind_bind.
      destruct ((nB == n0) || (nB == n1)) eqn: was_e2; try reflexivity.
      destruct (in_btw n0.+1 n1 nB) eqn: was_e3; try reflexivity.
      setoid_rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      rewrite H.
      eapply eqit_bind; try reflexivity.
      unfold aloop, loop, CategoryOps.cat, Cat_Kleisli; simpl.
      setoid_rewrite bind_ret_l; reflexivity.      
      intros pl3.
      setoid_rewrite bind_ret_l.
      unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
        CategoryOps.cat; simpl.
      setoid_rewrite bind_ret_l; reflexivity.
    }
      
Admitted.


(* equivalence between intemediate local and function-globablised
   semantics; the idea being that in Intermediate, local iterations
   can be pushed out up to functions; should be proved before
   interpreting LRec, otherwise one might end up with an infinite
   number of local iterations. probably the hardest bit *)
Lemma intemediate_local2intermediate_funglobal_fun {XS: stateE LState -< E}
  (fn: funname) :
  eutt eq (lsem_fun_imedL fn) (lsem_fun_imedF fn).
Proof.
  unfold lsem_fun_imedL, lsem_fun_imedF; simpl.
  unfold lsem_fun_imedAL, lsem_fun_imedAF; simpl.
  eapply eqit_bind; eauto; try reflexivity.
  unfold lsem_fun_imed_auxAL, lsem_fun_imed_auxAF.
  intros ltf; destruct ltf; simpl.
  destruct ((Datatypes.length lc1 == Datatypes.length lc1) &&
    (pl1.1 == Datatypes.length lc1 + code_length fn)) eqn: was_e; simpl;
      try reflexivity.
  eapply eqit_bind; try reflexivity.
  intros lp0.
  eapply eqit_bind; try reflexivity.
  set W := (intemediate_local2intermediate_funglobal_lcmd_aux lt lp0).
  unfold lsem_cmd_imedL, lsem_cmd_imedF in W; simpl in *.
  rewrite W; reflexivity.
Qed. 
    
(* equivalence between instrumented function-localised and
   intermediate function-globalised; basically, we need to match the
   global iteration with the mrec interpretation. *)
Lemma instrumented_funlocal2intermediate_funglobal_lcmd {XS: stateE LState -< E}
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) :
  eutt eq (@isem_lfloc E _ _ _ _ code_length (fn, fst plS))
    (lsem_imed_recF lt (fn, fst plS)).
Proof.
Admitted.

(* equivalence between instrumented global and intermediate local
   semantics then will follow. note: both semantics depend implicitly
   on glfenv *)
Lemma intermediate_local2instrumented_lcmd {XS: stateE LState -< E}
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) :
  eutt eq (lsem_imed_recL lt (fn, fst plS))
    (isem_lcmd_flow (fn, fst (fst (forget_imed_cmd lt)))).
Proof.
Admitted.

(* TODO: cleanup it_cflow_sem and redefine the lemma *)
(* equivalence between intermediate and source semantics *)
(* Lemma intermediate2source  *)

End Lemmas1.

End Lemmas.


(* MAYBE USEFUL *)
(* probably useless; similar to Intermediate Local; the only
  difference is that it inserts only the iterators that are strictly
  necessary. noethelss it reads slightly better, so for now I'm
  keeping it for reference. 
  parameterized intermediate local strict semantics.  
  LC -> isem_lcmd_seq_flow (isem_lcmd_acore could also do).  
  LSI -> isem_li_aflow *)
Fixpoint lsem_i_imedSL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : itree (LCall +' E) lpoint :=
  let '(pS, _) := plS in 
  let '(pE, _) := plE in 
  let LRec := @lsem_cmd_imedSL LSC LSI in
  match lt with
  | LErrLeaf _ => throw err
  | LLeaf _ (MkLI ii ir) => if LLeaf_ok (MkLI ii ir)
                            then LSI (fn, pS)
                            else throw err                                 
  | LIf1Node _ (p1, _) li1 lc li2 =>
      (* note: fst plE = S p1 *)
      match LIf1Node_ok li1 li2 with
      | false => throw err
      | true => let Bd := fun '(fnA, pA) =>
            if (pA == pS) || (pA == p1) then LSI (fn, pA)
            else if (pA == S pS) then LRec _ _ _ lc 
            else throw err in 
          LACntrI Bd fn pS pE (fn, pS) 
      end
  | LIfNode _ (p1, _) (p2, _) li1 lc2 li2 li3 lc1 li4 =>
      (* note: fst plE = S p2 *)
      match LIfNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true => let Bd := fun '(fnA, pA) =>
            if (pA == pS) || (pA == p1) ||
               (pA == S p1) || (pA == p2) then LSI (fn, pA)
            else if (pA == S pS) then LRec _ _ _ lc2
            else if (pA == S (S p1)) then LRec _ _ _ lc1 
            else throw err in
          LACntrI Bd fn pS pE (fn, pS)
      end     
  | LWhileTNode _ (p1, _) (p2, _) b ii li1 lc1 lc2 li2 =>
      (* note: fst plE = S p2 *)
      match LWhileTNode_ok li1 li2 with
      | false => throw err
      | true =>
         let bn := if b then 1 else 0 in  
         let Bd := fun '(fnA, pA) => 
            if (pA == pS) || (pA == pS + bn) || (pA == p2) then LSI (fn, pA)
            else if (pA == S (pS + bn)) then LRec _ _ _ lc1
            else if (pA == p1) then LRec _ _ _ lc2
            else throw err in                                       
          LACntrI Bd fn pS pE (fn, pS)
      end
  | LWhileFNode _ _ lc => LRec _ _ _ lc
  | LWhile1Node _ (p1, _) b ii li1 lc li2 =>
      (* note: fst plE = S p1 *)
      match LWhile1Node_ok li1 li2 with
      | false => throw err
      | true =>
         let bn := if b then 1 else 0 in  
         let Bd := fun '(fnA, pA) => 
            if (pA == pS) || (pA == pS + bn) || (pA == p1) then LSI (fn, pA)
            else if (pA == S (pS + bn)) then LRec _ _ _ lc
            else throw err in                                       
          LACntrI Bd fn pS pE (fn, pS)
      end
  | LWhileNode _ (p1, _) (p2, _) b ii li1 li2 lc2 li3 lc1 li4 =>
      (* note: fst plE = S p2 *)
      match LWhileNode_ok li1 li2 li3 li4 with
      | false => throw err
      | true =>
         let bn := if b then 1 else 0 in
         let pS1 := pS + bn in 
         let Bd := fun '(fnA, pA) => 
            if (pA == pS) || (pA == pS1) || (pA == S pS1)
               || (pA == p1) || (pA == p2) then LSI (fn, pA)
            else if (pA == S (S (pS1))) then LRec _ _ _ lc2
            else if (pA == S p1) then LRec _ _ _ lc1
            else throw err in                                       
          LACntrI Bd fn pS pE (fn, pS)
      end        
  | LCallNode _ nb na fn' lc_bef lc_aft li1 li2 =>
      match LCallNode_ok nb na fn' lc_bef lc_aft li1 li2 with
      | false => throw err  
      | true => LSC (lc_bef ++ [li1]) (fn, pS) ;;
                l1 <- (trigger_inl1 (Call fn')) ;;
                LSC (li2 :: lc_aft) l1 ;;
                Ret (fn, pS + nb + S (S na))            
      end 
  end
with lsem_cmd_imedSL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree (LCall +' E) lpoint :=
   match lt with
   | LListNil pl => Ret (fn, fst pl)
   | LListCons _ pl1 pl2 lt ltl =>
       @lsem_i_imedSL LSC LSI _ _ _ lt ;;
       @lsem_cmd_imedSL LSC LSI _ _ _ ltl
   end.                   

(* linear semantics of source functions. l1 is the return address (not
   used here, because LSC returns an lpoint) *)
Definition lsem_fun_imed_auxSL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) (fd: LTreeFun fn) : itree (LCall +' E) lpoint :=
  match fd with
  | LTFun lbl pl1 lc1 lc2 lt =>
      LSC lc1 (fn, 0) ;;
      l <- @lsem_cmd_imedSL LSC LSI _ _ _ lt ;; LSC lc2 l 
  end.                   

Definition lsem_fun_imedSL 
  (LSC: lcmd -> lpoint -> itree (LCall +' E) lpoint)
  (LSI: lpoint -> itree (LCall +' E) lpoint)
  (fn: funname) : itree (LCall +' E) lpoint :=
  fd <- err_def_option (ifenv fn) ;;
  lsem_fun_imed_auxSL LSC LSI fd.

  
(***** INTERMEDIATE LOCAL STRICT SEMANTICS *)
(* probably not needed *)

Section SLInterSemDef.
Context {XF: LFindE -< E} {XL: LEvalE -< E } {XSl: @stateE LState -< E}. 
  
Definition lsem_i_imedI  
  (fn: funname) (plS plE: plinfo)
  (lt : LTree fn plS plE) : itree (LCall +' E) lpoint :=
  @lsem_i_imedSL isem_lcmd_seq_flow isem_li_aflow _ _ _ lt.

Definition lsem_cmd_imedI  
  (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree (LCall +' E) lpoint :=
  lsem_cmd_imedSL isem_lcmd_seq_flow isem_li_aflow lt.

Definition lsem_fun_imedI  
  (fn: funname) : itree (LCall +' E) lpoint :=
  lsem_fun_imedSL isem_lcmd_seq_flow isem_li_aflow fn.

Definition handle_LRecI : LCall ~> itree (LCall +' E) :=
  fun T (rc : callE _ _ T) =>
   match rc with
   | Call fn => lsem_fun_imedI fn
   end.                            

(* LRec interpretation *)
Definition lsem_imed_recSL (fn: funname) (plS plE: plinfo)
  (lt : LTreeList fn plS plE) : itree E lpoint := 
  interp_mrec handle_LRecI (lsem_cmd_imedI lt).

End SLInterSemDef.

End IntermediateSem.

End LinSemContext.

End Asm1.



(******************************************************)
(******************************************************)
(* NOT USEFUL *)

(*
Lemma aloop_aux2_x {XS: stateE LState -< E}
  (la_cond1 la_lbl1: linstr) (fn fn0 : funname) (n0 n1 n2: nat) (l0 l1: label)
  (lcm1: LTreeList fn (incrP1 (n0, l0)) (n1, l1))
  (A1: (fn == fn0) = false) :
 let lp0 := (fn0, n2) in  
 (* PO2 *)
  aloop
     (LACntr
        (aloop
          (LACntr
             (λ '((_, pA) as lpA),
                if fn == lpA.1
                then
                 if LIf1Node_ok la_cond1 la_lbl1
                 then
                  if (pA == n0) || (pA == n1)
                  then isem_li_aflow lpA
                  else if in_btw n0.+1 n1 pA
                       then lsem_cmd_imedF lcm1 lpA else throw err
                 else throw err
                else throw err) fn n0.+1 n1)) fn n0 n1.+1) lp0 ≈

     throw err.
Proof.
  simpl.
  unfold aloop, loop, CategoryOps.cat, Cat_Kleisli; simpl.
  unfold inr_; simpl.
  rewrite bind_ret_l.
  unfold CategoryOps.iter, Iter_Kleisli, Basics.iter, MonadIter_itree; simpl.
  rewrite unfold_iter.
  rewrite bind_bind.
  unfold LACntr, ACntr; simpl.
  rewrite A1; simpl.
  rewrite bind_vis.
  eapply eqit_Vis.
  intro u. destruct u.
Qed.  
  



(* probably not good *)
Lemma aloop_aux2_inner {XS: stateE LState -< E}
  (la_cond1 la_lbl1: linstr) (fn fn0 : funname) (n0 n1 n2: nat) (l0 l1: label)
  (lcm1: LTreeList fn (incrP1 (n0, l0)) (n1, l1))
  (A1: n0 <= n2) (A2: n2 < n1) (A3: not_possible fn n1 == false) :
 let lp0 := (fn0, n2) in  
       (aloop
          (LACntr
             (λ '((_, pA) as lpA),
                if fn == lpA.1
                then
                 if LIf1Node_ok la_cond1 la_lbl1
                 then
                  if (pA == n0) || (pA == n1)
                  then isem_li_aflow lpA
                  else if in_btw n0.+1 n1 pA
                       then lsem_cmd_imedF lcm1 lpA else throw err
                 else throw err
                else throw err) fn n0.+1 n1)) lp0
  ≈ (λ '((_, pA) as lpA),
            if fn == lpA.1
            then
             if LIf1Node_ok la_cond1 la_lbl1
             then
              if (pA == n0) || (pA == n1)
              then isem_li_aflow lpA
              else
                if in_btw n0.+1 n1 pA
                then aloop (LACntr (lsem_cmd_imedF lcm1) fn n0.+1 n1) lpA
                else throw err
             else throw err
            else throw err) lp0.
Proof.
  unfold aloop; simpl.
  unfold LACntr, ACntr at 1; simpl.
(*  rewrite <- loop_natural_left. *)
Abort.

Require Import Equality.
From Paco Require Import paco.

(* wrong shape? *)
Lemma aloop_aux2a {XS: stateE LState -< E}
  (la_cond1 la_lbl1: linstr) (fn fn0 : funname) (n0 n1 n2: nat) (l0 l1: label)
  (lcm1: LTreeList fn (incrP1 (n0, l0)) (n1, l1))
  (A1: n0 <= n2) (A2: n2 < n1) (A3: not_possible fn n1 = false)
  (A4: fn = fn0) (A5: LIf1Node_ok la_cond1 la_lbl1)
  (A6: not_possible fn n1.+1 = false) :
  let lp0 := (fn0, n2) in
  eutt eq   
  (aloop (LACntr 
  (aloop (LACntr (λ '((_, pA) as lpA),
     if fn == lpA.1
     then if LIf1Node_ok la_cond1 la_lbl1
          then if (pA == n0) || (pA == n1)
               then isem_li_aflow lpA
               else if in_btw n0.+1 n1 pA
                    then lsem_cmd_imedF lcm1 lpA
                    else throw err
           else throw err
     else throw err) fn n0.+1 n1)) fn n0 n1.+1) lp0)
  (aloop (LACntr 
  ((λ lpB,                                  
     if fn == lpB.1
     then if LIf1Node_ok la_cond1 la_lbl1
          then (aloop (LACntr (λ '((_, pA) as lpA),
               if (pA == n0) || (pA == n1)
               then isem_li_aflow lpA
               else if in_btw n0.+1 n1 pA
                    then lsem_cmd_imedF lcm1 lpA
                    else throw err) fn n0.+1 n1)) lpB 
          else throw err
     else throw err)) fn n0 n1.+1) lp0).
Proof.
  simpl.

  ginit. gcofix CIH.
  unfold aloop, loop, CategoryOps.cat, Cat_Kleisli; simpl.
  unfold inr_; simpl.
  setoid_rewrite bind_ret_l.
  unfold CategoryOps.iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
  setoid_rewrite unfold_iter_ktree.
  setoid_rewrite bind_bind.
  unfold LACntr, ACntr; simpl.
  inversion A4; subst; simpl.
  destruct (fn0 == fn0); try congruence; simpl.
  destruct (not_possible fn0 n1.+1) eqn: was_e2;
    try congruence; try reflexivity.
  destruct ((n0 <= n2 < n1.+1) && (0 < n2)) eqn: was_e3; try reflexivity.
  rewrite A5. simpl.
  setoid_rewrite bind_bind.
  setoid_rewrite bind_bind.
  setoid_rewrite bind_ret_l.

(*
  setoid_rewrite eq_itree_bind.
  
  simpl in *.
  rewrite was_e2 in A6.
  intuition.
  2: {
  destruct pe as [[fn3 n3] | [fn3 n3]]; simpl.
  - destruct (fn == fn3) eqn: was_e1; try reflexivity.
    destruct (not_possible fn3 n1.+1) eqn: was_e2;
      try congruence; try reflexivity.
    destruct ((n0 <= n3 < n1.+1) && (0 < n3)) eqn: was_e3;
      try reflexivity; simpl.
    setoid_rewrite bind_bind; simpl.
    destruct (LIf1Node_ok la_cond1 la_lbl1);
      try congruence; try reflexivity.

    2: { intuition. }

    setoid_rewrite bind_bind.
    setoid_rewrite bind_ret_l; simpl.
    
    
    
  setoid_rewrite bind_iter.
  rewrite A4. 
  destruct (LIf1Node_ok la_cond1 la_lbl1).
  eapply eqit_bind; try reflexivity.
  intros pe.
  
  remember A4 as A4r.
  rewrite 
  dependent destruction A4r.
  destruct A4 eqn: was_A4.
  setoid_rewrite bind_ret_l.


  reflexivity.      
      intros pl3.
  

    ≈ CategoryOps.cat (aloop F) G lp0.
     (*  (x <- (aloop F lp0) ;; G x). *)
Proof.
  intros.
(*  Set Printing Implicit. *)
  unfold aloop.
  intros. simpl.  
  set W := (@loop_natural_right Type (ktree (LCall +' E)) _ _  
    (@Id_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E)))
    (@Cat_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E)))
     _ sum (@Case_Kleisli (itree (LCall +' E)))
    (@Inl_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E)))
    (@Inr_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E))) _ 
    (@Iter_Kleisli (itree (LCall +' E)) (@MonadIter_itree (LCall +' E))) _
    lpoint lpoint lpoint lpoint 
    F G).
  rewrite W.
  clear W.
  unfold loop, CategoryOps.cat, Cat_Kleisli; simpl.
  subst F G; simpl.
  setoid_rewrite bind_ret_l; try reflexivity.
  unfold lsem_cmd_imedF, lsem_cmd_imedAF.
  eapply eutt_iter; try reflexivity.
  intros pe.
  rewrite bind_bind.  
  eapply eqit_bind; try reflexivity.
  - unfold LACntr, ACntr; simpl.
    destruct pe as [[fn3 n3] | [fn3 n3]]; simpl.
    { destruct (fn == fn3) eqn: was_e0; simpl; try reflexivity. }
    { destruct (fn == fn3) eqn: was_e0; simpl; try reflexivity. }
  - intros pe1.
    destruct pe1 as [[fn3 n3] | [fn3 n3]]; simpl.
    + setoid_rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      setoid_rewrite bind_ret_l; simpl.
      unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
        CategoryOps.cat; simpl.
      setoid_rewrite bind_ret_l; simpl; reflexivity.    
    + setoid_rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      setoid_rewrite bind_ret_l; simpl.
      unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
        CategoryOps.cat; simpl.
      unfold not_possible in A3.
      destruct (fn == fn3); simpl.
      * setoid_rewrite bind_ret_l; simpl; reflexivity.    
      * (* PROBLEM *)
        admit.
*)
Abort.

Lemma aloop_aux2a {XS: stateE LState -< E}
  (la_cond1 la_lbl1: linstr) (fn fn0 : funname) (n0 n1 n2: nat) (l0 l1: label)
  (lcm1: LTreeList fn (incrP1 (n0, l0)) (n1, l1))
  (A1: n0 <= n2) (A2: n2 < n1) (A3: not_possible fn n1 == false) :
  let lp0 := (fn0, n2) in
  let F := (LACntr (λ '((_, pA) as lpA),
     if LIf1Node_ok la_cond1 la_lbl1
     then if (pA == n0) || (pA == n1)
          then isem_li_aflow lpA
          else if in_btw n0.+1 n1 pA
               then lsem_cmd_imedF lcm1 lpA
                (* aloop (LACntr (lsem_cmd_imedF lcm1) fn n0.+1 n1) lpA *)
               else throw err
          else throw err) fn n0.+1 n1) in
  let G := (fun lp1: lpoint => if fn == lp1.1 then Ret lp1 else throw err) in 
  (aloop (LACntr (λ '((_, pA) as lpA),
     if fn == lpA.1
     then if LIf1Node_ok la_cond1 la_lbl1
          then if (pA == n0) || (pA == n1)
               then isem_li_aflow lpA
               else if in_btw n0.+1 n1 pA
                    then lsem_cmd_imedF lcm1 lpA
                    else throw err
           else throw err
     else throw err) fn n0.+1 n1)) lp0
   ≈ CategoryOps.cat (aloop F) G lp0.
     (*  (x <- (aloop F lp0) ;; G x). *)
Proof.
  intros.
(*  Set Printing Implicit. *)
  unfold aloop.
  intros. simpl.  
  set W := (@loop_natural_right Type (ktree (LCall +' E)) _ _  
    (@Id_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E)))
    (@Cat_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E)))
     _ sum (@Case_Kleisli (itree (LCall +' E)))
    (@Inl_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E)))
    (@Inr_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E))) _ 
    (@Iter_Kleisli (itree (LCall +' E)) (@MonadIter_itree (LCall +' E))) _
    lpoint lpoint lpoint lpoint 
    F G).
  rewrite W.
  clear W.
  unfold loop, CategoryOps.cat, Cat_Kleisli; simpl.
  subst F G; simpl.
  setoid_rewrite bind_ret_l; try reflexivity.
  unfold lsem_cmd_imedF, lsem_cmd_imedAF.
  eapply eutt_iter; try reflexivity.
  intros pe.
  destruct pe as [[fn3 n3] | [fn3 n3]]; simpl.
  { rewrite bind_bind.  
    unfold LACntr, ACntr; simpl.
    destruct (fn == fn3) eqn: was_e0; simpl.
    2: {admit. }
    { eapply eqit_bind; try reflexivity.
      intros pe1.
      destruct pe1 as [[fn4 n4] | [fn4 n4]]; simpl.
      + setoid_rewrite bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite bind_ret_l; simpl.
        unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
          CategoryOps.cat; simpl.
        setoid_rewrite bind_ret_l; simpl; reflexivity.    
      + setoid_rewrite bind_bind.
        setoid_rewrite bind_ret_l.
        setoid_rewrite bind_ret_l; simpl.
        unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
          CategoryOps.cat; simpl.
        unfold not_possible in A3.
      destruct (fn == fn3); simpl.
Abort.      
(*    
    { destruct (fn == fn3) eqn: was_e0; simpl; try reflexivity. }
    { destruct (fn == fn3) eqn: was_e0; simpl; try reflexivity. }
  - intros pe1.
    destruct pe1 as [[fn3 n3] | [fn3 n3]]; simpl.
    + setoid_rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      setoid_rewrite bind_ret_l; simpl.
      unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
        CategoryOps.cat; simpl.
      setoid_rewrite bind_ret_l; simpl; reflexivity.    
    + setoid_rewrite bind_bind.
      setoid_rewrite bind_ret_l.
      setoid_rewrite bind_ret_l; simpl.
      unfold bimap, Case_Kleisli, Bimap_Coproduct, case_,
        CategoryOps.cat; simpl.
      unfold not_possible in A3.
      destruct (fn == fn3); simpl.
      * setoid_rewrite bind_ret_l; simpl; reflexivity.    
      * (* PROBLEM *)
        admit.
Admitted. 
*)        

        
(* wrong shape? indeed *)
Lemma aloop_aux2b {XS: stateE LState -< E}
  (la_cond1 la_lbl1: linstr) (fn fn0 : funname) (n0 n1 n2: nat) (l0 l1: label)
  (lcm1: LTreeList fn (incrP1 (n0, l0)) (n1, l1))
  (A1: n0 <= n2) (A2: n2 < n1) (A3: not_possible fn n1 == false) :
  let lp0 := (fn0, n2) in
  let F := (LACntr
                 (λ '((_, pA) as lpA),
                  if LIf1Node_ok la_cond1 la_lbl1
                  then
                     if (pA == n0) || (pA == n1)
                     then isem_li_aflow lpA
                     else
                       if in_btw n0.+1 n1 pA
                       then aloop (LACntr (lsem_cmd_imedF lcm1) fn n0.+1 n1)
                              lpA
                       else throw err
                  else throw err) fn n0.+1 n1) in
  let G := (fun x: lpoint => if fn == fn0 then Ret x else throw err) in 
  (aloop (LACntr
           (λ '((_, pA) as lpA),
                if fn == lpA.1
                then
                 if LIf1Node_ok la_cond1 la_lbl1
                 then
                  if (pA == n0) || (pA == n1)
                  then isem_li_aflow lpA
                  else if in_btw n0.+1 n1 pA
                       then lsem_cmd_imedF lcm1 lpA
                       else throw err
                 else throw err
                else throw err) fn n0.+1 n1)) lp0
    ≈ CategoryOps.cat (aloop F) G lp0.
     (*  (x <- (aloop F lp0) ;; G x). *)
Proof.
  intros.
(*  Set Printing Implicit. *)
  unfold aloop.
  intros. simpl.  
  set W := (@loop_natural_right Type (ktree (LCall +' E)) _ _  
    (@Id_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E)))
    (@Cat_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E)))
     _ sum (@Case_Kleisli (itree (LCall +' E)))
    (@Inl_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E)))
    (@Inr_Kleisli (itree (LCall +' E)) (@Monad_itree (LCall +' E))) _ 
    (@Iter_Kleisli (itree (LCall +' E)) (@MonadIter_itree (LCall +' E))) _
    lpoint lpoint lpoint lpoint 
    F G).
  rewrite W.
  unfold loop, CategoryOps.cat, Cat_Kleisli; simpl.
  setoid_rewrite bind_ret_l; try reflexivity.
  unfold lsem_cmd_imedF, lsem_cmd_imedAF.
  eapply eutt_iter.
  intros pe.
  subst F G; simpl.
  rewrite bind_bind.
  eapply eqit_bind; try reflexivity.
  - unfold LACntr, ACntr; simpl.
    destruct pe as [[fn3 n3] | [fn3 n3]]; simpl.
Abort.

*)
(********************************************************************)
