(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect.
Require Import expr psem compiler_util ZArith.
Require Import asm_op_spec1 asm_op_spec2 propagate_inline.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Module Import E.

  Definition pass : string := "spec transform".

  Definition spec_transform_error := pp_internal_error_s pass.

End E.

Definition cond_env_rec (e : pexpr) :=
if use_mem e then None else Some e.

(* expression defining the boolean condition and Sv.t defining the 
   free variables present in e *)
Definition cond_env := option (pexpr * Sv.t).

Definition cond_env_empty : cond_env := None.

Definition var_env := Sv.t.

Definition env := (cond_env * var_env)%type.

Definition empty_env := (cond_env_empty, Sv.empty).

Definition get_fv (env : cond_env) : Sv.t :=
match env with 
| Some e => e.2
| None => Sv.empty
end.

Inductive wf_env (envi : env) : Prop :=
| wf_cond_env : forall e fv msf,
                envi = (Some (e, fv), msf)  ->
                fv = read_e e ->
                use_mem e = false ->
                wf_env envi
| wf_none_env : forall msf,
                envi = (None, msf) ->
                wf_env envi.
 
Definition update_cond_env (X: Sv.t) (E : cond_env) : cond_env :=
match E with 
| Some (e, fv) => if Sv.subset X fv then None else E
| None => None
end.

Section ASM_OP.

Context `{asmop : asmOp}.
Context {pd : PointerData}.

Definition asm_spec1_to_asm_spec2 (o : asm_op_spec1) : asm_op_spec2 :=
match o with 
| asm_op_spec1.Oprotect w => asm_op_spec2.Oprotect w
| asm_op_spec1.Oset_msf => asm_op_spec2.Oset_msf
| asm_op_spec1.Oinit_msf => asm_op_spec2.Oinit_msf
| asm_op_spec1.Omov_msf => asm_op_spec2.Omov_msf
| asm_op_spec1.Oasm o => asm_op_spec2.Oasm o
end.

Definition sopn_spec1_to_spec2 (o :  @sopn asm_op_spec1 asmOp_spec1) :
@sopn asm_op_spec2 asmOp_spec2 := 
match o with 
| Ocopy w p => Ocopy w p
| Onop => Onop
| Omulu w => Omulu w
| Oaddcarry w => Oaddcarry w
| Osubcarry w => Osubcarry w
| sopn.Oasm o => sopn.Oasm (asm_spec1_to_asm_spec2 o)
end.

End ASM_OP.

Section CMD.

Context `{asmop : asmOp}.
Context {pd : PointerData}.

Variable i_spec1_to_spec2 : env -> @instr asm_op_spec1 asmOp_spec1 -> 
                            cexec (env * seq (@instr asm_op_spec2 asmOp_spec2))%type.

Fixpoint c_spec1_to_spec2 (envi : env) (cmd : seq (@instr asm_op_spec1 asmOp_spec1)) 
: cexec (env * seq (@instr asm_op_spec2 asmOp_spec2)) :=
match cmd with 
| [::] => ok (envi, [::])%type
| i :: c => Let ir := i_spec1_to_spec2 envi i in 
            Let cr := c_spec1_to_spec2 ir.1 c in 
            ok (cr.1, ir.2 ++ cr.2)
end.

End CMD.

Section INST.

Context `{asmop : asmOp}.
Context {pd : PointerData}.

Fixpoint ir_spec1_to_spec2 envi ii (ir: @instr_r asm_op_spec1 asmOp_spec1) {struct ir}
: cexec (env * seq (@instr asm_op_spec2 asmOp_spec2)) := 
match ir with 
| Cassgn x tag ty e => ok (envi, [:: MkI ii (@Cassgn asm_op_spec2 asmOp_spec2 x tag ty e)])
| Copn xs tag o es => 
  let cr := [:: MkI ii (@Copn asm_op_spec2 asmOp_spec2 xs tag ((sopn_spec1_to_spec2 o)) es)] in
  match o with 
  | Ocopy _ _ | Onop | Omulu _ | Oaddcarry _ | Osubcarry _ => ok (envi, cr)
    (* xs := init_msf 
       X = xs U X 
       E = update E based on whether X is present in E or not *)
  | sopn.Oasm asm_op_spec1.Oinit_msf =>
    match es with 
    | [::] => let cenv := update_cond_env envi.2 envi.1 in 
              let venv := vrvs_rec envi.2 xs in  
              ok ((cenv, venv), cr)
    | _ => Error (spec_transform_error "Too many arguments")
    end 
    (* xs := set_msf (e, y) 
       here y represents the msf flag and e is the boolean 
       X = xs U X (E is Some e and y in X) 
       X = X (y not in X) *)
  | sopn.Oasm asm_op_spec1.Oset_msf =>
    match es with 
    | [:: e ; y] => let cenv := update_cond_env envi.2 envi.1 in
                    let rs := read_e_rec Sv.empty y in
                    let r2 := disjoint rs envi.2 in
                    if negb r2
                    then ok ((cenv, vrvs_rec envi.2 xs), cr)
                    else ok ((cenv, envi.2), cr)
    | _ =>  Error (spec_transform_error "Too many arguments")
   end 
   (* xs := protect (e, y)
      should fail if y is not in X *)
  | sopn.Oasm (asm_op_spec1.Oprotect w) => 
    match es with 
    | [:: e; y] => let cenv := update_cond_env envi.2 envi.1 in 
                   let rs := read_e_rec Sv.empty y in 
                   let r := disjoint rs envi.2 in 
                   if r 
                   then Error (spec_transform_error "Msf variable not present")
                   else ok ((cenv, envi.2), cr)
    | _ => Error (spec_transform_error "Too many arguments")
    end
   (* xs := mov_msf(y) 
      if y is present in msf set then xs U X else X *)
  | sopn.Oasm asm_op_spec1.Omov_msf => 
    match es with
    | [:: y] => let rs := read_e_rec Sv.empty y in 
                let r := disjoint rs envi.2 in
                if r 
                then ok ((update_cond_env envi.2 envi.1, envi.2), cr)
                else ok ((update_cond_env envi.2 envi.1, vrvs_rec envi.2 xs), cr)
    | _ => Error (spec_transform_error "Too many arguments")
    end
  | sopn.Oasm o => ok (envi, cr) 
  end
 (* FIX ME *)                   
| Csyscall xs o es => ok (envi, [:: MkI ii (@Csyscall asm_op_spec2 asmOp_spec2 xs o es)])
(* FIX ME *)
| Cif b c1 c2 => 
  Let rc1 := (c_spec1_to_spec2 i_spec1_to_spec2 (Some (b, get_fv envi.1), envi.2) c1) in 
  Let rc2 := (c_spec1_to_spec2 i_spec1_to_spec2 (Some ((enot b), get_fv envi.1), envi.2) c2) in 
  ok ((update_cond_env envi.2 envi.1, Sv.inter rc1.1.2 rc2.1.2), [:: MkI ii (@Cif asm_op_spec2 asmOp_spec2 b rc1.2 rc2.2)])
| Cfor x (dir, e1, e2) c => Let cr := c_spec1_to_spec2 i_spec1_to_spec2 envi c in 
                            ok (cr.1, [:: MkI ii (@Cfor asm_op_spec2 asmOp_spec2 x (dir, e1, e2) cr.2)])
| Cwhile a c e c' => (*let c := (c_spec1_to_spec2 i_spec1_to_spec2 c) in 
                     let c' := (c_spec1_to_spec2 i_spec1_to_spec2 c') in 
                     [:: MkI ii (@Cwhile asm_op_spec2 asmOp_spec2 a c e c')]*) ok (envi, [::])
| Ccall ini xs fn es => ok (envi, [:: MkI ii (@Ccall asm_op_spec2 asmOp_spec2 ini xs fn es)])
end 

with i_spec1_to_spec2 (envi: env) (i : @instr asm_op_spec1 asmOp_spec1)
: cexec (env * seq (@instr asm_op_spec2 asmOp_spec2)) := 
let (ii,ir) := i in
(ir_spec1_to_spec2 envi ii ir).

End INST.

Section Section.

Context `{asmop : asmOp}.
Context {pd : PointerData}.
Context {T} {pT:progT T}.

Definition fun_spec1_to_spec2 (f:@fundef asm_op_spec1 asmOp_spec1 _ _)
: cexec (env * @fundef asm_op_spec2 asmOp_spec2 _ _) :=
  let 'MkFun ii si p c so r ev := f in
  Let c := c_spec1_to_spec2 i_spec1_to_spec2 empty_env c in
  ok (c.1, MkFun ii si p c.2 so r ev).

Variable map_spec1_to_spec2 : 
(@fundef asm_op_spec1 asmOp_spec1 _ _ -> 
cexec (env * @fundef asm_op_spec2 asmOp_spec2 _ _)) -> 
@prog asm_op_spec1 asmOp_spec1 _ _ -> 
(@prog asm_op_spec2 asmOp_spec2 _ _).

Definition prog_spec1_to_spec2 (p:@prog asm_op_spec1 asmOp_spec1 _ _) : 
(@prog asm_op_spec2 asmOp_spec2 _ _) := 
map_spec1_to_spec2 fun_spec1_to_spec2 p.

End Section.

Section PROOF.

Context
  {syscall_state asm_op : Type}
  `{asmop : asmOp}
  {fcp : FlagCombinationParams}
  {pd : PointerData}
  {sc_sem : syscall_sem syscall_state}.

Existing Instance progUnit.

Variable (ev:extra_val_t).
(*Variable (p: @prog asm_op_spec1 asmOp_spec1 _ _).*)

Variable (p: @prog asm_op_spec1  (@asmOp_of_spp (@asm_op_spec1 asm_op0 asmop) _ _) _ _).

(*Context {T:eqType} {pT:progT T} `{sCP: semCallParams}.
Variable (ev:extra_val_t).
Variable (p: @prog asm_op_spec1 asmOp_spec1 _ _).
Variable (sppe: SemPexprParams asm_op syscall_state).*)

Variable map_spec1_to_spec2 : 
(@fundef asm_op_spec1 asmOp_spec1 _ _ -> 
cexec (env * @fundef asm_op_spec2 asmOp_spec2 _ _)) -> 
@prog asm_op_spec1 asmOp_spec1 _ _ -> 
@prog asm_op_spec2 asmOp_spec2 _ _.

Definition estate_spec1_spec2 (s1 : @estate (@asm_op_spec1 asm_op0 asmop) syscall_state
                  (@spp_of_asm_op_spec1 asm_op0 asmop pd syscall_state fcp sc_sem)) :
@estate (@asm_op_spec2 asm_op0 asmop) syscall_state
                  (@spp_of_asm_op_spec2 asm_op0 asmop pd syscall_state fcp sc_sem) :=
match s1 with 
| Estate ss m f => @Estate (@asm_op_spec2 asm_op0 asmop) syscall_state
                   (@spp_of_asm_op_spec2 asm_op0 asmop pd syscall_state fcp sc_sem) ss m f
end. 

Let p' := prog_spec1_to_spec2 map_spec1_to_spec2 p.

Let Pi_r s1 (i: @instr_r asm_op_spec1 asmOp_spec1) s2 :=
forall ii (envi : env), 
wf_env envi ->
match (ir_spec1_to_spec2 envi ii i) with
 | Ok (envi', c') => sem p' ev (estate_spec1_spec2 s1) c' (estate_spec1_spec2 s2) /\ wf_env envi'
 | _ => True
end.

Let Pi s1 i s2 :=
forall (envi : env),
wf_env envi ->
match (i_spec1_to_spec2 envi i) with
 | Ok (envi', c') => sem p' ev (estate_spec1_spec2 s1) c' (estate_spec1_spec2 s2) /\ wf_env envi'
 | _ => True
end.

Let Pc s1 c s2 :=
forall (envi : env),
wf_env envi ->
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => sem p' ev (estate_spec1_spec2 s1) c' (estate_spec1_spec2 s2) /\ wf_env envi'
 | _ => True
end.

Let Pfor i vs s1 c s2 :=
forall (envi : env),
wf_env envi ->
match (c_spec1_to_spec2 (i_spec1_to_spec2) envi c) with
 | Ok (envi', c') => sem_for p' ev i vs (estate_spec1_spec2 s1) c' (estate_spec1_spec2 s2) /\ wf_env envi'
 | _ => True
end.

(*Set Printing Implicit.
Set Printing All.
About sem_Ind_nil. About estate. Print estate. Print sem_Ind_nil.
Print Instances SemPexprParams. 
Print Pc.
Print Estate.*)

Lemma eq_globs : p_globs p = p_globs p'.
Proof.
rewrite /p' /=. case: p=> /=. 
move=> pf pg pe /=. rewrite /prog_spec1_to_spec2 /= /fun_spec1_to_spec2 /=. 
Admitted.

Lemma Hskip : sem_Ind_nil Pc.
Proof.
move=> s1 envi hwf /=. split=> //=.
rewrite /estate_spec1_spec2. case: s1=> //=. 
by constructor.
Qed.

Lemma Hcons : sem_Ind_cons p ev Pc Pi.
Admitted.

Lemma HmkI : sem_Ind_mkI p ev Pi_r Pi.
Admitted.

Lemma Hassgn : sem_Ind_assgn p Pi_r.
Proof.
move=> s1 s2 x tag ty e v v' he ht hw. rewrite /Pi_r /=.
move=> ii envi hwf /=.
have heg := eq_globs. split=> //=.
+ rewrite /estate_spec1_spec2 /=. case: s1 he ht hw=> //= ss m f he ht hw. 
  case: s2 hw=> //= ss' m' f' hw. econstructor. 
  + econstructor. econstructor.
    + rewrite -heg /=.  admit.
    + by apply ht.
    rewrite -heg /=. admit.
  by constructor.
Admitted.

Lemma Hopn : sem_Ind_opn p Pi_r.
Proof.
move=> s1 s2 t [].
(* Ocopy *)
+ move=> w pos xs es /= hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf /=. split=> //=.
  rewrite /estate_spec1_spec2 /=. case: s1 hop=> //= ss m vm hop.
  case: s2 hop=>//= ss' m' vm' hop'. econstructor.
  econstructor. + econstructor. rewrite -heg /=. admit.
  by constructor.
(* Onop *)
+ move=> xs es hop. rewrite /Pi_r /=. have heg := eq_globs.
  move=> ii envi hwf /=. split=> //=. econstructor. 
  + econstructor. econstructor. rewrite -heg. admit.
  by constructor.
(* Omul *)
+ admit.
(* Oaddcarry *)
+ admit.
(* Osubcarry *)
+ admit.
move=> [].
(* protect *)
+ admit.
(* set_msf *)
+ admit.
(* init_msf *)
+ move=> xs [] //= hop. rewrite /Pi_r /= /estate_spec1_spec2 /=. have heg := eq_globs.
  case: s1 hop=> //=. case: s2=> //=.
  move=> ss' m' vm' ss m vm /= hop ii envi hwf /=.
  split=> //=.
  + econstructor.
    + econstructor. econstructor. rewrite -heg. Set Printing Implicit.  admit.
    by constructor.
  case: hwf=> //=.
  (* some *)
  + move=> e fv msf -> -> hmem /=. case: ifP=> //=.
    + move=> hsub. by apply wf_none_env with (vrvs_rec msf xs).
    move=> hsub. by apply wf_cond_env with e (read_e e) (vrvs_rec msf xs).
  (* none *)
  move=> msf -> /=. by apply wf_none_env with (vrvs_rec msf xs).
(* mov_msf *)
+ move=> xs es hop. rewrite /Pi_r /ir_spec1_to_spec2 /estate_spec1_spec2 /=. have heg := eq_globs.
  case: s1 hop=> //=. case: s2=> //=. move=> ss' m' vm' ss m vm /= hop.
  case: es hop=> //= e es. case: es=> //= hop ii envi hwf.
  case: ifP=> //=.
  (* e not present in X ==> X = X*)
  + move=> hdisj. split=> //=.
    + econstructor.
      + econstructor. econstructor.
  
Admitted.

Lemma Hif_true : sem_Ind_if_true p ev Pc Pi_r.
Admitted.

Lemma Hif_false : sem_Ind_if_false p ev Pc Pi_r.
Admitted.

Lemma Hwhile_true : sem_Ind_while_true p ev Pc Pi_r.
Admitted.

Lemma Hwhile_false : sem_Ind_while_false p ev Pc Pi_r.
Admitted.

Lemma Hfor : sem_Ind_for p ev Pi_r Pfor.
Admitted.





