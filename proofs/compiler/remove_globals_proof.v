(* ** Imports and settings *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssralg.
From mathcomp Require Import word_ssrZ.
From Coq Require Import ZArith.
Require Import xseq.
Require Import compiler_util expr psem remove_globals low_memory.
Import Utf8.

Definition gd_incl (gd1 gd2: glob_decls) :=
  forall g v, get_global gd1 g = ok v -> get_global gd2 g = ok v.

Lemma gd_inclT gd3 gd1 gd2 :  gd_incl gd1 gd3 -> gd_incl gd3 gd2 -> gd_incl gd1 gd2.
Proof. by move=> h1 h2 g v /h1 /h2. Qed.

Module INCL. Section INCL.

  Context
    {wsw : WithSubWord}
    {dc:DirectCall}
    {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state}.

  Section INCL_E.
    Context (wdb : bool) (gd1 gd2 : glob_decls) (s : estate) (hincl : gd_incl gd1 gd2).
    Let P e : Prop :=
      ∀ v, sem_pexpr wdb gd1 s e = ok v → sem_pexpr wdb gd2 s e = ok v.
    Let Q es : Prop :=
      ∀ vs, sem_pexprs wdb gd1 s es = ok vs → sem_pexprs wdb gd2 s es = ok vs.

    Lemma gd_incl_gvar (x : gvar) (v : value) :
      get_gvar wdb gd1 (evm s) x = ok v → get_gvar wdb gd2 (evm s) x = ok v.
    Proof. by rewrite /get_gvar; case: x => x [] //=; apply: hincl. Qed.

    Lemma gd_incl_e_es : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; split; subst P Q => //=.
      - move => e rec es ih q; t_xrbindP => v ok_v vs ok_vs <- {q}.
        by rewrite (rec _ ok_v) /= (ih _ ok_vs).
      - by apply gd_incl_gvar.
      - move => al aa sz x e rec v; apply: on_arr_gvarP => n t h1 h2; t_xrbindP => z v1 /rec -> hz w.
        by rewrite /on_arr_var (gd_incl_gvar h2) /= hz /= => -> <-.
      - move=> aa sz len x e rec v; apply: on_arr_gvarP => n t h1 h2; t_xrbindP => z v1 /rec -> hz w.
        by rewrite /on_arr_var  (gd_incl_gvar h2) /= hz /= => -> <-.
      - by move => al sz e hrec v; t_xrbindP => ?? /hrec -> /= -> ? /= -> <-.
      - by move=> ? e hrec v; t_xrbindP => ? /hrec -> <-.
      - by move=> ? e1 hrec1 e2 hrec2 v; t_xrbindP => ? /hrec1 -> ? /= /hrec2 -> <-.
      - by move => op es rec v; rewrite -!/(sem_pexprs _ _ _); t_xrbindP => vs /rec ->.
      move=> t e1 hrec1 e2 hrec2 e3 hrec3 v.
      by t_xrbindP => ?? /hrec1 -> /= -> ?? /hrec2 -> /= -> ?? /hrec3 -> /= -> /= <-.
    Qed.

  End INCL_E.

  Definition gd_incl_e wdb gd1 gd2 s e v h :=
    (@gd_incl_e_es wdb gd1 gd2 s h).1 e v.

  Definition gd_incl_es wdb gd1 gd2 s es vs h :=
    (@gd_incl_e_es wdb gd1 gd2 s h).2 es vs.

  Lemma gd_incl_wl wdb gd1 gd2 x v (s1 s2:estate) :
    gd_incl gd1 gd2 ->
    write_lval wdb gd1 x v s1 = ok s2 ->
    write_lval wdb gd2 x v s1 = ok s2.
  Proof.
    move=> hincl;case: x => //=.
    + by move=> al ws vi e;t_xrbindP => ?? /(gd_incl_e hincl) -> /= -> ? -> /= ? -> <-.
    + move=> al aa sz x e; apply: on_arr_varP;rewrite /on_arr_var => ?? h1 ->.
     by rewrite /write_var; t_xrbindP => ?? /(gd_incl_e hincl) -> /= -> ? -> /= ? -> /= ? -> <-.
    move=> aa sz len x e; apply: on_arr_varP;rewrite /on_arr_var => ?? h1 ->.
    by rewrite /write_var; t_xrbindP => ?? /(gd_incl_e hincl) -> /= -> ? -> /= ? -> /= ? -> <-.
  Qed.

  Lemma gd_incl_wls wdb gd1 gd2 xs vs s1 s2 :
    gd_incl gd1 gd2 ->
    write_lvals wdb gd1 s1 xs vs = ok s2 ->
    write_lvals wdb gd2 s1 xs vs = ok s2.
  Proof.
    move=> hincl;elim: xs vs s1 s2 => //= x xs hrec [|v vs] s1 s2 //=.
    by t_xrbindP => ? /(gd_incl_wl hincl) -> /hrec /= ->.
  Qed.

  Context (P1:uprog) (ev:unit) (gd2:glob_decls).

  Notation gd := (P1.(p_globs)).

  Hypothesis hincl : gd_incl gd gd2.

  Let P2 := {| p_globs := gd2; p_funcs := P1.(p_funcs); p_extra := P1.(p_extra) |}.

  Section SEM.

  Let Pc s1 c s2 := sem P2 ev s1 c s2.

  Let Pi_r s1 i s2 := sem_i P2 ev s1 i s2.

  Let Pi s1 i s2 := sem_I P2 ev s1 i s2.

  Let Pfor x vs s1 c s2 := sem_for P2 ev x vs s1 c s2.

  Let Pfun scs1 m1 fn vs1 scs2 m2 vs2 := sem_call P2 ev scs1 m1 fn vs1 scs2 m2 vs2.

  Local Lemma Hnil : sem_Ind_nil Pc.
  Proof. move=> s; constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons P1 ev Pc Pi.
  Proof. by move=> s1 s2 s3 i c ? h1 ?; apply: Eseq. Qed.

  Local Lemma HmkI : sem_Ind_mkI P1 ev Pi_r Pi.
  Proof. move=> ?????;apply: EmkI. Qed.

  Local Lemma Hasgn : forall s1 s2 (x : lval) (tag : assgn_tag) ty (e : pexpr) v v',
    sem_pexpr true gd s1 e = ok v ->
    truncate_val (eval_atype ty) v = ok v' ->
    write_lval true gd x v' s1 = ok s2 ->
    Pi_r s1 (Cassgn x tag ty e) s2.
  Proof.
    move=> ???????? /(gd_incl_e hincl) h1 h2 /(gd_incl_wl hincl) h3.
    apply: Eassgn;eauto.
  Qed.

  Local Lemma Hopn : forall s1 s2 t (o : sopn) (xs : lvals) (es : pexprs),
    sem_sopn gd o s1 xs es = Ok error s2 ->
    Pi_r s1 (Copn xs t o es) s2.
  Proof.
    move=> ??????;rewrite /sem_sopn.
    t_xrbindP => ?? /(gd_incl_es hincl) h1 h2 /(gd_incl_wls hincl) h3.
    by econstructor;eauto;rewrite /sem_sopn h1 /= h2.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall P1 Pi_r.
  Proof.
    move=> s1 scs m s2 o xs es ves vs /(gd_incl_es hincl)hes ho /(gd_incl_wls hincl) hw.
    econstructor; eauto.
  Qed.

  Local Lemma Hif_true : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr true gd s1 e = ok (Vbool true) ->
    sem P1 ev s1 c1 s2 -> Pc s1 c1 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof. by move=> ????? /(gd_incl_e hincl) h1 ? h2; apply Eif_true. Qed.

  Local Lemma Hif_false : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd),
    sem_pexpr true gd s1 e = ok (Vbool false) ->
    sem P1 ev s1 c2 s2 -> Pc s1 c2 s2 -> Pi_r s1 (Cif e c1 c2) s2.
  Proof. by move=> ????? /(gd_incl_e hincl) h1 ? h2; apply Eif_false. Qed.

  Local Lemma Hwhile_true : forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (ei : instr_info) (c' : cmd),
    sem P1 ev s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool true) ->
    sem P1 ev s2 c' s3 -> Pc s2 c' s3 ->
    sem_i P1 ev s3 (Cwhile a c e ei c') s4 -> Pi_r s3 (Cwhile a c e ei c') s4 -> Pi_r s1 (Cwhile a c e ei c') s4.
  Proof.
    move=> ?????????? h1 /(gd_incl_e hincl) h2 ? h3 ? h4; apply: Ewhile_true; eauto.
  Qed.

  Local Lemma Hwhile_false : forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (ei : instr_info) (c' : cmd),
    sem P1 ev s1 c s2 -> Pc s1 c s2 ->
    sem_pexpr true gd s2 e = ok (Vbool false) ->
    Pi_r s1 (Cwhile a c e ei c') s2.
  Proof. move=> ???????? h1 /(gd_incl_e hincl) ?; apply: Ewhile_false; eauto. Qed.

  Local Lemma Hfor : sem_Ind_for P1 ev Pi_r Pfor.
  Proof.
    move=> ????????? /(gd_incl_e hincl) h1 /(gd_incl_e hincl) h2 h3.
    apply: Efor;eauto.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> ???;constructor. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P1 ev Pc Pfor.
  Proof. move=> ???????? h1 ? h2 h3 h4;econstructor;eauto. Qed.

  Local Lemma Hcall : sem_Ind_call P1 ev Pi_r Pfun.
  Proof.
    move=> ????????? /(gd_incl_es hincl) h1 ? h2 /(gd_incl_wls hincl) h3.
    econstructor;eauto.
  Qed.

  Local Lemma Hproc : sem_Ind_proc P1 ev Pc Pfun.
  Proof. move=> ?????????? h1 h2 h3 ? h4 h5 h6; econstructor;eauto. Qed.

  Lemma gd_incl_fun scs m (fn : funname) (l : seq value) scs0 m0 vs:
      sem_call P1 ev scs m fn l scs0 m0 vs -> Pfun scs m fn l scs0 m0 vs.
  Proof.
    exact:
      (sem_call_Ind
         Hnil
         Hcons
         HmkI
         Hasgn
         Hopn
         Hsyscall
         Hif_true
         Hif_false
         Hwhile_true
         Hwhile_false
         Hfor
         Hfor_nil
         Hfor_cons
         Hcall
         Hproc).
  Qed.

  End SEM.

  Section IT.

  Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

  Notation st_equal := (st_rel (fun _ : unit => eq)).

  Lemma st_equalP d s1 s2 : st_equal d s1 s2 <-> s1 = s2.
  Proof.
    rewrite st_relP; split.
    + by move=> [-> <-]; rewrite with_vm_same.
    by move=> ->; rewrite with_vm_same.
  Qed.

  Definition check_es_equal (_:unit) (es1 es2 : pexprs) (_:unit) := es1 = es2.

  Definition check_lvals_equal (_:unit) (xs1 xs2 : lvals) (_:unit) := xs1 = xs2.

  Lemma check_esP_R_equal d es1 es2 d' :
    check_es_equal d es1 es2 d' →
    ∀ s1 s2, st_equal d s1 s2 → st_equal d' s1 s2.
  Proof. done. Qed.

  Definition checker_equal : Checker_e st_equal :=
    {| check_es := check_es_equal
     ; check_lvals := check_lvals_equal
     ; check_esP_rel := check_esP_R_equal
    |}.

  Lemma checker_ginclP : Checker_eq P1 P2 checker_equal.
  Proof.
    constructor.
    + move=> > /wdb_ok_eq <- <- ??? /st_equalP -> /gd_incl_es -/(_ _ hincl) ->; eexists; eauto.
    by move=> > /wdb_ok_eq <- <- ???? /st_equalP -> /gd_incl_wls -/(_ _ hincl) ->; eexists; eauto.
  Qed.
  #[local] Hint Resolve checker_ginclP : core.

  Let Pi i :=
    wequiv_rec P1 P2 ev ev eq_spec (st_equal tt) [::i] [::i] (st_equal tt).

  Let Pi_r i := forall ii, Pi (MkI ii i).

  Let Pc c :=
    wequiv_rec P1 P2 ev ev eq_spec (st_equal tt) c c (st_equal tt).

  Lemma it_gd_incl_fun fn : wiequiv_f P1 P2 ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:=eq_spec)).
  Proof.
    apply wequiv_fun_ind => {}fn _ fs ft [<- <-] fd ->.
    exists fd => // s1 hinit; exists s1 => //.
    exists (st_equal tt), (st_equal tt); split => //; last by move=> s t vs /st_equalP <- ->; eexists; eauto.
    move: (f_body fd) => {fn fs ft fd s1 hinit}.
    apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //.
    + by apply wequiv_nil.
    + by move=> i c hi hc; apply wequiv_cons with (st_equal tt).
    + by move=> >; apply wequiv_assgn_rel_eq with checker_equal tt.
    + by move=> >; apply wequiv_opn_rel_eq with checker_equal tt.
    + by move=> >; apply wequiv_syscall_rel_eq with checker_equal tt.
    + by move=> > hc1 hc2 ii; apply wequiv_if_rel_eq with checker_equal tt tt tt.
    + by move=> > hc ii; apply wequiv_for_rel_eq with checker_equal tt tt.
    + by move=> > hc hc' ii; apply wequiv_while_rel_eq with checker_equal tt.
    move=> ????; apply wequiv_call_rel_eq with checker_equal tt => //.
    by move=> ???; apply: wequiv_fun_rec.
  Qed.

  End IT.

End INCL. End INCL. Import INCL.

Module EXTEND. Section ASM_OP.

Context `{asmop:asmOp}.
Context {spp: SemPexprParams}.

Section PROOFS.

  Context (fresh_id : glob_decls -> var -> Ident.ident).

  Let Pi (i:instr) :=
    forall gd1 gd2,
      extend_glob_i fresh_id i gd1 = ok gd2 ->
      gd_incl gd1 gd2.

  Let Pr (i:instr_r) := forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall gd1 gd2,
      foldM (extend_glob_i fresh_id) gd1 c = ok gd2 ->
      gd_incl gd1 gd2.

  Local Lemma Hmk  : forall i ii, Pr i -> Pi (MkI ii i).
  Proof. move=> ?? h;apply h. Qed.

  Local Lemma Hnil : Pc [::].
  Proof. by move=> ?? [<-]. Qed.

  Local Lemma Hcons: forall i c, Pi i -> Pc c -> Pc (i::c).
  Proof.
    by move=> i c hi hc gd1 gd2 /=;t_xrbindP => gd3 /hi h1 /hc; apply: gd_inclT.
  Qed.

  (* TODO: Move *)
  Lemma hasPP T (a : pred T) (s : seq T): reflect (exists2 x : T, List.In x s & a x) (has a s).
  Proof.
    elim: s => /=;first by constructor => -[].
    move=> x l ih; apply (equivP orP);split.
    + by move=> [ h| /ih []];eauto.
    move=> [x' [<- ?| ??]];first by auto.
    by right; apply /ih;eauto.
  Qed.

  Lemma assoc_memP (T : eqType) U (s : seq (T * U)) (x : T) (w : U): assoc s x = Some w → List.In (x, w) s.
  Proof.
    by elim: s => //= -[x' u] l ih; case: eqP => [-> [<-] | ? /ih];auto.
  Qed.

  Lemma add_glob_gd_incl ii x gd1 gv gd2 :
      add_glob fresh_id ii x gd1 gv = ok gd2 →
      gd_incl gd1 gd2.
  Proof.
    rewrite /add_glob.
    case:ifPn => hhas1; first by move=> [<-].
    case:ifPn => // /hasPP hhas2 [<-] g v.
    rewrite /get_global /get_global_value /=.
    case:eqP => heq //;subst g.
    case ha : assoc => [|// ].
    by have hin := assoc_memP ha; elim hhas2;eauto.
  Qed.

  Local Lemma Hasgn: forall x tg ty e, Pr (Cassgn x tg ty e).
  Proof.
    move=> [ii ty|x|al ws x e|al aa ws x e|aa ws len x e] ?? e1 ??? //=. 1,3-5: by move=> [<-].
    case: ifP => ?; last by move=> [<-].
    case: e1 => // [ [] // w [] // z | [] // len es ]; last t_xrbindP => array _.
    all: exact: add_glob_gd_incl.
  Qed.

  Local Lemma Hopn : forall xs t o es, Pr (Copn xs t o es).
  Proof. by move=> xs t o es ii gd1 gd2 /= [<-]. Qed.

  Local Lemma Hsyscall : forall xs o es, Pr (Csyscall xs o es).
  Proof. by move=> xs o es ii gd1 gd2 /= [<-]. Qed.

  Local Lemma Hif  : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 hc1 hc2 ii gd1 gd2 /=.
    by t_xrbindP => gd3 /hc1 h1 /hc2; apply: gd_inclT.
  Qed.

  Local Lemma Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof. by move=> ????? hc ii gd1 gd2 /= /hc. Qed.

  Local Lemma Hwhile : forall a c e ei c', Pc c -> Pc c' -> Pr (Cwhile a c e ei c').
  Proof.
    move=> a c e ei c' hc hc' ii gd1 gd2 /=.
    by t_xrbindP => gd3 /hc h1 /hc'; apply gd_inclT.
  Qed.

  Local Lemma Hcall: forall xs f es, Pr (Ccall xs f es).
  Proof. by move=> xs f es ii gd1 gd2 /= [<-]. Qed.

  Local Lemma extend_glob_cP c gd1 gd2 :
    foldM (extend_glob_i fresh_id) gd1 c = ok gd2 ->
    gd_incl gd1 gd2.
  Proof.
    exact: (cmd_rect Hmk Hnil Hcons Hasgn Hopn Hsyscall Hif Hfor Hwhile Hcall).
  Qed.

End PROOFS.

Lemma extend_glob_progP fresh_id P gd' :
  extend_glob_prog fresh_id P = ok gd' ->
  gd_incl (p_globs P) gd'.
Proof.
  rewrite /extend_glob_prog.
  elim: (p_funcs P) (p_globs P) => /= [gd [<-] // | fd fds hrec gd].
  by t_xrbindP => gd1 /extend_glob_cP h1 /hrec; apply: gd_inclT.
Qed.

End ASM_OP.

End EXTEND. Import EXTEND.

Module RGP. Section PROOFS.

  Context
    {wsw : WithSubWord}
    {dc:DirectCall}
    {asm_op syscall_state : Type}
    {ep : EstateParams syscall_state}
    {spp : SemPexprParams}
    {sip : SemInstrParams asm_op syscall_state}
    (fresh_id : glob_decls -> var -> Ident.ident).

  Notation venv := (Mvar.t var).

  Section FDS.

  Context (P:uprog) (ev:unit).

  Context (fds: ufun_decls).
  Notation gd := (p_globs P).

  Hypothesis fds_ok : map_cfprog (remove_glob_fundef gd) (p_funcs P) = ok fds.
  Hypothesis uniq_gd : uniq (map fst gd).
  Notation P' := {|p_globs := gd; p_funcs := fds; p_extra := p_extra P |}.

  Definition valid (m:venv) (s1 s2:estate) :=
    [/\ s1.(escs) = s2.(escs), s1.(emem) = s2.(emem),
        (forall x, ~~is_glob_var x -> value_uincl (evm s1).[x] (evm s2).[x]),
        (forall x g, Mvar.get m x = Some g -> is_glob_var x) &
        (forall x g,
           Mvar.get m x = Some g ->
           exists2 gv,
           get_global gd g = ok gv & value_uincl (evm s1).[x] gv) ].

  Lemma vm_uincl_valid m s vm s' :
    valid m (with_vm s vm) s' →
    evm s <=1 vm →
    valid m s s'.
  Proof.
    case => ?? hlocal ? hglobal le_vm; split => //.
    + move => ? /hlocal; exact: (value_uincl_trans (le_vm _)).
    by move => ?? /hglobal[] gv -> ?; exists gv; last apply: (value_uincl_trans (le_vm _)).
  Qed.

  Lemma valid_vm_uincl m s s' vm :
    valid m s s' →
    evm s' <=1 vm →
    valid m s (with_vm s' vm).
  Proof.
    case => ?? hlocal ?? le_vm; split => // ? /hlocal ?.
    exact: value_uincl_trans (le_vm _).
  Qed.

  Section REMOVE_GLOB_E.
    Context (wdb : bool) (m: venv) (ii: instr_info) (s1 s2: estate) (hvalid: valid m s1 s2).

    Let Pe e : Prop :=
      ∀ e' v,
        remove_glob_e ii m e = ok e' →
        sem_pexpr wdb gd s1 e = ok v →
        exists2 v', sem_pexpr wdb gd s2 e' = ok v' & value_uincl v v'.

    Let Pes es : Prop :=
      ∀ es' vs,
        mapM (remove_glob_e ii m) es = ok es' →
        sem_pexprs wdb gd s1 es = ok vs →
        exists2 vs', sem_pexprs wdb gd s2 es' = ok vs' & List.Forall2 value_uincl vs vs'.

    Lemma remove_glob_e_esP : (∀ e, Pe e) ∧ (∀ es, Pes es).
    Proof.
      case: hvalid => hscs hmem hm1 hm2 hm3.
      apply: pexprs_ind_pair; subst Pe Pes; split => //=.
      - by move => _ _ [<-] [<-]; exists [::].
      - move => e he es hes q qs.
        t_xrbindP => e' /he{}he es' /hes{}hes <- {q} v /he[] v' ok_e' ok_v' vs /hes[] vs' ok_es' ok_vs' <- {qs}.
        exists (v' :: vs').
        + by rewrite /= ok_e' ok_es'.
        by constructor.
      - by move => z _ _ [<-] [<-]; eexists; first reflexivity.
      - by move => b _ _ [<-] [<-]; eexists; first reflexivity.
      - by move => ws n _ _ [<-] [<-]; eexists; first reflexivity.
      - move => [x []] e' v /=; rewrite /get_gvar /get_var_ /=.
        + case : ifP => hx.
          + case heq: (Mvar.get _ _) => [ g | // ] [<-] /=.
            by rewrite /get_gvar /get_var /=; t_xrbindP => hdef <-; apply hm3.
          move/ok_inj => <-.
          move: hm1 => /(_ x); rewrite hx => /(_ erefl) {}hx.
          rewrite /= /get_gvar /get_var /=; t_xrbindP => hdef <- {v}.
          eexists; last exact: hx.
          case: wdb hdef (@value_uincl_defined (~~wdb) _ _ hx); last by [].
          by move => hdef /(_ hdef) ->.
        by move/ok_inj => <-; rewrite /= /get_gvar /= => ->; eexists; first reflexivity.
      - move => al aa ws [x []] e he q v; rewrite /get_var_ /=; t_xrbindP => e' ok_e'; last first.
        + move=> <- /=; apply: on_arr_gvarP; rewrite /on_arr_var /get_gvar /= => n t heq ->.
          t_xrbindP => z ? /(he _ _ ok_e')[] v' -> ok_v' /to_intI ?; subst.
          case: v' ok_v' => // _ /= <- w -> <-.
          by eexists; first reflexivity.
        move=> gx; case: ifPn => // hx; last first.
        + move=> [<-] <-;apply: on_arr_gvarP; rewrite /= /on_arr_var /get_gvar /= => n t heq.
          rewrite /get_var; t_xrbindP => ok_x ok_t i ? /(he _ _ ok_e')[] v' -> ok_v' /to_intI ?; subst.
          case: v' ok_v' => // _ /= <- w ok_w <-.
          move: hm1 => /(_ x); rewrite hx ok_t => /(_ erefl) /value_uinclE[] t' -> ok_t'.
          rewrite orbT /= (WArray.uincl_get ok_t' ok_w).
          eexists; first reflexivity.
          exact: word_uincl_refl.
        case heq: (Mvar.get _ _) => [ g | // ] [<-] <-.
        apply: on_arr_gvarP; rewrite /= /on_arr_var /get_gvar /get_var /= => n t ?.
        t_xrbindP => hdef ok_x z ? /(he _ _ ok_e')[] v' -> ok_v' /to_intI ?; subst.
        case: v' ok_v' => // _ /= <- w ok_w <-.
        case: (hm3 _ _ heq) => ? -> /value_uinclE.
        rewrite ok_x => - [] t' -> ok_t' /=.
        rewrite (WArray.uincl_get ok_t' ok_w).
        eexists; first reflexivity.
        exact: word_uincl_refl.
      - move => aa ws len [x []] e he q v; rewrite /get_var_ /=; t_xrbindP => e' ok_e'; last first.
        + move=> <- /=; apply: on_arr_gvarP; rewrite /on_arr_var /get_gvar /= => n t heq ->.
          t_xrbindP => ? ? /(he _ _ ok_e')[] z -> ok_z /to_intI ?; subst.
          case: z ok_z => // _ /= <- t' -> <- /=.
          by eexists; first reflexivity.
        move=> gx; case: ifPn => // hx; last first.
        + move=> [<-] <-;apply: on_arr_gvarP; rewrite /= /on_arr_var /get_gvar /get_var /= => n t heq.
          t_xrbindP => hdef ht i ? /(he _ _ ok_e')[] v' -> ok_v' /to_intI ?; subst.
          case: v' ok_v' => // _ /= <- arr ok_arr <-.
          move: (hm1 _ hx); rewrite ht => /value_uinclE[] t' -> ok_t'.
          rewrite orbT /=.
          case: (WArray.uincl_get_sub ok_t' ok_arr) => arr' -> ok_arr'.
          by eexists; first reflexivity.
        case heq: (Mvar.get _ _) => [ g | // ] [<-] <-.
        apply: on_arr_gvarP; rewrite /= /on_arr_var /get_gvar /get_var /= => n t ?.
        t_xrbindP => _ ht i ? /(he _ _ ok_e')[] v' -> ok_v' /to_intI ?; subst.
        case: v' ok_v' => // _ /= <- arr ok_arr <-.
        case: (hm3 _ _ heq) => ? -> /value_uinclE.
        rewrite ht => - [] t' -> ok_t' /=.
        case: (WArray.uincl_get_sub ok_t' ok_arr) => arr' -> ok_arr'.
        by eexists; first reflexivity.
      - move => ??? ih ??.
        t_xrbindP => ? /ih h <- adr ? /h[] ? /= -> /= A /to_wordI[] ? [] ? [] ? ok_adr; subst.
        move/value_uinclE: A => [] ? [] ? [] ? ok_adr'; subst => /=.
        rewrite (word_uincl_truncate ok_adr' ok_adr) /= hmem => ? -> <-.
        by eexists; first reflexivity.
      - move => ?? hrec ??; t_xrbindP => ? /hrec h <- /= ? /h[] ? -> {} h ok_v /=.
        rewrite (vuincl_sem_sop1 h ok_v).
        by eexists; first reflexivity.
      - move=> ?? hrec1 ? hrec2 ??; t_xrbindP=> ? /hrec1 h1 ? /hrec2 h2 <- ? /= /h1 [] ? -> {} h1 ? /h2[] ? -> {} h2 ok_v.
        rewrite /= (vuincl_sem_sop2 h1 h2 ok_v).
        by eexists; first reflexivity.
      - move => ?? ih ??; t_xrbindP => ? /ih{}ih <- ? /ih /=[] ?.
        rewrite -/(sem_pexprs _ _ _) => -> h ok_v.
        rewrite /= (vuincl_sem_opN h ok_v).
        by eexists; first reflexivity.
      move=> ? ? hrec1 ? hrec2 ? hrec3 ??.
      t_xrbindP => ? /hrec1 h1 ? /hrec2 h2 ? /hrec3 h3 <- b ? /= /h1[] ? -> /= /value_uinclE {} h1 /to_boolI ?; subst; subst.
      move => ?? /h2[] ? -> {} h2 ok_v2 ?? /h3[] ? -> {} h3 ok_v3 /=.
      case: (value_uincl_truncate h2 ok_v2) => ? -> {} h2.
      case: (value_uincl_truncate h3 ok_v3) => ? -> {} h3 /= <-.
      eexists (if b then _ else _); first reflexivity.
      by case: b.
    Qed.

  End REMOVE_GLOB_E.

  Definition remove_glob_eP wdb m ii s1 s2 e e' v h :=
    (@remove_glob_e_esP wdb m ii s1 s2 h).1 e e' v.

  Definition remove_glob_esP wdb m ii s1 s2 es es' vs h :=
    (@remove_glob_e_esP wdb m ii s1 s2 h).2 es es' vs.

  Lemma write_var_remove_uincl wdb (x:var_i) m s1 s2 v v' s1' :
    ~~ is_glob_var x ->
    valid m s1 s2 ->
    write_var wdb x v s1 = ok s1' ->
    value_uincl v v' ->
    exists s2', valid m s1' s2' /\ write_var wdb x v' s2 = ok s2'.
  Proof.
    move=> hglob hval /write_varP [-> hdb htr] hv'.
    case: (compat_truncate_uincl (compat_ctype_refl _ _) htr hv' hdb) => htr' hvv' hdb'.
    rewrite (write_var_truncate hdb' htr'); eexists; split; eauto.
    case: hval => hsc hmem h1 h2 h3; split => //= z hz.
    + by rewrite !Vm.setP; case: eqP; last by auto.
    move=> hv1; rewrite Vm.setP_neq; first by apply h3.
    by apply/eqP => ?; subst z; rewrite (h2 _ _ hv1) in hglob.
  Qed.

  Lemma write_var_remove wdb (x:var_i) m s1 s2 v s1' :
    ~~ is_glob_var x ->
    valid m s1 s2 ->
    write_var wdb x v s1 = ok s1' ->
    exists s2', valid m s1' s2' /\ write_var wdb x v s2 = ok s2'.
  Proof. by move => hglob hval hw; apply: (write_var_remove_uincl hglob hval hw). Qed.

  Lemma remove_glob_lvP wdb m ii s1 s1' s2 lv lv' v :
    valid m s1 s2 ->
    remove_glob_lv ii m lv = ok lv' ->
    write_lval wdb gd lv v s1 = ok s1' ->
    exists s2',
      valid m s1' s2' /\ write_lval wdb gd lv' v s2 = ok s2'.
  Proof.
    move=> hval; case:(hval) => hscs hmem hm1 hm2 hm3; case:lv => [vi ty|x|al ws vi e|al aa ws x e|aa ws len x e] /=.
    + by move=> [<-] /write_noneP; rewrite /= /write_none => -[-> -> ->]; eauto.
    + by case: ifPn => // hg [<-] /=; apply write_var_remove.
    + t_xrbindP => ? /(remove_glob_eP hval) h <- ??.
      rewrite hmem /= => /h[] ? -> /value_uinclE {}h /to_wordI[] ? [] ? [] ? h1; subst.
      case: h => ? [] ? [] ? h2; subst.
      rewrite /= (word_uincl_truncate h2 h1) /=.
      move => ? /to_wordI[] ? [] ? [] ?; subst => /= -> /= ? -> <- /=.
      by eexists; split; last reflexivity.
    + case: ifPn => hg //.
      t_xrbindP => ? /(remove_glob_eP hval) h <-.
      apply: on_arr_varP => ?? hty.
      rewrite /= /get_var /on_arr_var /=; t_xrbindP => _ ht.
      have := hm1 _ hg; rewrite ht => /value_uinclE[] ? -> {} ht.
      rewrite orbT /= => ? ? /h[] ? -> /value_uinclE {} h /to_intI ?; subst => /=; subst => /=.
      move => ? -> t ok_t ok_s' /=.
      have := WArray.uincl_set ht ok_t.
      case => t' [] -> ok_t' /=.
      by apply: write_var_remove_uincl; eauto.
    case: ifPn => hg //.
    t_xrbindP => ? /(remove_glob_eP hval) h <-.
    apply: on_arr_varP => ?? hty; rewrite /= /get_var /on_arr_var.
    t_xrbindP => hdef ht.
    have := hm1 _ hg.
    rewrite ht => /value_uinclE[] t' -> ht' ?? /h[] ? -> /value_uinclE {} h /to_intI ?; subst; subst.
    move => arr ok_arr sub ok_sub ok_w.
    rewrite orbT /= ok_arr /=.
    have := WArray.uincl_set_sub ht' (WArray.uincl_refl _) ok_sub.
    case => sub' -> ok_sub' /=.
    by apply: write_var_remove_uincl; eauto.
  Qed.

  Lemma remove_glob_lvsP wdb m ii s1 s1' s2 lv lv' v :
    valid m s1 s2 ->
    mapM (remove_glob_lv ii m) lv = ok lv' ->
    write_lvals wdb gd s1 lv v = ok s1' ->
    exists2 s2',
      write_lvals wdb gd s2 lv' v = ok s2'
      & valid m s1' s2'.
  Proof.
    elim: lv lv' v s1 s1' s2 => //=.
    + by move=> ? []// s1 s1' s2 ? [<-] [<-]; exists s2.
    move=> x xs hrec lv' vs s1 s1' s2 hval.
    t_xrbindP=> x' /(remove_glob_lvP hval) h1 xs' /hrec h2 <-.
    case: vs => // v vs.
    t_xrbindP => s3 /h1 [s4 [hs4 w4]] /(h2 _ _ _ _ hs4) [s5 w5 hs5].
    exists s5 => //.
    by rewrite /write_lvals /= w4.
  Qed.

  Lemma check_dataP gv gv' ty :
    convertible (type_of_glob_value gv) ty →
    check_data gv' gv →
    type_of_val (gv2val gv') = eval_atype ty ∧ value_uincl (gv2val gv) (gv2val gv').
  Proof.
    case: gv gv' => [ ws w | len arr ] [ ws' w' | len' arr' ] //=.
    - move/eqP => <- /andP[] /eqP ? /eqP ->; subst.
      by rewrite zero_extend_u.
    case: ty => // ws n /eqP; rewrite arr_sizeE Z.mul_1_l => eq_len /WArray.is_uinclP => h.
    split; last by [].
    by case: h => ? _; subst; congr carr; rewrite -eq_len.
  Qed.

  Lemma find_globP ii xi gv g :
    find_glob ii xi gd gv = ok g ->
    exists2 gv', get_global gd g = ok (gv2val gv') & value_uincl (gv2val gv) (gv2val gv').
  Proof.
    rewrite /find_glob /get_global /get_global_value.
    elim: gd uniq_gd => //= -[g' gv'] gd hrec /andP /= [hg' huniq]; case: ifPn => /= /andP.
    + case => /= ok_type ok_data /ok_inj ?; subst g'.
      rewrite eq_refl /=.
      have [ -> h ] := check_dataP ok_type ok_data.
      rewrite eq_refl.
      by eexists; first reflexivity.
    move=> hn /(hrec huniq) hget {hrec}.
    case: eqP => heq //; subst g'.
    case: hget hg' => gv₀.
    case heq : assoc => [z1 | // ].
    by rewrite (assoc_mem_dom' heq).
  Qed.

  Lemma MinclP m1 m2 x g :
    Mincl m1 m2 ->
    Mvar.get m1 x = Some g ->
    Mvar.get m2 x = Some g.
  Proof.
    move=> /allP hincl.
    have /= h := Mvar.elementsP (x,g) m1.
    by move=> /h {h} /hincl;case: Mvar.get => //= g' /eqP ->.
  Qed.

  Lemma valid_Mincl m1 m2 s s' :
    Mincl m1 m2 ->
    valid m2 s s' ->
    valid m1 s s'.
  Proof.
    move=> hincl [hscs hmem hm1 hm2 hm3];split => //.
    + by move=> x g /(MinclP hincl) -/hm2.
    by move=> x g /(MinclP hincl); apply hm3.
  Qed.

  Lemma merge_incl_l m1 m2 : Mincl (merge_env m1 m2) m1.
  Proof.
    apply /allP => -[x g].
    rewrite /merge_env => /Mvar.elementsP /=.
    rewrite Mvar.map2P //. case: Mvar.get => // g1.
    by case: Mvar.get => //= g2; case:ifP => // _ [<-].
  Qed.

  Lemma merge_incl_r m1 m2 : Mincl (merge_env m1 m2) m2.
  Proof.
    apply /allP => -[x g].
    rewrite /merge_env => /Mvar.elementsP /=.
    rewrite Mvar.map2P //. case: Mvar.get => // g1.
    by case: Mvar.get => //= g2; case:ifP => // /eqP <- [<-].
  Qed.

  Lemma MinclR m : Mincl m m.
  Proof. by apply /allP => -[x g] /Mvar.elementsP ->. Qed.

  Lemma MinclT m2 m1 m3: Mincl m1 m2 -> Mincl m2 m3 -> Mincl m1 m3.
  Proof.
    move=> /allP h1 /allP h2; apply /allP => x /h1.
    case heq : (Mvar.get m2 x.1) => [g|//] /eqP ?; subst g.
    by apply h2; apply /Mvar.elementsP.
  Qed.

  Local Lemma loopP check_c n m m' c':
    loop check_c n m = ok (m', c') ->
      exists m1,
      [/\ check_c m' = ok (m1,c'), Mincl m' m1 & Mincl m' m].
  Proof.
    elim: n m => //= n hrec m; t_xrbindP => -[m2 c2] /= hc.
    case:ifP => hincl.
    + by move=> []??; subst m' c2; exists m2;split => //;apply MinclR.
    move=> /hrec => -[m1 [hc' h1 h2]]. exists m1;split=>//.
    apply: (MinclT h2);apply merge_incl_l.
  Qed.

  Lemma loop2P check_c2 n m e c1 c2 m1:
    loop2 check_c2 n m = ok (Loop2_r e c1 c2 m1) ->
    exists m2 m3,
      [/\ check_c2 m3 = ok (Check2_r e (m1,c1) (m2,c2)), Mincl m3 m2 & Mincl m3 m].
  Proof.
    elim: n m => //= n hrec m; t_xrbindP.
    move=> [e' [m1' c1'] [m2' c2']] heq; case:ifPn => hincl.
    + move=> [] ????; subst e' c1' c2' m1'.
      by exists m2', m; split => //; apply MinclR.
    move=> /hrec [m2 [m3 [h1 h2]]] hm3; exists m2, m3; split=>//.
    apply: (MinclT hm3); apply merge_incl_l.
  Qed.

  Local Lemma get_fundefP fn f:
    get_fundef (p_funcs P) fn = Some f ->
    exists f',
       get_fundef (p_funcs P') fn = Some f' /\
       remove_glob_fundef gd f = ok f'.
  Proof.
    move=> hget.
    have [f' hget' hremove] := get_map_cfprog_gen fds_ok hget.
    by exists f'.
  Qed.

  Lemma evaluate_bytesP ii xi es vs s:
    evaluate_bytes ii xi es = ok vs ->
    sem_pexprs true gd s es = ok vs.
  Proof.
    rewrite /evaluate_bytes /sem_pexprs.
    elim: es vs; first by case.
    move => e es ih vs' /=.
    case: e => // - [] // sz [] // z /=.
    by t_xrbindP => vs /ih -> <-.
  Qed.

  Lemma array_from_cellsP ii xi len cells arr s bytes :
    array_from_cells ii xi len cells = ok arr →
    sem_pexprs true gd s cells = ok bytes →
    sem_opN (Oarray len) bytes = ok (Varr arr).
  Proof.
    rewrite /array_from_cells; t_xrbindP => ? /evaluate_bytesP - /(_ s) -> h /ok_inj ?; subst.
    case: sem_opN h => // v /=.
    case h: to_arr => // /ok_inj ?; subst.
    by rewrite (to_arrI h).
  Qed.

  Lemma valid_set ii (x: var_i) m s s' g gv v :
    is_glob_var x →
    find_glob ii x gd gv = ok g →
    value_uincl (vm_truncate_val (eval_atype (vtype x)) v) (gv2val gv) →
    valid m s s' →
    valid (Mvar.set m x g) (with_vm s (evm s).[x <- v]) s'.
  Proof.
    move => hglob hfind htr [] hscs hm hm1 hm2 hm3; split => //=.
    * move=> y hy; rewrite Vm.setP_neq; first by apply hm1.
      by apply/eqP => ?;subst y;move: hy;rewrite hglob.
    * by move=> y gy;rewrite Mvar.setP; case:eqP => [<- // | ?]; apply hm2.
    move=> y gy;rewrite Mvar.setP Vm.setP //; case:eqP => [|/eqP hneq]; last by apply hm3.
    move=> ?[?]; subst.
    case: (find_globP hfind) => gv' -> hgv.
    eexists; first reflexivity.
    exact: value_uincl_trans htr hgv.
  Qed.

  Lemma Hassgn_aux m m' ii x tag ty e c' :
    remove_glob_i gd m (MkI ii (Cassgn x tag ty e)) = ok (m', c') ->
    forall s1 s2 s1', valid m s1 s1' ->
      sem_assgn P x tag ty e s1 = ok s2 ->
      exists2 s2', esem P' ev c' s1' = ok s2' & valid m' s2 s2'.
  Proof.
    rewrite /= /sem_assgn; t_xrbindP => e' he hx s1 s2 s1' hval v hv v' htr hw.
    have [ w ok_w v_w ] := remove_glob_eP hval he hv. clear he.
    have h :
      (Let lv := remove_glob_lv ii m x in
      ok (m, [:: MkI ii (Cassgn lv tag ty e')])) = ok (m', c') ->
      exists2 s2', esem P' ev c' s1' = ok s2' & valid m' s2 s2' .
    + t_xrbindP => x' /(remove_glob_lvP hval) h <- <-.
      rewrite /= /sem_assgn ok_w /=.
      have [ w' -> v_w' /= ] := value_uincl_truncate v_w htr.
      have [ vm ] := write_uincl (vm_uincl_refl _) v_w' hw.
      rewrite with_vm_same => {} hw' le_vm.
      move: h => /(_ true _ w' hw')[] s2' [] hval' ->.
      eexists; first reflexivity.
      exact: vm_uincl_valid le_vm.
    case: x hw h hx => //=.
    move=> xi hxi hdef; case: ifPn => // hglob {hdef}.
    case: e' ok_w => // [ [] // sz [] // z /= /ok_inj ? | [] // len cells /= ]; last first.
    + t_xrbindP => bytes ok_bytes ok_w.
      case: ifP => // htxi.
      t_xrbindP => arr ok_arr g hfind <-{m'} <-{c'}.
      eexists; first reflexivity.
      move/write_varP: hxi => [-> hdb htr'].
      apply: (valid_set hglob hfind) hval.
      move: htr'.
      rewrite (convertible_eval_atype htxi) /=.
      case: v' htr hdb => //; move => len' arr' /truncate_valI; case => hty ? _; subst.
      move=>/eqP ?; subst.
      rewrite /= eqxx.
      move: ok_w.
      by rewrite (array_from_cellsP ok_arr ok_bytes) => /ok_inj ->.
    subst.
    case: andP => //= -[hty htxi].
    move: htr; rewrite (convertible_eval_atype hty) /truncate_val /=.
    t_xrbindP => w ok_w ?; subst => g hfind <- <-; exists s1' => //.
    move/write_varP: hxi => [-> hdb htr].
    apply: (valid_set hglob hfind) hval.
    have /vm_truncate_valE [ws] := htr.
    rewrite (convertible_eval_atype htxi) => -[] [<-] _ ->.
    rewrite cmp_le_refl.
    case/to_wordI: ok_w => ? [] ? [] ?; subst.
    case/truncate_wordP => sz_le ?; subst.
    case/andP: v_w => le_sz /eqP ?; subst.
    have ? := cmp_le_antisym sz_le le_sz; subst.
    by rewrite ! zero_extend_u.
  Qed.

  Section SEM.

  Let Pc s1 c s2 :=
    forall m m' c', remove_glob (remove_glob_i gd) m c = ok (m', c') ->
    forall s1', valid m s1 s1' ->
    exists s2', valid m' s2 s2' /\ sem P' ev s1' c' s2'.

  Let Pi s1 i s2 :=
    forall m m' c', remove_glob_i gd m i = ok (m', c') ->
    forall s1', valid m s1 s1' ->
    exists s2', valid m' s2 s2' /\ sem P' ev s1' c' s2'.

  Let Pi_r s1 i s2 := forall ii, Pi s1 (MkI ii i) s2.

  Let Pfor xi vs s1 c s2 :=
    ~~is_glob_var xi.(v_var) ->
    forall m m' c', remove_glob (remove_glob_i gd) m c = ok (m', c') ->
    Mincl m m' ->
    forall s1', valid m s1 s1' ->
    exists s2', valid m s2 s2' /\ sem_for P' ev xi vs s1' c' s2'.

  Let Pfun scs m fn vargs scs' m' vres :=
    exists2 vres',
    List.Forall2 value_uincl vres vres' &
    sem_call P' ev scs m fn vargs scs' m' vres'.

  Local Lemma Hnil : sem_Ind_nil Pc.
  Proof.
    move=> s1 m m' c' /= [<- <-] s1' hv; exists s1';split => //.
    econstructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons P ev Pc Pi.
  Proof.
    move=> s1 s2 s3 i c _ hi _ hc m m' c' /=.
    t_xrbindP => -[mi ci] /hi{}hi [mc cc] /hc{}hc <- <- ? /hi [s2' [/hc [s3' [hv sc] si]]].
    exists s3';split => //=; apply: sem_app si sc.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI P ev Pi_r Pi.
  Proof. done. Qed.

  Local Lemma Hasgn : sem_Ind_assgn P Pi_r.
  Proof.
    move=> s1 s2 x tag ty e v v' he hv hw ii m m' c' hrm s1' hval.
    have /(_ s2) [|s2' /esem_sem ? ?]:= Hassgn_aux hrm hval.
    + by rewrite /sem_assgn he /= hv /=.
    by exists s2'.
  Qed.

  Local Lemma Hopn : sem_Ind_opn P Pi_r.
  Proof.
   move=> s1 s2 t o xs es ho ii m m' c /= hrm s1' hval.
   move: hrm; t_xrbindP.
   move=> xs' /(remove_glob_lvsP hval) hxs' es' /(remove_glob_esP hval) hes' <- <-.
   move: ho;rewrite /sem_sopn; t_xrbindP => vs vres /hes'[] vs' h1 vs_vs' h2 /hxs' [s2' h hval'].
   have [ vs'' {} h2 vs_vs'' ] := vuincl_exec_opn vs_vs' h2.
   have [ vm ] := writes_uincl (vm_uincl_refl _) vs_vs'' h.
   rewrite with_vm_same => {} h le_vm.
   eexists; split; first exact: valid_vm_uincl le_vm.
   by apply sem_seq1; constructor; constructor; rewrite /sem_sopn h1 /= h2 /= h.
  Qed.

  Local Lemma Hsyscall : sem_Ind_syscall P Pi_r.
  Proof.
   move=> s1 scs mem s2 o xs es ves vs hes ho hw ii m m' c /= hrm s1' hval.
   move: hrm; t_xrbindP => xs' hrlv es' hres <- <-.
   have [ vres' hes' hvres' ] := remove_glob_esP hval hres hes.
   have [ vs' ho' hvs' ] := exec_syscallP ho hvres'.
   have [ vm /= hw' le_vm ] := writes_uincl (vm_uincl_refl _) hvs' hw.
   have hval' : valid m (with_vm (with_scs (with_mem s1 mem) scs) (evm s1)) (with_scs (with_mem s1' mem) scs).
   + by case: hval.
   have [ s2' hw'' hval'' ] := remove_glob_lvsP hval' hrlv hw'.
   exists s2'; split.
   + exact: vm_uincl_valid le_vm.
   apply sem_seq1; constructor; econstructor; eauto.
   by case: hval => <- <- *; exact: ho'.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true P ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 he _ hc ii m m' c' /= hrm s1' hval.
    move: hrm; t_xrbindP => e' /(remove_glob_eP hval) -/(_ _ _ he) [] [] // [] // he' _.
    move=> [m1 c1'] /hc -/(_ _ hval) [s2' [hval' hc1']].
    move=> [m2 c2'] h /= <- <-.
    exists s2'; split.
    + apply: valid_Mincl hval'; apply merge_incl_l.
    by apply sem_seq1; constructor; apply Eif_true.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false P ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 he _ hc ii m m' c' /= hrm s1' hval.
    move: hrm; t_xrbindP => e' /(remove_glob_eP hval) -/(_ _ _ he) [] [] // [] // he' _.
    move=> [m1 c1'] h /= [m2 c2'] /hc -/(_ _ hval) [s2' [hval' hc1']] <- <-.
    exists s2'; split.
    + apply: valid_Mincl hval'; apply merge_incl_r.
    by apply sem_seq1; constructor; apply Eif_false.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true P ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e ei c' _ hc he _ hc' _ hw ii m m' c'0 /= hrn s1' hval.
    move: hrn; t_xrbindP => -[e' c1' c2' m1] /loop2P [m2 [m3 []]].
    t_xrbindP => -[m4 c4] h1 /= e1 he1 [m5 c5] h2.
    have h1' := hc _ _ _ h1.
    have h2' := hc' _ _ _ h2.
    move=> ? [??] [??] hm hm1 ? <-;subst e1 m4 c4 m5 c5 m1.
    have /h1' [s2' [hs2 hc1]]: valid m3 s1 s1' by apply: valid_Mincl hval.
    have := remove_glob_eP hs2 he1 he.
    case => - [] // [] // he' _.
    have [s3' [hs3 hc2]]:= h2' _ hs2.
    have : remove_glob_i gd m3 (MkI ii (Cwhile a c e ei c')) =
             ok (m', [::MkI ii (Cwhile a c1' e' ei c2')]).
    + by rewrite /= Loop.nbP /= h1 /= he1 /= h2 /= hm.
    move=> /hw{}hw; have /hw : valid m3 s3 s3' by apply: (valid_Mincl hm).
    move=> [s4' [hs4 /semE hw']]; exists s4';split => //.
    apply sem_seq1; constructor; apply: Ewhile_true;eauto.
    by case: hw' => s [] /sem_IE hw' /semE ->.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false P ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c e ei c' _ hc he ii m m' c'0 /= hrn s1' hval.
    move: hrn; t_xrbindP => -[e' c1' c2' m1] /loop2P [m2 [m3 []]].
    t_xrbindP => -[m4 c4] h1 /= e1 he1 [m5 c5] h2.
    move=> ? [??] [??] hm hm1 ? <-;subst e1 m4 c4 m5 c5 m1.
    have h1' := hc _ _ _ h1.
    have /h1' [s2' [hs2 hc1]]: valid m3 s1 s1' by apply: valid_Mincl hval.
    have := remove_glob_eP hs2 he1 he.
    case => - [] // [] // he' _.
    exists s2';split => //.
    by apply sem_seq1;constructor;apply: Ewhile_false.
  Qed.

  Local Lemma Hfor : sem_Ind_for P ev Pi_r Pfor.
  Proof.
    move=> s1 s2 i d lo hi c vlo vhi hlo hhi _ hfor ii m m' c' /= hrn s1' hval.
    case : ifPn hrn => // hglob.
    t_xrbindP => lo' /(remove_glob_eP hval) -/(_ _ _ hlo) [] ? hlo' /value_uinclE ?; subst.
    move=> hi' /(remove_glob_eP hval) -/(_ _ _ hhi) [] ? hhi' /value_uinclE ?; subst.
    move=> [m2 c2] /= /loopP [m1 [hc h1 h2]] [??];subst m2 c'.
    have hval': valid m' s1 s1' by apply: valid_Mincl hval.
    have [s2' [??]]:= hfor hglob _ _ _ hc h1 _ hval'.
    exists s2';split => //.
    apply sem_seq1;constructor;econstructor;eauto.
  Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s xi c ii m m' c' hrm hincl s1' hval; exists s1';split => //; constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P ev Pc Pfor.
  Proof.
    move=> s1 s2 s3 s4 xi w ws c hw _ hc _ hfor hglob m m' c' hrm hincl s1' hval.
    have [s2' [hs2' ws2']]:= write_var_remove hglob hval hw.
    have [s3' [hs3' ws3']]:= hc _ _ _ hrm _ hs2'.
    have hval' := valid_Mincl hincl hs3'.
    have [s4' [hs4' ws4']]:= hfor hglob _ _ _ hrm hincl _ hval'.
    exists s4'; split => //; econstructor; eauto.
  Qed.

  Local Lemma Hcall : sem_Ind_call P ev Pi_r Pfun.
  Proof.
    move=> s1 scs2 m2 s2 xs fn args vargs rvs hargs _ hfun hres ii m m' c' /=
      hrm s1' hval.
    move: hrm; t_xrbindP => xs' hxs es' hes ??;subst m' c'.
    have := remove_glob_esP hval hes hargs.
    case => vargs' hes' hvargs.
    case: hfun => vres hvres /(sem_call_uincl hvargs).
    case => vres' [] hfun' hvres'.
    have := writes_uincl (vm_uincl_refl _) (values_uincl_trans hvres hvres') hres.
    case => vm hres' le_vm.
    have hval' : valid m (with_scs (with_mem s1 m2) scs2) (with_scs (with_mem s1' m2) scs2).
    + by case: hval;split.
    have [s2' hxs' hs2' ]:= remove_glob_lvsP hval' hxs hres'.
    exists s2';split.
    + exact: vm_uincl_valid le_vm.
    apply sem_seq1;constructor;econstructor;eauto.
    by case: hval => <- <-.
  Qed.

  Local Lemma Hproc : sem_Ind_proc P ev Pc Pfun.
  Proof.
    move=> scs1 m1 scs2 m2 fn f vargs vargs' s0 s1 s2 vres vres' hget hargs hwa hi _ hc hres hres' hscs hfi.
    rewrite /Pfun; have [f' [hget']]:= get_fundefP hget.
    rewrite /remove_glob_fundef; t_xrbindP => ? hparams res1 hres1 [m' c'] hrm ?;subst f'.
    have hval: valid (Mvar.empty var) s1 s1 by split.
    have [s2' [hs2' ws2]] := hc _ _ _ hrm _ hval.
    subst m2; case: (hs2') => /= hscse hmem hm _ _.
    have : exists2 vres', get_var_is (~~ direct_call) (evm s2') (f_res f) = ok vres' & List.Forall2 value_uincl vres vres'.
    + elim: (f_res f) (vres) res1 hres1 hres.
      * by move => _ _ _ /ok_inj <-; exists [::]; constructor.
      move => x xs hrec vres0 res1 /=.
      t_xrbindP; case: ifPn => hglob // _ ? /hrec hres1 ? v.
      case/(get_var_uincl_at (hm _ hglob)) => v' -> v_v' vs /hres1[] vs' -> vs_vs' <- /=; eauto.
    case => vs ok_vs vres_vs.
    have := mapM2_dc_truncate_val hres' vres_vs.
    case => vs' ok_vs' vres_vs'.
    subst scs2.
    eexists; last econstructor; eauto.
  Qed.

  Local Lemma remove_glob_call scs1 m1 f vargs scs2 m2 vres :
     sem_call P ev scs1 m1 f vargs scs2 m2 vres ->
     Pfun scs1 m1 f vargs scs2 m2 vres.
  Proof.
    exact:
      (sem_call_Ind
         Hnil
         Hcons
         HmkI
         Hasgn
         Hopn
         Hsyscall
         Hif_true
         Hif_false
         Hwhile_true
         Hwhile_false
         Hfor
         Hfor_nil
         Hfor_cons
         Hcall
         Hproc).
  Qed.

  End SEM.

  Section IT.

  Context {E E0: Type -> Type} {wE : with_Error E E0} {rE : EventRels E0}.

  Definition check_es_valid ii (d:venv) (es1 es2 : pexprs) (d':venv) :=
    d = d' /\ mapM (remove_glob_e ii d) es1 = ok es2.

  Definition check_lvals_valid ii (d:venv) (xs1 xs2 : lvals) (d':venv) :=
    d = d' /\ mapM (remove_glob_lv ii d) xs1 = ok xs2.

  Lemma check_esP_R_valid ii d es1 es2 d' :
    check_es_valid ii d es1 es2 d' →
    ∀ s1 s2, valid d s1 s2 → valid d' s1 s2.
  Proof. by move=> [<-]. Qed.

  Definition checker_valid ii : Checker_e valid :=
    {| check_es := check_es_valid ii
     ; check_lvals := check_lvals_valid ii
     ; check_esP_rel := @check_esP_R_valid ii
    |}.

  Lemma checker_validP ii : Checker_uincl P P' (checker_valid ii).
  Proof.
    constructor.
    + move=> > /wdb_ok_eq <- [_ hes] s1 s2 vs hval hses.
      exact: remove_glob_esP hval hes hses.
    move=> > /wdb_ok_eq <- [<- hxs] vs vs' vs_vs' s1 s2 s1' hval hw.
    have [ s2' hw' hval' ]  :=  remove_glob_lvsP hval hxs hw.
    have := writes_uincl (vm_uincl_refl _) vs_vs' hw'.
    rewrite with_vm_same => - [] vm -> le_vm.
    eexists; first reflexivity.
    exact: valid_vm_uincl.
  Qed.
  #[local] Hint Resolve checker_validP : core.

  Let Pi i :=
    forall d dc, remove_glob_i gd d i = ok dc ->
    wequiv_rec P P' ev ev uincl_spec (valid d) [::i] dc.2 (valid dc.1).

  Let Pi_r i := forall ii, Pi (MkI ii i).

  Let Pc c :=
    forall d dc, remove_glob (remove_glob_i gd) d c = ok dc ->
    wequiv_rec P P' ev ev uincl_spec (valid d) c dc.2 (valid dc.1).

  Lemma it_remove_glob_call fn : wiequiv_f P P' ev ev (rpreF (eS:= uincl_spec)) fn fn (rpostF (eS:=uincl_spec)).
  Proof.
    apply wequiv_fun_ind => {}fn _ fs fs' [<-] hfs fd hget.
    have [fd' [hget' hfd']]:= get_fundefP hget.
    have fsi := fs_uincl_initialize (fd := fd) (fd' := fd').
    exists fd' => //.
    move: hfd'; rewrite /remove_glob_fundef; t_xrbindP => _tt hparams res1 hres1 [m' c'] hrm ?;subst fd' => /=.
    move=> s1 /fsi /= /(_ _ _ erefl erefl erefl erefl hfs)[] s1' hinit hs1.
    exists s1'; first exact: hinit.
    exists (valid (Mvar.empty var)), (valid m'); split => // {hfs fsi hget hinit}; cycle -1.
    + move=> {hs1} s1 s2 {} fs [/= hscse hmem hm _ _]; rewrite /finalize_funcall /=; t_xrbindP.
      move=> vs hget vs' htr <-.
      have : exists2 vres', get_var_is (~~ direct_call) (evm s2) (f_res fd) = ok vres' & List.Forall2 value_uincl vs vres'.
      - elim: (f_res fd) (vs) res1 hres1 hget.
        * by move => _ _ _ /ok_inj <-; exists [::]; constructor.
        move => x xs hrec vres0 res1 /=.
        t_xrbindP; case: ifPn => hglob // _ ? /hrec hres1 ? v.
        case/(get_var_uincl_at (hm _ hglob)) => v' -> v_v' qs /hres1[] qs' -> qs_qs' <- /=; eauto.
      case => vres' -> vs_vres' /=.
      have := mapM2_dc_truncate_val htr vs_vres'.
      case => vs'' -> vs'_vs'' /=.
      by eexists; first reflexivity.
    + by case: hs1 => ?? le_vm.
    move: hrm; set dc_ := (m', c'); have [-> ->] : m' = dc_.1 /\ c' = dc_.2 by done.
    move: (f_body fd) (Mvar.empty var) dc_ => {fn fd m' c' hget' _tt hparams res1 hres1}.
    apply (cmd_rect (Pr := Pi_r) (Pi:=Pi) (Pc:=Pc)) => //.
    + by move=> d _ [<-]; apply wequiv_nil.
    + move=> i c hi hc d dc_ /=; t_xrbindP => dci /hi{}hi ? /hc{}hc <-.
      by rewrite -cat1s; apply wequiv_cat with (valid dci.1).
    + move=> x tg ty e ii d [d' c'] hrm.
      apply wequiv_assgn_esem => {hs1} s1 s2 {} s1' hval hsem.
      by apply (Hassgn_aux hrm hval hsem).
    + move=> xs tg o es ii d dc_ /=; t_xrbindP => xs' hxs' es' hes' <- /=.
      by apply wequiv_opn_rel_uincl with (checker_valid ii) d.
    + move=> xs o es ii d dc_ /=; t_xrbindP => xs' hxs' es' hes' <- /=.
      apply wequiv_syscall_rel_uincl_core_R with (checker_valid ii) d d => //.
      + by move=> > []. + by move=> > [?????].
      exact: fs_uincl_syscall.
    + move=> e c1 c2 hc1 hc2 ii d dc_ /=; t_xrbindP.
      move=> e' he' dc1 /hc1{}hc1 dc2 /hc2{}hc2 <- /=.
      apply wequiv_if_rel_uincl_R with (checker_valid ii) d dc1.1 dc2.1 => //.
      + by split => //=; rewrite he'.
      + by move=> >; apply/valid_Mincl/merge_incl_l.
      by move=> >; apply/valid_Mincl/merge_incl_r.
    + move=> v dir lo hi c hc ii d dc_ /=.
      case: ifP => // hv; t_xrbindP => lo' hlo hi' hhi [d' c'] /loopP [d1] [/hc{}hc hincl1 hincl2] [<-] /=.
      apply wequiv_for_rel_uincl_R with (checker_valid ii) d d' => //.
      + by split => //=; rewrite hlo /= hhi.
      + by move=> >; apply valid_Mincl.
      + by split => //=; rewrite hv.
      apply wequiv_weaken with (valid d') (valid d1) => //.
      by move=> >; apply valid_Mincl.
    + move=> a c1 e ii' c2 hc1 hc2 ii d dc_ /=; t_xrbindP.
      move=> [e' c1' c2' d'] /loop2P [d1][d2] []; t_xrbindP.
      move=> [d1_ c1_] /hc1/={}hc1 /= e_ he [d2_ c2_] /hc2/={}hc2 ? [??] [??] hincl1 hincl2 <- /=.
      subst e_ d1_ c1_ d2_ c2_.
      apply wequiv_weaken with (valid d2) (valid d') => //.
      + by move=> >; apply valid_Mincl.
      apply wequiv_while_rel_uincl with (checker_valid ii) d' => //.
      + by split => //=; rewrite he.
      apply wequiv_weaken with (valid d') (valid d1) => //.
      by move=> >; apply valid_Mincl.
    move=> xs fn es ii d dc_ /=; t_xrbindP => xs' hxs' es' hes' <- /=.
    apply wequiv_call_rel_uincl_R with (checker_valid ii) d d => //.
    + by move=> > []. + by move=> > [?????].
    by move => ???; apply: wequiv_fun_rec.
  Qed.

  End IT.

  End FDS.

  Lemma remove_globP P P' f ev scs mem scs' mem' va vr :
    remove_glob_prog fresh_id P = ok P' ->
    sem_call P ev scs mem f va scs' mem' vr ->
    exists2 vr',
     List.Forall2 value_uincl vr vr' &
    sem_call P' ev scs mem f va scs' mem' vr'.
  Proof.
    rewrite /remove_glob_prog; t_xrbindP => gd' /extend_glob_progP hgd.
    case: ifP => // huniq; t_xrbindP => fds hfds <- h; have hf := gd_incl_fun hgd h.
    exact: (remove_glob_call (P:={| p_globs := gd'; p_funcs := p_funcs P |}) hfds huniq hf).
  Qed.

  Section IT.

  Context {E E0: Type -> Type} {wE : with_Error E E0} {rE0 : EventRels E0} {rE0_trans : EventRels_trans rE0 rE0 rE0}.

  Lemma it_remove_globP P P' ev fn:
    remove_glob_prog fresh_id P = ok P' ->
    wiequiv_f P P' ev ev (rpreF (eS:= eq_spec)) fn fn (rpostF (eS:= uincl_spec)).
  Proof.
    rewrite /remove_glob_prog; t_xrbindP => gd' /extend_glob_progP hgd.
    case: ifP => // huniq; t_xrbindP => fds hfds <-.
    have h1 := [elaborate it_gd_incl_fun ev hgd (fn := fn)].
    set P1 := {| p_funcs := p_funcs P; p_globs := gd'; p_extra := p_extra P |}.
    have h2 := it_remove_glob_call (P:=P1) ev hfds huniq (wE:=wE) (rE:=rE0) (fn:=fn).
    move: h1 h2.
    apply wiequiv_f_trans => //.
    + by move=> fs1 fs2 [] _ <-; exists fs1 => //; split => //; exact: fs_uinclR.
    by move=> ??? fs1 fs3 _ _ [fs2] <-.
  Qed.

  End IT.

End PROOFS. End RGP.
