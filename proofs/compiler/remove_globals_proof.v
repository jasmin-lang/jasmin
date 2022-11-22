(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.word Require Import ssrZ.
Require Import xseq.
Require Import compiler_util ZArith expr psem remove_globals low_memory.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition gd_incl (gd1 gd2: glob_decls) :=
  forall g v, get_global gd1 g = ok v -> get_global gd2 g = ok v.

Lemma gd_inclT gd3 gd1 gd2 :  gd_incl gd1 gd3 -> gd_incl gd3 gd2 -> gd_incl gd1 gd2.
Proof. by move=> h1 h2 g v /h1 /h2. Qed.

Module INCL. Section INCL.

  Section INCL_E.
    Context (gd1 gd2: glob_decls) (s: estate) (hincl: gd_incl gd1 gd2).
    Let P e : Prop :=
      ∀ v le, sem_pexpr gd1 s e = ok (v, le) → sem_pexpr gd2 s e = ok (v, le).
    Let Q es : Prop :=
      ∀ vs, sem_pexprs gd1 s es = ok vs → sem_pexprs gd2 s es = ok vs.

    Lemma gd_incl_e_es : (∀ e, P e) ∧ (∀ es, Q es).
    Proof.
      apply: pexprs_ind_pair; split; subst P Q => //=.
      - move => e rec es ih q. t_xrbindP. move=> [ve le] ok_v vs ok_vs <-.
        move: (rec ve le ok_v). move=> -> /=. move: (ih vs ok_vs).
        by move=> -> /=.
      (* Pglobal *)  
      - move=> g v le. t_xrbindP. move=> v' Hg <- <-. move: hincl.
        rewrite /gd_incl. move=> H. move:(H g v' Hg). by move=> -> /=.
      (* Pget *)
      - move => sz x e rec v l. apply: on_arr_varP => n t h1 h2.
        t_xrbindP. move=> [ve le] He z Hi w Ha <- <- /=.
        rewrite /on_arr_var. rewrite h2 /=. move: (rec ve le He).
        move=> -> /=. rewrite Hi /=. by rewrite Ha /=.
      (* Pload *)
      - move=> sz x e rec v l. t_xrbindP.
        by move=> vp vg -> /= -> /= [ve le] /rec -> /= vp' -> /= vw -> /= <- <- /=.
      (* Papp1 *)
      - move=> op e rec v l. t_xrbindP. by move=> [ve le] /rec -> /= vo -> <- <- /=.
      (* Papp2 *)
      - move=> op e1 rec1 e2 rec2 v l. t_xrbindP.
        by move=> [ve le] /rec1 -> /= [ve' le'] /rec2 -> /= vo -> /= <- <- /=.
      (* PappN *)
      - move=> op es rec v le. t_xrbindP. rewrite /sem_pexprs in rec.
        by move=> ys /rec -> /= vo -> /= <- <-.
      (* Pif *)    
      - move=> ty e rece e1 rece1 e2 rece2. t_xrbindP.
        by move=> hv hl [ve le] /rece -> /= be -> /= [ve1 le1] /rece1 -> /=
                  [ve2 le2] /rece2 -> /= tv -> /= tv' -> /= <- <-.
    Qed.

  End INCL_E.

  Definition gd_incl_e gd1 gd2 s e v h :=
    (@gd_incl_e_es gd1 gd2 s h).1 e v.

  Definition gd_incl_es gd1 gd2 s es vs h :=
    (@gd_incl_e_es gd1 gd2 s h).2 es vs.

  Lemma gd_incl_wl gd1 gd2 x v s1 s2 lw:
    gd_incl gd1 gd2 ->
    write_lval gd1 x v s1 = ok (s2, lw) ->
    write_lval gd2 x v s1 = ok (s2, lw).
  Proof.
    move=> hincl. case: x=> //=.
    (* Lmem *)
    + move=> ws x e. t_xrbindP. move=> vp vg -> /= -> /= [ve le] /(gd_incl_e hincl) -> /=.
      by move=> vp' -> /= vw -> /= m -> /= <- <-.
    (* Laset *)
    move=> sz x e. apply: on_arr_varP;rewrite /on_arr_var => ?? h1 ->. t_xrbindP.
    by move=> [ve le] /(gd_incl_e hincl) -> /= vi -> /= vw -> /= va -> /= vm -> /= <- <-.
  Qed.

  Lemma gd_incl_wls gd1 gd2 xs vs s1 s2 lw:
    gd_incl gd1 gd2 ->
    write_lvals gd1 s1 xs vs = ok (s2, lw) ->
    write_lvals gd2 s1 xs vs = ok (s2, lw).
  Proof.
    rewrite /write_lvals.
    move=> hincl;elim: xs vs s1 s2 [::] lw => //= x xs hrec [|v vs] s1 s2 lw1 lw //=.
    t_xrbindP. by move=> [s' lw'] /(gd_incl_wl hincl) -> /= [s'' lws] /hrec -> <- <- /=.
  Qed.

  Context (P1:prog) (gd2:glob_decls).

  Notation gd := (P1.(p_globs)).

  Hypothesis hincl : gd_incl gd gd2.

  Let P2 := {| p_globs := gd2; p_funcs := P1.(p_funcs) |}.

  Let Pc s1 c s2 := sem P2 s1 c s2.

  Let Pi_r s1 i s2 := sem_i P2 s1 i s2.

  Let Pi s1 i s2 := sem_I P2 s1 i s2.

  Let Pfor x vs s1 c s2 := sem_for P2 x vs s1 c s2.

  Let Pfun m1 fn vs1 m2 vs2 := sem_call P2 m1 fn vs1 m2 vs2.

  Local Lemma Hnil : sem_Ind_nil Pc.
  Proof. move=> s; constructor. Qed.

  Local Lemma Hcons : sem_Ind_cons P1 Pc Pi.
  Proof. by move=> s1 s2 s3 i c li lc ? h1 ?; apply: Eseq. Qed.

  Local Lemma HmkI : sem_Ind_mkI P1 Pi_r Pi.
  Proof. move=> ??????;apply: EmkI. Qed.

  Local Lemma Hasgn : forall (s1 s2 : estate) (x : lval) (tag : assgn_tag) ty (e : pexpr) v v' le lw,
    sem_pexpr gd s1 e = ok (v, le) ->
    truncate_val ty v = ok v' ->
    write_lval gd x v' s1 = ok (s2, lw) ->
    Pi_r s1 (Cassgn x tag ty e) (Lopn (LSub ([:: le ; lw]))) s2.
  Proof.
    move=> ?????????? /(gd_incl_e hincl) h1 h2 /(gd_incl_wl hincl) h3.
    apply: Eassgn;eauto.
  Qed.

  Local Lemma Hopn : forall (s1 s2 : estate) t (o : sopn) (xs : lvals) (es : pexprs) lo,
    sem_sopn gd o s1 xs es = Ok error (s2, lo) ->
    Pi_r s1 (Copn xs t o es) (Lopn lo) s2.
  Proof.
    move=> s1 s2 ty o xs es lo;rewrite /sem_sopn.
    t_xrbindP. move=> ys /(gd_incl_es hincl) h1 ve h2 [vws lws] /(gd_incl_wls hincl) h3 <- <-.
    econstructor. rewrite /sem_sopn. replace (p_globs P2) with gd2. rewrite h1 /=.
    rewrite h2 /=. rewrite h3 /=. auto. constructor.
  Qed.

  Local Lemma Hif_true : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) le lc,
    sem_pexpr gd s1 e = ok (Vbool true, le) ->
    sem P1 s1 c1 lc s2 -> Pc s1 c1 lc s2 -> Pi_r s1 (Cif e c1 c2) (Lcond le true lc) s2.
  Proof.
    move=> s1 s2 e c1 c2 le lc /(gd_incl_e hincl) h1 ? h2; apply Eif_true.
    replace (p_globs P2) with gd2. auto. constructor. auto.
  Qed.

  Local Lemma Hif_false : forall (s1 s2 : estate) (e : pexpr) (c1 c2 : cmd) le lc,
    sem_pexpr gd s1 e = ok (Vbool false, le) ->
    sem P1 s1 c2 lc s2 -> Pc s1 c2 lc s2 -> Pi_r s1 (Cif e c1 c2) (Lcond le false lc) s2.
  Proof.
    move=> s1 s2 e c1 c2 le lc /(gd_incl_e hincl) h1 ? h2; apply Eif_false.
    replace (p_globs P2) with gd2. auto. constructor. auto.
  Qed.

  Local Lemma Hwhile_true : forall (s1 s2 s3 s4 : estate) a (c : cmd) (e : pexpr) (c' : cmd) lc le lc' li,
    sem P1 s1 c lc s2 -> Pc s1 c lc s2 ->
    sem_pexpr gd s2 e = ok (Vbool true, le) ->
    sem P1 s2 c' lc' s3 -> Pc s2 c' lc' s3 ->
    sem_i P1 s3 (Cwhile a c e c') li s4 -> Pi_r s3 (Cwhile a c e c') li s4 ->
    Pi_r s1 (Cwhile a c e c') (Lwhile_true lc le lc' li) s4.
  Proof.
    move=> s1 s2 s3 s4 a c e c' lc le lc' li h1 h2 /(gd_incl_e hincl) he h1' h2' h3 h4.
    apply: Ewhile_true; eauto.
  Qed.

  Local Lemma Hwhile_false : forall (s1 s2 : estate) a (c : cmd) (e : pexpr) (c' : cmd) lc le,
    sem P1 s1 c lc s2 -> Pc s1 c lc s2 ->
    sem_pexpr gd s2 e = ok (Vbool false, le) ->
    Pi_r s1 (Cwhile a c e c') (Lwhile_false lc le) s2.
  Proof.
    move=> s1 s2 a c e c' lc le h1 h1' /(gd_incl_e hincl) he.
    apply: Ewhile_false; eauto.
  Qed.

  Local Lemma Hfor : sem_Ind_for P1 Pi_r Pfor.
  Proof.
    move=> s1 s2 i r wr c lr lf /= Hr Hf Hpf /=.
    apply Efor with wr. move: Hr. rewrite /sem_range. t_xrbindP.
    case: r. move=> [d lo] hi /=. t_xrbindP. move=> [ve le] /(gd_incl_e hincl) -> /=.
    by move=> vi -> /= [ve' le'] /(gd_incl_e hincl) -> /= vi' -> /= <- <-. auto.
  Qed. 

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. move=> s1 i c;constructor. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P1 Pc Pfor.
  Proof.
    move=> s1 s1' s2 s3 i sz c c' lc lf h1 hs1 hc1 hf hpf.
    apply EForOne with s1' s2. auto. auto. auto.
  Qed.

  Local Lemma Hcall : sem_Ind_call P1 Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 ii xs fn args vargs vs lf lw /(gd_incl_es hincl) hes hc hf /(gd_incl_wls hincl) hws.
    econstructor;eauto.
  Qed.

  Local Lemma Hproc : sem_Ind_proc P1 Pc Pfun.
  Proof. move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' h1 h2 h3 h4 h5 h6 h7.
         econstructor;eauto. Qed.

  Lemma gd_incl_fun m (fn : funname) (l : seq value) m0 vs lf:
      sem_call P1 m fn l (fn, lf) m0 vs -> Pfun m fn l (fn, lf) m0 vs.
  Proof.
    apply: (@sem_call_Ind P1 Pc Pi_r Pi Pfor Pfun
             Hnil Hcons HmkI Hasgn Hopn Hif_true Hif_false Hwhile_true Hwhile_false
             Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

End INCL. End INCL. Import INCL.

Module EXTEND. Section PROOFS.

  Context (is_glob : var -> bool).
  Context (fresh_id : glob_decls -> var -> Ident.ident).

  Let Pi (i:instr) :=
    forall gd1 gd2,
      extend_glob_i is_glob fresh_id i gd1 = ok gd2 ->
      gd_incl gd1 gd2.

  Let Pr (i:instr_r) := forall ii, Pi (MkI ii i).

  Let Pc (c:cmd) :=
    forall gd1 gd2,
      foldM (extend_glob_i is_glob fresh_id) gd1 c = ok gd2 ->
      gd_incl gd1 gd2.

  Local Lemma Hmk  : forall i ii, Pr i -> Pi (MkI ii i).
  Proof. move=> ?? h;apply h. Qed.

  Local Lemma Hnil : Pc [::].
  Proof. by move=> ?? [<-]. Qed.

  Local Lemma Hcons: forall i c, Pi i -> Pc c -> Pc (i::c).
  Proof.
    by move=> i c hi hc gd1 gd2 /=;t_xrbindP => gd3 /hi h1 /hc; apply: gd_inclT.
  Qed.

  Local Lemma Hasgn: forall x tg ty e, Pr (Cassgn x tg ty e).
  Proof.
    move=> [ii ty|x|ws x e|ws x e] ?? e1 ??? //=. 1,3-4: by move=> [<-].
    case: ifP => ?; last by move=> [<-].
    case: e1 => // - [] // w [] // z; rewrite /add_glob.
    case:ifPn => hhas1; first by move=> [<-].
    case:ifPn => // /hasP hhas2 [<-] g v.
    rewrite /get_global /get_global_word /get_global_Z /=.
    case:eqP => heq //;subst g.
    case ha : assoc => [|// ].
    have /assoc_mem hin := ha; elim hhas2;eauto.
  Qed.

  Local Lemma Hopn : forall xs t o es, Pr (Copn xs t o es).
  Proof. by move=> xs t o es ii gd1 gd2 /= [<-]. Qed.

  Local Lemma Hif  : forall e c1 c2, Pc c1 -> Pc c2 -> Pr (Cif e c1 c2).
  Proof.
    move=> e c1 c2 hc1 hc2 ii gd1 gd2 /=.
    by t_xrbindP => gd3 /hc1 h1 /hc2; apply: gd_inclT.
  Qed.

  Local Lemma Hfor : forall v dir lo hi c, Pc c -> Pr (Cfor v (dir,lo,hi) c).
  Proof. by move=> ????? hc ii gd1 gd2 /= /hc. Qed.

  Local Lemma Hwhile : forall a c e c', Pc c -> Pc c' -> Pr (Cwhile a c e c').
  Proof.
    move=> a c e c' hc hc' ii gd1 gd2 /=.
    by t_xrbindP => gd3 /hc h1 /hc'; apply gd_inclT.
  Qed.

  Local Lemma Hcall: forall i xs f es, Pr (Ccall i xs f es).
  Proof. by move=> i xs f es ii gd1 gd2 /= [<-]. Qed.

  Local Lemma extend_glob_cP c gd1 gd2 :
    foldM (extend_glob_i is_glob fresh_id) gd1 c = ok gd2 ->
    gd_incl gd1 gd2.
  Proof.
    apply (@cmd_rect Pr Pi Pc Hmk Hnil Hcons Hasgn Hopn Hif Hfor Hwhile Hcall c).
  Qed.

End PROOFS.

Lemma extend_glob_progP is_glob fresh_id P gd' :
  extend_glob_prog is_glob fresh_id P = ok gd' ->
  gd_incl (p_globs P) gd'.
Proof.
  rewrite /extend_glob_prog.
  elim: (p_funcs P) (p_globs P) => /= [gd [<-] // | fd fds hrec gd].
  by t_xrbindP => gd1 /extend_glob_cP h1 /hrec; apply: gd_inclT.
Qed.

End EXTEND. Import EXTEND.

Module RGP. Section PROOFS.

  Context (is_glob : var -> bool).
  Context (fresh_id : glob_decls -> var -> Ident.ident).

  Notation venv := (Mvar.t global).

  Section FDS.

  Context (P:prog).

  Context (fds: fun_decls * seq (funname * seq leak_i_tr)).
  Notation gd := (p_globs P).
  (*Variable Fs: seq (funname * seq leak_i_tr).*)

  (** NEED TO FIX **)
  (*Hypothesis fds_ok : (mapM (remove_glob_fundef is_glob gd) (p_funcs P)) = ok fds.*)
  
 
  Hypothesis fds_ok : map_fnprog_leak (remove_glob_fundef is_glob gd) (p_funcs P) = ok fds.
  
  Hypothesis uniq_gd : uniq (map fst gd).
  Notation P' := {|p_globs := gd; p_funcs := fds.1|}.

  (*Hypothesis remove_glob_prog_ok : remove_glob_prog is_glob fresh_id P = ok (P', fds.2).*)

  Definition valid (m:venv) (s1 s2:estate) :=
    [/\ s1.(emem) = s2.(emem),
        (forall x, ~~is_glob x -> get_var (evm s1) x = get_var (evm s2) x),
        (forall x g, Mvar.get m x = Some g -> is_glob x) &
        (forall x g v,
           Mvar.get m x = Some g ->
           get_var (evm s1) x = ok v ->
           get_global gd g = ok v) ].

  Section REMOVE_GLOB_E.
    Context (m: venv) (ii: instr_info) (s1 s2: estate) (hvalid: valid m s1 s2).
    Variable stk: pointer.

    Let Pe e : Prop :=
      ∀ e' v le lte,
        remove_glob_e is_glob ii m e = ok (e', lte) →
        sem_pexpr gd s1 e = ok (v, le) →
        sem_pexpr gd s2 e' = ok (v, leak_E stk lte le).

    Let Pes es : Prop :=
      ∀ es' vs,
        mapM (remove_glob_e is_glob ii m) es = ok es' →
        sem_pexprs gd s1 es = ok vs →
        sem_pexprs gd s2 (unzip1 es') = ok (zip (unzip1 vs)
                                                (map2 (leak_E stk) (unzip2 es') (unzip2 vs))).

    Lemma remove_glob_e_esP : (∀ e, Pe e) ∧ (∀ es, Pes es).
    Proof.
      case: hvalid => hmem hm1 hm2 hm3.
      apply: pexprs_ind_pair; subst Pe Pes; split => //=.
      (* Base case *)
      - by move=> es' vs' [] <- [] <- /=.
      (* Inductive case *)
      - move=> e rec es recs. t_xrbindP. move=> es' vs' [ve lte] Hr vs'' Hes <- [ve' le'] He ves'' Hes' <- /=.
        move: (rec ve ve' le' lte Hr He). move=> -> /=.
        move: (recs vs'' ves'' Hes Hes'). by move=> -> /=.
      (* Pconst *)
      - by move=> z e v le lte [] <- <- [] <- <- /=.
      (* Pbool *)
      - by move=> b e v le lte [] <- <- [] <- <- /=.
      (* Parr_init *)
      - by move=> n e v le lte [] <- <- [] <- <- /=.
      (* Pget *)
      - move=> x e' v le lte. case: ifP => hx. case heq:(Mvar.get m x)=>[ g | // ] [<-].
        + move=> <- /=. t_xrbindP. move=> vg hg <- <- /=.
          move: (hm3 x g vg heq hg). by move=> -> /=.
        case => <- <-. t_xrbindP. rewrite /= -hm1 //. by move=> vg -> <- <- /=. 
        rewrite /is_true /= hx. auto.
      - move=> g e' v le lte [] <- <- /=. t_xrbindP. by move=> vg -> <- <- /=.            
      (* Pload *)            
      - move=> sz x e he q v; case: ifPn => // hx; t_xrbindP;
        move=> le lte [ve' lte'] he' <- <- /=. rewrite /= /on_arr_var.
        t_xrbindP. move=> [] /= vg //= a hg. t_xrbindP. move=> [ve1 lte1] he1.
        move=> z hi ws ha <- <- /=. move: (hm1 x hx). move=> <- /=. rewrite hg /=.
        move: (he ve' ve1 lte1 lte' he' he1). move=> -> /=. rewrite hi /=.
        by rewrite ha /=.
        move=> sz x e he e' v le lte. case: ifPn => // hx. t_xrbindP.
        move=> [ve' lte'] hre <- <- /=. move=> u v' hg hp' [ve1 lte1] he1 vp hp sz' hr <- <- /=.
        move: (he ve' ve1 lte1 lte' hre he1). move=> -> /=. move: (hm1 x hx). move=> h.
        rewrite -h /=. rewrite hg /=. rewrite hp' /=. rewrite hp /=. rewrite -hmem /=. by rewrite hr /=.
      (* Pop1 *)
      - move=> op1 e he. t_xrbindP. move=> h h0 le lte [ve lte'] hre <- <- [ve1 lte1] he' vo ho <- <- /=.
        move: (he ve ve1 lte1 lte' hre he'). move=> -> /=. by rewrite ho /=.
      (* Pop2 *)
      - move=> op2 e1 he1 e2 he2. t_xrbindP. move=> h h0 le1 lte1 [ve1 lte1'] hr1 [ve2 lte2] hr2 <- <-.
        move=> [vee1 ltee1] hee1 [vee2 ltee2] hee2 vo hop <- <- /=. move: (he1 ve1 vee1 ltee1 lte1' hr1 hee1).
        move=> -> /=. move: (he2 ve2 vee2 ltee2 lte2 hr2 hee2). move=> -> /=. by rewrite hop /=.
      (* PopN *)
      - move=> opN es hes e ve lte lte'. t_xrbindP. move=> ves hm <- <- ves' hm' vo ho <- <- /=. 
        rewrite /sem_pexprs in hes. move: (hes ves ves' hm hm'). move=> -> /=. rewrite unzip1_zip.
        rewrite ho /=. rewrite unzip2_zip. auto.
        rewrite map2E size_map size1_zip.
        + by rewrite !size_map -(mapM_size hm) -(mapM_size hm').
          by rewrite !size_map -(mapM_size hm) -(mapM_size hm').
        rewrite map2E size_map size1_zip. by rewrite !size_map -(mapM_size hm) -(mapM_size hm').
        by rewrite !size_map -(mapM_size hm) -(mapM_size hm').
      (* Pif *)
      - move=> ty e he e1 he1 e2 he2. t_xrbindP. move=> e' ve le lte [ve' le'] hre [ve1 le1] hre1 [ve2 le2] hre2 <- <- /=.
        move=> [v1 l1] hee b hb [v1' l1'] hee1 [v1'' l1''] hee2 vt ht vt' ht' <- <-.
        move: (he ve' v1 l1 le' hre hee). move=> -> /=. rewrite hb /=.
        move: (he1 ve1 v1' l1' le1 hre1 hee1). move=> -> /=.
        move: (he2 ve2 v1'' l1'' le2 hre2 hee2). move=> -> /=. rewrite ht /=.
        by rewrite ht' /=.
    Qed.


  End REMOVE_GLOB_E.
  
  Variable stk: pointer.
  Definition remove_glob_eP m ii s1 s2 e e' v h:=
    (@remove_glob_e_esP m ii s1 s2 h stk).1 e e' v.

  Definition remove_glob_esP m ii s1 s2 es es' vs h:=
    (@remove_glob_e_esP m ii s1 s2 h stk).2 es es' vs.

  Lemma write_var_remove (x:var_i) m s1 s2 v vm :
    ~~ is_glob x ->
    valid m s1 s2 ->
    set_var (evm s1) x v = ok vm ->
    exists s2' :
      estate, valid m {| emem := emem s1; evm := vm |} s2' /\ write_var x v s2 = ok s2'.
  Proof.

    rewrite /write_var /set_var => hglob hval; case:(hval) => hmem hm1 hm2 hm3.
    apply: on_vuP.
    + move=> ? -> <- /=;eexists;split;last reflexivity.
      split => //=.
      + move=> y hy; rewrite /get_var /= /on_vu.
        case: (v_var x =P y) => [<- | /eqP heq].
        + by rewrite !Fv.setP_eq.
        by rewrite !Fv.setP_neq //; apply (hm1 _ hy).
      move=> y g v0 hy.
      rewrite /get_var /on_vu Fv.setP_neq;first by apply: hm3 hy.
      by apply /eqP => ?;subst y; move: hglob; rewrite (hm2 _ _ hy).
    move=> ->; case:ifPn => // hx [<-] /=;eexists;split;last reflexivity.
    split => //=.
    + move=> y hy; rewrite /get_var /= /on_vu.
      case: (v_var x =P y) => [<- | /eqP heq].
      + by rewrite !Fv.setP_eq.
      by rewrite !Fv.setP_neq //; apply (hm1 _ hy).
    move=> y g v0 hy.
    rewrite /get_var /on_vu Fv.setP_neq;first by apply: hm3 hy.
    by apply /eqP => ?;subst y; move: hglob; rewrite (hm2 _ _ hy).
  Qed.

  Lemma remove_glob_lvP m ii s1 s1' s2 lv lv' v lte le:
    valid m s1 s2 ->
    remove_glob_lv is_glob ii m lv = ok (lv', lte) ->
    write_lval gd lv v s1 = ok (s1', le) ->
    exists s2',
      valid m s1' s2' /\ write_lval gd lv' v s2 = ok (s2', leak_E stk lte le).
  Proof.
    move=> hval; case:(hval) => hmem hm1 hm2 hm3. case:lv => [vi ty|x|ws x e|ws x e] /=.
    (* Lnone *)
    + move=> [<- <-]; rewrite /write_none. t_xrbindP. move=> s2' hu <- <- /=.
      move: hu. apply on_vuP. move=> ty' hv <- /=. exists s2. split=> //.
      rewrite /write_none. t_xrbindP. by rewrite hv /=. 
      rewrite /write_none. move=> hv. case: ifPn=> // ? [<-]. exists s2. split=> //.
      by rewrite hv /=.
    (* Lvar *)
    + case: ifPn=> // hg [<- <-]; rewrite /write_var. t_xrbindP.
      move=> s2' vm hs <- <- <- /=. move: write_var_remove. move=> hw.
      move: (hw x m s1 s2 v vm hg hval hs). move=> {hw} [] s2'' [] hval' -> /=.
      exists s2''. by split.
    (* Lmem *)
    + case: ifPn => hg //. t_xrbindP.
      move=> [ve' lte'] /(remove_glob_eP hval).
      move=> he <- <- u vg hg' hp [ve2 lte2] he' vp hp' sz hw m' hm <- <- /=.
      move: (hm1 _ hg). move=> <-. rewrite hg' /=. rewrite hp /=.
      move: (he ve2 lte2 he'). move=> -> /=. rewrite hp' /=.
      rewrite hw /=. rewrite -hmem. rewrite hm /=. by exists ({| emem := m'; evm := evm s2 |}).
    (* Laset *)                                                        
    case: ifPn => hg //. t_xrbindP.
    move=> [ve' lte'] /(remove_glob_eP hval) he <- <-.
    apply: on_arr_varP => ?? hty; rewrite (hm1 x hg) => hget. t_xrbindP.
    move=> [ve1 lte1] he' z hi sz hw a ha vm hs <- <- /=.
    move: (he ve1 lte1 he'). move=> -> /=. rewrite hi /=.
    rewrite hw /=. rewrite /on_arr_var /=. rewrite hget /=.
    rewrite ha /=. move: (write_var_remove hg hval hs). move=> [] s2' [] hvm hw'.
    exists s2'. split. auto. rewrite /write_var in hw'. move: hw'.
    t_xrbindP. by move=> vm' -> /= <-.
  Qed.
   
  Lemma remove_glob_lvsP  m ii s1 s1' s2 lv lv' v les:
    valid m s1 s2 ->
    mapM (remove_glob_lv is_glob ii m) lv = ok lv' ->
    write_lvals gd s1 lv v = ok (s1', les) ->
    exists s2',
      valid m s1' s2' /\
      write_lvals gd s2 (unzip1 lv') v = ok (s2', map2 (leak_E stk) (unzip2 lv') les).
  Proof.
    elim: lv lv' v s1 s2 s1' les => //=.
    + move=> lv' [] // s1 s2 s1' les hm [<-] [<-] <- /=.
      by exists s2.
    move=> x xs hrec lv' vs s1 s2 s1' les hval. t_xrbindP.
    move=> [ve lte] /(remove_glob_lvP hval) h1 xs' /hrec hms <-. 
    case: vs => // v vs. t_xrbindP. move=> [s3 lt3] hw [s4 lt4] hws <- <- /=.
    move: (h1 s3 v lt3 hw). move=> [] s3' [] hval' hw'.
    rewrite hw' /=. move: (hms vs s3 s3' s4 lt4 hval' hws).
    move=> [] s4' [] hval'' -> /=. exists s4'; auto.
  Qed.

  Let Pc s1 c lc s2 :=
    forall m m' c' ltc fn, remove_glob (remove_glob_i is_glob gd fn) m c = ok (m', c', ltc) ->
    forall s1', valid m s1 s1' ->
    leak_WFs (leak_Fun fds.2) ltc lc /\
    exists s2', valid m' s2 s2' /\
                sem P' s1' c' (leak_Is (leak_I (leak_Fun fds.2)) stk ltc lc) s2'.

  Let Pi s1 i li s2 :=
    forall m m' c' lti fn, remove_glob_i is_glob gd fn m i = ok (m', c', lti) ->
    forall s1', valid m s1 s1' ->
    leak_WF (leak_Fun fds.2) lti li /\
    exists s2', valid m' s2 s2' /\
                sem P' s1' c' (leak_I (leak_Fun fds.2) stk li lti) s2'.

  Let Pi_r s1 i li s2 := forall ii, Pi s1 (MkI ii i) li s2.

  Let Pfor xi vs s1 c lf s2 :=
    ~~is_glob xi.(v_var) ->
    forall m m' c' ltc' fn, remove_glob (remove_glob_i is_glob gd fn) m c = ok (m', c', ltc') ->
    Mincl m m' ->
    forall s1', valid m s1 s1' ->
    leak_WFss (leak_Fun fds.2) ltc' lf /\
    exists s2', valid m s2 s2' /\
                sem_for P' xi vs s1' c' (leak_Iss (leak_I (leak_Fun fds.2)) stk ltc' lf) s2'.

  Let Pfun m fn vs lf m' vs':=
      leak_WFs (leak_Fun fds.2) (leak_Fun fds.2 lf.1) lf.2 /\
      sem_call P' m fn vs (lf.1, (leak_Is (leak_I (leak_Fun fds.2)) stk (leak_Fun fds.2 lf.1) lf.2)) m' vs'.

  Local Lemma Hnil : sem_Ind_nil Pc.
  Proof.
    move=> s1 m m' c' ltc fn /= [<- <- <-] s1' hv. split=> //. 
    constructor. exists s1';split => //.
    econstructor.
  Qed.

  Local Lemma Hcons : sem_Ind_cons P Pc Pi.
  Proof.
    move=> s1 s2 s3 i c li lc hsi hi hsc hc m m' c' fn /=. t_xrbindP.
    move=> fn' [[mi ci] lti] /hi{hi}hi. t_xrbindP.
    move=> [[mc cc] ltc] /hc{hc}hc [] <- <- <- s1' hvm.
    move: (hi s1' hvm). move=> [] Hwf [] s2' [] hvm' {hi} hi.
    move: (hc s2' hvm'). move=> [] Hwf' [] s3' [] hvm'' {hc} hc.
    split=> //. constructor. apply Hwf. apply Hwf'.
    exists s3'; split => //=; apply sem_app with s2'; auto.
  Qed.

  Local Lemma HmkI : sem_Ind_mkI P Pi_r Pi.
  Proof. done. Qed.

  Lemma find_globP ii xi sz z g :
    find_glob ii xi gd sz z = ok g ->
    get_global gd g =  ok (Vword (wrepr sz z)).
  Proof.
    rewrite /find_glob /get_global /get_global_word /get_global_Z.
    elim: gd uniq_gd => //= -[g' z'] gd hrec /andP /= [hg' huniq]; case: ifPn => /= /andP.
    + by move=> [/eqP ? /eqP ? [?]] {hrec};subst; rewrite eq_refl.
    move=> hn /(hrec huniq) hget {hrec}.
    case: eqP => heq //; subst g'.
    case heq : assoc hget hg' => [z1 | //].
    by rewrite (assoc_mem_dom' heq).
  Qed.

  Local Lemma Hasgn : sem_Ind_assgn P Pi_r.
  Proof.
  move=> s1 s2 x tag ty e v v' le lw he hv hw ii m m' c' lti fn /= hrm s1' hval.
  move: hrm; t_xrbindP. move=> [e' lte'] /(remove_glob_eP hval) -/(_ _ _ he) he' /=.
  have :
      (Let rlv := remove_glob_lv is_glob ii m x
       in ok
            (m, [:: MkI ii (Cassgn rlv.1 tag ty e')],
             LT_ile (LT_map [::lte'; rlv.2])) = ok (m', c', lti) -> ∃ s2' : estate,
      valid m' s2 s2'
      ∧ sem P' s1' c' (*(leak_I (leak_Fun fds.2) stk (Lopn (LSub [:: le; le])) (LT_ile (LT_map [::lte'; rlv.2])))*)
          match lti with
          | LT_iremove => [::]
          | LT_ile lte0 => [:: Lopn (leak_E stk lte0 (LSub [:: le; lw]))]
          | _ => [::]
          end s2').
  + t_xrbindP. move=> [x' lte''] /(remove_glob_lvP hval) -/(_ _ _ _ hw) [] s2' [] hs2' hw' <- <- <-.
    exists s2'. split. auto. apply sem_seq1; econstructor; econstructor; eauto.
  case: x hw=> //=. 
  + move=> x xi /=; t_xrbindP=> y // Hw <- <- /= // H Hm Hc' Hlti.
    move: H. move=> []. repeat f_equal; auto. rewrite -Hlti /=. move=> s [Hvs] Hs. 
    split=> //.
  + constructor.
  exists s. split=> //.
  + move=> xi hxi hdef. case: ifPn => // hglob {hdef}.
    case: e' he' => // - [] // sz [] //= z [] hv' hl'; subst v.
    case: andP => //= -[/eqP ? /eqP htxi];subst ty.
    move: hv; rewrite /truncate_val /= truncate_word_u /= => -[?]; subst v'.
    move: xi htxi hglob hxi.
    rewrite /write_var /set_var => -[[xty xn] xii] /= ? hglob; subst xty.
    rewrite /pof_val /= sumbool_of_boolET => -[<-] hl'' /=.
    t_xrbindP => g hfind <- <- <-;split=>//. constructor. exists s1'; split=> //=.
    set x := {| vtype := _ |}.
    case: hval => hm hm1 hm2 hm3; split => //=.
    + move=> y hy; rewrite /get_var /on_vu.
      rewrite Fv.setP_neq; first by apply hm1.
      by apply /eqP => ?;subst y;move: hy;rewrite hglob.
    + by move=> y gy;rewrite Mvar.setP; case:eqP => [<- // | ?]; apply hm2.
      move=> y gy v;rewrite Mvar.setP;case:eqP => [<- | /eqP hneq].
    + move=> [<-]. rewrite /get_var Fv.setP_eq /= => -[<-].
      by apply: find_globP hfind.
    + by rewrite /get_var Fv.setP_neq //; apply hm3.
    constructor.
  + t_xrbindP. move=> -[lv ltv]. case: ifP=> // hglob'. 
    move: hxi. t_xrbindP. move=> y Hw <- <- /=. rewrite /write_var in Hw. move: Hw. t_xrbindP. move=> vm Hset hy /=.
    move: (write_var_remove). move=> Hg.
    move=> <- <- <- <- <- /=. move: (Hg xi m s1 s1' v' vm hglob hval Hset). move=> [] x [Hvm] Hw'.
    split. constructor.
    exists x. split=> //. rewrite hy in Hvm. auto.
    apply sem_seq1; econstructor; econstructor; eauto. rewrite /write_lval. by rewrite Hw' /=.
  + move=> sz vi ei /=. t_xrbindP=> u vu Hg hp -[v1 l1] he1 u' hp' w hw m1 /= hm <- <- /=.
    case: ifP=> //= hglob. t_xrbindP=> //= H -[lv ltv] -[l1' lt1] hr /= [] Hlv Hlt Hm Hc Hl /=. rewrite hr /= in H.
    move: H. move=> []. repeat f_equal; auto. by rewrite Hlv. rewrite -Hlt in Hl. auto. rewrite -Hm -Hc -Hl /=.
    move=> x [Hvm] Hs. split. constructor. exists x. split=> //.
  move=> sz vi ei. t_xrbindP=> //=. rewrite /on_arr_var. t_xrbindP=> vg hg h. case: ifP=> // hglob.
  t_xrbindP=> //= H -[lv ltv] -[l1' lt1] hr /= [] Hlv Hlt Hm Hc Hl /=. rewrite hr /= in H.
  move: H. move=> []. repeat f_equal; auto. by rewrite Hlv. rewrite -Hlt in Hl. auto. rewrite -Hm -Hc -Hl /=.
  move=> x [Hvm] Hs. split. constructor. exists x. split=> //.
Qed.
  
  Local Lemma Hopn : sem_Ind_opn P Pi_r.
  Proof.
   move=> s1 s2 t o xs es lo ho ii m m' c lti fn /= hrm s1' hval.
   move: hrm. t_xrbindP. move=> xs' /(remove_glob_lvsP hval) hxs' es' hes_es'.
   move: (hes_es') => /(remove_glob_esP hval) hes' <- <- <-.
   move: ho; rewrite /sem_sopn; t_xrbindP. move=> vs hes_vs. 
   move: (hes_vs) => /hes' h1 vs' h2 [s3 lt3] /hxs' [s2' [hval' h]] <- <-.
   split. + constructor.
   exists s2'. split=> //.
   apply sem_seq1; constructor; constructor.
   have heq : size (unzip1 vs) = size (map2 (leak_E stk) (unzip2 es') (unzip2 vs)).
   + rewrite map2E !(size_map, size_zip).
     have <- := mapM_size hes_es'; have -> := mapM_size hes_vs.
     by rewrite minnn.
   rewrite /sem_sopn h1 /= unzip1_zip /=; last by rewrite heq.
   by rewrite h2 /= h /= unzip2_zip /= ?heq.
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
    move=> hincl [hmem hm1 hm2 hm3];split => //.
    + by move=> x g /(MinclP hincl) -/hm2.
    by move=> x g v /(MinclP hincl); apply hm3.
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

  Local Lemma Hif_true : sem_Ind_if_true P Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc he hsc hc ii m m' c' lti fn /= hrm s1' hval.
    move: hrm; t_xrbindP. move=> [e' lte'] /(remove_glob_eP hval) -/(_ _ _ he) he' /=.
    move=> [[m1 c1'] lt1] /hc -/(_ _ hval) [Hwf [s2' [hval' hc1']]]. t_xrbindP.
    move=> [[m2 c2'] lt2] h /= [] <- <- <- /=. split. constructor. apply Hwf.
    exists s2'; split.
    + apply: valid_Mincl hval'; apply merge_incl_l.
    apply sem_seq1. apply EmkI. apply Eif_true.
    replace gd with (p_globs P') in he'. auto. by simpl. auto.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false P Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 le lc he hsc hc ii m m' c' lti fn /= hrm s1' hval.
    move: hrm; t_xrbindP. move=> [e' lte'] /(remove_glob_eP hval) -/(_ _ _ he) he'.
    move=> [[m1 c1'] lt1] h /=. t_xrbindP.
    move=> [[m2 c2'] lt2] /hc -/(_ _ hval) [Hwf [s2' [hval' hc1']]] [] <- <- <- /=.
    split. constructor. apply Hwf.
    exists s2'; split.
    + apply: valid_Mincl hval'. apply merge_incl_r.
    apply sem_seq1. apply EmkI. apply Eif_false.
    replace gd with (p_globs P') in he'. auto. by simpl. auto.
  Qed.  

  Lemma MinclR m : Mincl m m.
  Proof. by apply /allP => -[x g] /Mvar.elementsP ->. Qed.

  Lemma MinclT m2 m1 m3: Mincl m1 m2 -> Mincl m2 m3 -> Mincl m1 m3.
  Proof.
    move=> /allP h1 /allP h2; apply /allP => x /h1.
    case heq : (Mvar.get m2 x.1) => [g|//] /eqP ?; subst g.
    by apply h2; apply /Mvar.elementsP.
  Qed.


  Lemma loop2P fn check_c2 n m e c1 c2 m1 (ltc: leak_c_tr) (lte: leak_e_tr) (ltc': leak_c_tr):
    loop2 fn check_c2 n m = ok (Loop2_r e c1 c2 (m1, (ltc, lte, ltc'))) ->
    exists m2 m3,
      [/\ check_c2 m3 = ok (Check2_r e (m1,c1) (m2,c2, (ltc, lte, ltc'))), Mincl m3 m2 & Mincl m3 m].
  Proof.
    elim: n m => //= n hrec m; t_xrbindP.
    move=> [e' [m1' c1'] [[m2' c2'] [[lt1 lt2] lt3]]] heq; case:ifPn => hincl.
    + move=> [] <- <- <- <- <- <- <- /=.
      by exists m2', m; split => //; apply MinclR.
    move=> /hrec [m2 [m3 [h1 h2]]] hm3; exists m2, m3; split=>//.
    apply: (MinclT hm3); apply merge_incl_l.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true P Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c e c' lc le lc' li hsc hc he hsc' hc' hsw hw ii m m' c'0 lti fn
              /= hrn s1' hval. move: hrn. t_xrbindP.
    move=> -[e' c1' c2' [m1 [[ltc lte] ltc']]] /loop2P [m2 [m3 []]].
    t_xrbindP. move=> -[[m4 c4] ltc4] h1 /=. t_xrbindP.
    move=> [e1 lte1] he1 [[m5 c5] ltc5] h2 [] <- <- <- <- <- <- <- <- /=.
    have h1' := hc _ _ _ _ _ h1. have h2' := hc' _ _ _ _ _ h2.
    move=> hm hm1 <- <- <-.
    have /h1' [Hwf [s2' [hs2 hc1]]]: valid m3 s1 s1' by apply: valid_Mincl hval.
    move: (h2' s2' hs2). move=> [] Hwf'. 
    have he' := remove_glob_eP hs2 he1 he. have [Hwf'' [s3' [hs3 hc2]]]:= h2' _ hs2.
    have : remove_glob_i is_glob gd fn m3 (MkI ii (Cwhile a c e c')) =
           ok (m4, [::MkI ii (Cwhile a c4 e1 c5)], (LT_iwhile ltc4 lte1 ltc5)).
    + by rewrite /= Loop.nbP /= h1 /= he1 /= h2 /= hm /=.
    move=> /hw{hw}hw; have /hw : valid m3 s3 s3' by apply: (valid_Mincl hm).
    move=> [Hwf''' [s4' [hs4 hw']]]. move=> h. split.
    constructor. apply Hwf. apply Hwf'. apply Hwf'''.
    exists s4';split => //.
    apply sem_seq1; constructor; apply: Ewhile_true;eauto.
    by case/semE: hw' => s [] lk [] _ [] /sem_IE hw' /semE[] -> -> -> /=.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false P Pc Pi_r.
  Proof.
    move=> s1 s2 a c e c' lc le hsc hc he ii m m' c'0 lti fn /= hrn s1' hval.
    move: hrn; t_xrbindP. move=> -[e' c1' c2' [m1 [[ltc lte] ltc']]] /loop2P [m2 [m3 []]].
    t_xrbindP. move=> -[[m4 c4] ltc4] h1 /=. t_xrbindP.
    move=> [e1 lte1] he1 [[m5 c5] ltc5] h2 [] <- <- <- <- <- <- <- <- /=.
    move=> hm hm1 <- <- <-.
    have h1' := hc _ _ _ _ _ h1.
    have /h1' [Hwf [s2' [hs2 hc1]]]: valid m3 s1 s1' by apply: valid_Mincl hval.
    split. constructor. apply Hwf.
    exists s2';split => //.
    apply sem_seq1;constructor;apply: Ewhile_false => //.
    move: remove_glob_eP. move=> H. by move: (H m4 ii s2 s2' e e1 false hs2 le lte1 he1 he).
  Qed.

  Local Lemma loopP fn check_c n m m' c' ltc':
    loop fn check_c n m = ok (m', c', ltc') ->
      exists m1,
      [/\ check_c m' = ok (m1,c',ltc'), Mincl m' m1 & Mincl m' m].
  Proof.
    elim: n m => //= n hrec m; t_xrbindP. move=> -[[m2 c2] ltc2] /= hc.
    case:ifP => hincl.
    + move=> [<- <- <-]; exists m2; split=> //; apply MinclR.
    move=> /hrec=> -[m1 [hc' h1 h2]]. exists m1; split=> //.
    apply: (MinclT h2); apply merge_incl_l.
  Qed.

  Local Lemma Hfor : sem_Ind_for P Pi_r Pfor.
  Proof.
    move=> s1 s2 i r wr c li lr hr hsfor hfor ii m m' c' lti fn /=.
    rewrite /sem_range in hr. move: hr. case: r => [[d e1] e2].
    t_xrbindP. move=> [ve1 le1] he1 vi hi [ve2 le2] he2 vi'
                                hi' hwr <- h s1' hval. move: h.
    case: ifPn => // hglob.
    t_xrbindP. move=> [e le] /(remove_glob_eP hval) he.
    move=> [e' le'] /(remove_glob_eP hval) he'.
    move=> [[m2 c2] ltc2] /= /loopP [m1 [hc h1 h2]] [<- <- <-].
    have hval': valid m2 s1 s1'. by apply: valid_Mincl hval.
    rewrite /Pfor in hfor. move: (hfor hglob m2 m1 c2 ltc2 fn hc h1 s1' hval').
    move=> [] Hwf [] s2' [] hval'' {hfor} hfor. split. constructor. apply Hwf.
    exists s2'; split=> //.
    apply sem_seq1; constructor; econstructor.
    rewrite /sem_range. move: (he ve1 le1 he1). replace gd with (p_globs P').
    move=> -> /=. rewrite hi /=. move: (he' ve2 le2 he2). move=> -> /=.
    rewrite hi' /=. auto. by simpl. rewrite -hwr in hfor. auto.
  Qed.  

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof.
    move=> s xi c ii m m' c' ltc' fn hrm hincl s1' hval. split. constructor. 
    exists s1';split => //; constructor.
  Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P Pc Pfor.
  Proof.
    move=> s1 s2 s3 s4 xi w ws c lc lf hw hsc hc hsfor hfor hglob m m' c' ltc' fn hrm hincl s1' hval.
    move: hw; rewrite /write_var; t_xrbindP => vm hvm ?;subst s2.
    have [s2' [hs2' ws2']]:= write_var_remove hglob hval hvm.
    have [Hwf [s3' [hs3' ws3']]]:= hc _ _ _ _ _ hrm _ hs2'.
    have hval' := valid_Mincl hincl hs3'.
    have [Hwf' [s4' [hs4' ws4']]]:= hfor hglob _ _ _ _ _ hrm hincl _ hval'.
    split. constructor. apply Hwf. apply Hwf'.
    exists s4'; split => //; econstructor; eauto.
  Qed.

  Local Lemma Hcall : sem_Ind_call P Pi_r Pfun.
  Proof.
    move=> s1 m2 s2 fii cs fn args vargs rvs lf lw hargs hcall hfun hres ii m m' c' lti fn0 /= hrm s1' hval.
    case hlf: lf=> [fn' lfn].
    move: hrm. t_xrbindP. move=> xs' hxs es' hes <- <- <-.
    have hes' := remove_glob_esP hval hes hargs.
    have hval' : valid m {| emem := m2; evm := evm s1 |} {| emem := m2; evm := evm s1' |}.
    + by case: hval=> hm hm1 hm2 hm3; split.
    have [s2' [hs2' hxs']]:= remove_glob_lvsP hval' hxs hres.
    split. apply sem_eq_fn in hcall. rewrite hlf /= in hcall. rewrite hcall. constructor.
    rewrite /Pfun in hfun. move: hfun. move=>[] Hwf hfun. rewrite hlf /= in Hwf. 
    rewrite hcall in Hwf. apply Hwf.
    exists s2'; split=> //.
    apply sem_seq1;constructor.
    rewrite /=. move: Ecall.
    move=> H. rewrite hlf in hfun. rewrite /Pfun in hfun. rewrite /= in hfun.
    replace gd with (p_globs P') in hes'.
    rewrite /valid in hval. move: hval. move=> [] h1 h2 h3 h4. rewrite h1 in hfun.
    move: hfun. move=> [] Hwf hfun.
    replace (unzip1 vargs) with (unzip1 (zip (unzip1 vargs) (map2 (leak_E stk) (unzip2 es') (unzip2 vargs)))) in hfun.
    move: (H P' s1' m2 s2' fii (unzip1 xs') fn (unzip1 es')  (zip (unzip1 vargs) (map2 (leak_E stk) (unzip2 es') (unzip2 vargs))) rvs 
             (fn', leak_Is (leak_I (leak_Fun fds.2)) stk (leak_Fun fds.2 fn') lfn) (map2 (leak_E stk) (unzip2 xs') lw) hes' hfun hxs'). 
    move=> hi. rewrite unzip2_zip in hi. auto.
    + rewrite map2E size_map size2_zip !size_map. auto. rewrite /sem_pexprs in hes'. rewrite /sem_pexprs in hargs.
      move: (mapM_size hes'). move: (mapM_size hargs). move: (mapM_size hes). move=> H1 H2 H3.
      rewrite H1 in H2. rewrite H2. auto. rewrite unzip1_zip. auto. rewrite map2E size_map size2_zip !size_map. auto.
      move: (mapM_size hes'). move: (mapM_size hargs). move: (mapM_size hes). move=> H1 H2 H3.
      rewrite H1 in H2. rewrite H2; auto. auto.
    Qed.

  Local Lemma get_fundefP fn f:
    get_fundef (p_funcs P) fn = Some f ->
    exists f', exists ltc, 
       get_fundef (p_funcs P') fn = Some f' /\
       get_leak fds.2 fn = Some ltc /\
       remove_glob_fundef is_glob gd (fn,f) = ok (f', ltc).
  Proof.
    change (p_funcs P') with fds.1.
    elim: (p_funcs P) fds fds_ok => //=.
    move=> fd1 fds1 hrec fds'.
    rewrite /map_fnprog_leak /= -/(map_fnprog_leak _ _).
    apply: rbindP. move=> fdlts.
    apply: rbindP. move=> fdlts'.
    apply: rbindP. move=> [fd' ltc'] Hpl' [] <- /=. t_xrbindP.
    move=> fdlts'' Hm <- <-.
    case heq: fd1=> [fd11 fd12]. case: ifP.
    + move=> /eqP -> /=.
      move=> [] <- /=.
      exists fd'. exists ltc'.
      case: ifP. split=> //. split=> //. rewrite /eqP /=. 
      move: Hpl'.
      t_xrbindP. rewrite heq /=. move=> y -> /= y' -> /= [[m' c'] ltc''] hrm [] <- <- /=.
      by rewrite hrm /=.
   + move=> /eqP /= []; auto.
   + move=> H Hf. rewrite /map_fnprog_leak in hrec.
     rewrite Hm in hrec. rewrite /= in hrec. rewrite /=.
     rewrite H /=. move: (hrec ([seq (t.1, t.2.1) | t <- fdlts''], [seq (t.1, t.2.2) | t <- fdlts''])). move=> {hrec} hrec; auto.
  Qed.

  Local Lemma Hproc : sem_Ind_proc P Pc Pfun.
  Proof.
    move=> m1 m2 fn f vargs vargs' s1 vm2 vres vres' lc hget hargs hwa _ hc hres hres'.
    rewrite /Pfun. move: get_fundefP. move=> Hg.
    move: (Hg fn f hget). move=> [] fd' [] ltc' [] hget' [] hfs.
    rewrite /remove_glob_fundef; t_xrbindP.
    move=> y hparams res1 hres1 [[m' c'] ltc''] hrm [] hfd' hl.
    have hval: valid (Mvar.empty global) s1 s1 by split.
    rewrite /Pc in hc. move: (hc (Mvar.empty global) m' c' ltc'' fn hrm s1 hval).
    move=> [Hwf [[mem2 vm2'] [hs2' ws2]]]. case: (hs2')=> /= hmem hm x g; subst mem2.
    have hres2 : mapM (fun x : var_i => get_var vm2' x) (f_res f) = ok vres.
    + elim: (f_res f) (vres) res1 hres1 hres => //= x' xs hrec vres0 res1.
      t_xrbindP => ?; case: ifPn => hglob // [<-] ? /hrec hres1 ? v hx vs /hres1 hxs ?.
      by subst res1 vres0; rewrite -hm //= hx /= hxs.
    econstructor; eauto. rewrite /get_leak in hfs. rewrite /leak_Fun /=. 
    rewrite hfs /=. rewrite -hl. apply Hwf. 
    econstructor; eauto. rewrite -hfd'. rewrite /=. apply hargs. rewrite -hfd' /=. apply hwa.
    rewrite -hfd' /=. rewrite /= in hfs. rewrite /get_leak in hfs. replace (leak_Fun fds.2 fn) with ltc''.
    apply ws2. rewrite /leak_Fun /=. by rewrite hfs /=.
    rewrite -hfd' /=. apply hres2. rewrite -hfd' /=. apply hres'.
  Qed.


  Local Lemma remove_glob_call m1 f vargs m2 vres lf:
    sem_call P m1 f vargs lf m2 vres ->
    Pfun m1 f vargs lf m2 vres.
  Proof.
     apply /(@sem_call_Ind P Pc Pi_r Pi Pfor Pfun Hnil Hcons HmkI Hasgn Hopn Hif_true Hif_false
                             Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.

  End FDS.

  Lemma remove_globP P P' f mem mem' va vr lf lft stk:
    remove_glob_prog is_glob fresh_id P = ok (P', lft) ->
    sem_call P mem f va (f, lf) mem' vr ->
    leak_WFs (leak_Fun lft) (leak_Fun lft f) lf /\
    sem_call P' mem f va (f, (leak_Is (leak_I (leak_Fun lft)) stk (leak_Fun lft f) lf)) mem' vr.
  Proof. 
    rewrite /remove_glob_prog; t_xrbindP=> gd' /extend_glob_progP hgd.
    case: ifP=> // huniq; t_xrbindP=> fds hfds <- <- /(gd_incl_fun hgd) hf.
    apply (remove_glob_call (P:={| p_globs := gd'; p_funcs := p_funcs P |}) hfds huniq stk hf).
  Qed.

End PROOFS. End RGP.
