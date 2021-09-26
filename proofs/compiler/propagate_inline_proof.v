(* ** License
 * -----------------------------------------------------------------------
 * Copyright 2016--2017 IMDEA Software Institute
 * Copyright 2016--2017 Inria
 *
 * Permission is hereby granted, free of charge, to any person obtaining
 * a copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
 * IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
 * CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
 * TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
 * SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 * ----------------------------------------------------------------------- *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import psem constant_prop constant_prop_proof.
Require Export propagate_inline.

Import Utf8 ZArith Morphisms Classes.RelationClasses.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope seq_scope.
Local Open Scope vmap_scope.

(* ** proofs
 * -------------------------------------------------------------------- *)

Section Section.

Context {T:eqType} {pT:progT T} {sCP: semCallParams}.

(*
Section EqRead.

Lemma eq_gvar_read x1 x2 : eq_gvar x1 x2 -> read_gvar x1 = read_gvar x2.
Proof. by rewrite /eq_gvar /read_gvar /is_lvar => /andP [] /eqP -> /eqP ->. Qed.

Let P e1 : Prop := forall e2 s, eq_expr e1 e2 -> read_e_rec s e1 = read_e_rec s e2.
Let Q es1 : Prop := 
  forall es2 s,  seq.all2 eq_expr es1 es2 -> foldl read_e_rec s es1 = foldl read_e_rec s es2.

Lemma eq_expr_read_e_rec : (∀ e, P e) ∧ (∀ es, Q es).
Proof.
  apply: pexprs_ind_pair; subst P Q; split => /=.
  + by case.
  + by move=> e1 hrec1 es1 hrec1s [] // e2 es2 s /andP[] /hrec1-> /hrec1s->.
  1-3: by move=> ? []. 
  + by move=> x1 [] //= x2 s /eq_gvar_read->.
  + by move=> ?? x1 e1 hrec [] //= ?? x2 e2 s /andP[]/andP[]/andP[] _ _ /eq_gvar_read-> /hrec->. 
  + by move=> ????? hrec [] //= ????? s /andP[]/andP[]/andP[]/andP[] _ _ _ /eq_gvar_read-> /hrec->.
  + by move=> ? x1 e1 hrec [] //= ? x2 e2 s /andP[]/andP[] _ /eqP-> /hrec->.
  + by move=> ? e1 hrec [] //= ? e2 s /andP[] _ /hrec->.
  + by move=> ? e1 hrec1 e2 hrec2 [] //= ???? /andP[]/andP[] _ /hrec1-> /hrec2->.
  + by move=> ?? hrec [] //= ??? /andP[] _ /hrec->.
  by move=> ?? hrec ? hrec1 ? hrec2 []//= ????? /andP[]/andP[]/andP[] _ /hrec-> /hrec1-> /hrec2->.
Qed.

Lemma eq_expr_read_e e1 e2 : eq_expr e1 e2 -> read_e e1 = read_e e2.
Proof. case: eq_expr_read_e_rec => h _; apply: h. Qed.

End EqRead.

Section EqUse.

Let P e1 : Prop := forall e2, eq_expr e1 e2 -> use_mem e1 = use_mem e2.
Let Q es1 : Prop := 
  forall es2,  seq.all2 eq_expr es1 es2 -> has use_mem es1 = has use_mem es2.

Lemma eq_expr_use_mem_rec : (∀ e, P e) ∧ (∀ es, Q es).
Proof.
  apply: pexprs_ind_pair; subst P Q; split => /=.
  + by case.
  + by move=> e1 hrec1 es1 hrec1s [] // e2 es2 /andP[] /hrec1-> /hrec1s->.
  1-4: by move=> ? []. 
  + by move=> ?? x1 e1 hrec [] //= ?? x2 e2 /andP[]/andP[]/andP[] _ _ _ /hrec->. 
  + by move=> ????? hrec [] //= ????? /andP[]/andP[]/andP[]/andP[] _ _ _ _ /hrec->.
  + by move=> ? x1 e1 hrec [] //= ? x2 e2 /andP[]/andP[] _ /eqP-> /hrec->.
  + by move=> ? e1 hrec [] //= ? e2 /andP[] _ /hrec->.
  + by move=> ? e1 hrec1 e2 hrec2 [] //= ??? /andP[]/andP[] _ /hrec1-> /hrec2->.
  + by move=> ?? hrec [] //= ?? /andP[] _ /hrec->.
  by move=> ?? hrec ? hrec1 ? hrec2 []//= ???? /andP[]/andP[]/andP[] _ /hrec-> /hrec1-> /hrec2->.
Qed.

Lemma eq_expr_use_mem e1 e2 : eq_expr e1 e2 -> use_mem e1 = use_mem e2.
Proof. case: eq_expr_use_mem_rec => h _; apply: h. Qed.

End EqUse.
*)

Definition wf_pimap (pi:pimap) := 
  forall x c,
    Mvar.get pi x = Some c -> 
    c.(pi_fv) = read_e c.(pi_def) /\ 
    c.(pi_m) = use_mem c.(pi_def).

Lemma wf_piempty : wf_pimap piempty.
Proof. by move=> ? //. Qed.

Definition dfl_cel := {| pi_def := Pconst 0; pi_fv := Sv.empty; pi_m := false |}.

Lemma removeP pi x y :
  wf_pimap pi -> 
  Mvar.get (remove pi x) y = 
    if (x == y) || Sv.mem x (odflt dfl_cel (Mvar.get pi y)).(pi_fv) then None 
    else Mvar.get pi y.
Proof. 
  rewrite /remove /= => hwf; rewrite Mvar.filter_mapP.
  by case: eqP => //=; case heqy: Mvar.get. 
Qed.

Lemma wf_remove pi x : wf_pimap pi -> wf_pimap (remove pi x).
Proof. by move=> hwf y efv; rewrite removeP //; case: ifP => // _; apply hwf. Qed.

Lemma remove_mP pi y :
  wf_pimap pi -> 
  Mvar.get (remove_m pi) y = 
    if (odflt dfl_cel (Mvar.get pi y)).(pi_m) then None 
    else Mvar.get pi y.
Proof. 
  rewrite /remove_m /= => hwf; rewrite Mvar.filter_mapP.
  by case heqy: Mvar.get. 
Qed.

Lemma wf_remove_m pi : wf_pimap pi -> wf_pimap (remove_m pi).
Proof. by move=> hwf y efv; rewrite remove_mP //; case: ifP => // _; apply hwf. Qed.

Lemma setP pi x e y :
  Mvar.get (set pi x e) y = 
    if x == y then 
      Some {| pi_def := e; pi_fv := read_e e; pi_m := use_mem e |} 
    else Mvar.get pi y.
Proof. by rewrite /set /= Mvar.setP. Qed.

Lemma wf_set pi x e : wf_pimap pi -> wf_pimap (set pi x e).
Proof. by move => hwf y efv; rewrite setP; case: eqP => [ _ [<-]| _ /hwf]. Qed.

Lemma mergeP pi1 pi2 x : 
  Mvar.get (merge pi1 pi2) x = 
    match Mvar.get pi1 x, Mvar.get pi2 x with
    | Some c1, Some c2 => 
      if eq_expr c1.(pi_def) c2.(pi_def) then Mvar.get pi1 x
      else None
    | _, _ => None
    end.
Proof. by rewrite /merge Mvar.map2P. Qed.

Lemma wf_merge pi1 pi2 : wf_pimap pi1 -> wf_pimap pi2 -> wf_pimap (merge pi1 pi2).
Proof.
  move=> hwf1 hwf2 x efv; rewrite mergeP.
  case heq1 : Mvar.get => [ c1 | // ]; case heq2 : Mvar.get => [ c2 | // ].
  case: ifP => // _ [<-]; apply: hwf1 heq1.
Qed.

Lemma incl_merge_l pi1 pi2 : incl (merge pi1 pi2) pi1.
Proof.
  rewrite /incl Mvar.inclP /= => x; rewrite mergeP.
  case: Mvar.get => // c1; case: Mvar.get => // c2.
  by case: ifP => //= _; apply eq_expr_refl.
Qed.

Lemma incl_merge_r pi1 pi2 : incl (merge pi1 pi2) pi2.
Proof.
  rewrite /incl Mvar.inclP /= => x; rewrite mergeP.
  case: Mvar.get => // c1; case: Mvar.get => // c2.
  by case: ifP => //= _; apply eq_expr_refl.
Qed.

Section Global.
Context (gd: glob_decls).

Definition valid_pi (s: estate) (pi:pimap) :=
  forall x c v, 
    Mvar.get pi x = Some c -> 
    get_var (evm s) x = ok v -> 
    sem_pexpr gd s c.(pi_def) = ok v. 

Section Expr.

Context (s:estate) (pi:pimap) (hwf: wf_pimap pi) (hvalid: valid_pi s pi).

Let P e : Prop := 
  forall v, sem_pexpr gd s e = ok v -> sem_pexpr gd s (pi_e pi e) = ok v.

Let Q es : Prop := 
  forall vs, sem_pexprs gd s es = ok vs -> sem_pexprs gd s (pi_es pi es) = ok vs.

Lemma snotE e b: 
  sem_pexpr gd s e = ok (Vbool b) ->
  sem_pexpr gd s (snot e) = ok (Vbool (~~ b)).
Proof.
  move=> he; have /snotP : sem_pexpr gd s (Papp1 Onot e) = ok (Vbool (~~b)).
  + by rewrite /= he.
  by move=> [v] [->] /value_uincl_bool1 ->.
Qed.

Lemma sbeqE e1 e2 b : 
  sem_pexpr gd s (Papp2 Obeq e1 e2) = ok (Vbool b) ->
  sem_pexpr gd s (sbeq e1 e2) = ok (Vbool b).
Proof. by move=> /sbeqP [v] [-> /value_uincl_bool1 ->]. Qed.

Lemma sorE e1 e2 b1 b2 : 
  sem_pexpr gd s e1 = ok (Vbool b1) ->
  sem_pexpr gd s e2 = ok (Vbool b2) ->
  sem_pexpr gd s (sor e1 e2) = ok (Vbool (b1 || b2)).
Proof. 
  move=> h1 h2; have : sem_pexpr gd s (Papp2 Oor e1 e2) = ok (Vbool (b1 || b2)).
  + by rewrite /= h1 h2.
  by move=> /sorP [v] [-> /value_uincl_bool1 ->]. 
Qed.

Lemma sandE e1 e2 b1 b2 : 
  sem_pexpr gd s e1 = ok (Vbool b1) ->
  sem_pexpr gd s e2 = ok (Vbool b2) ->
  sem_pexpr gd s (sand e1 e2) = ok (Vbool (b1 && b2)).
Proof. 
  move=> h1 h2; have : sem_pexpr gd s (Papp2 Oand e1 e2) = ok (Vbool (b1 && b2)).
  + by rewrite /= h1 h2.
  by move=> /sandP [v] [-> /value_uincl_bool1 ->]. 
Qed.

Lemma scfcP c es vs v: 
  sem_pexprs gd s es = ok vs → 
  sem_opN (Ocombine_flags c) vs = ok v → 
  sem_pexpr gd s (scfc c es) = ok v.
Proof.
  rewrite /scfc /lower_cfc.
  case heq : cf_tbl => [n cfc] /=.
  case: es => /= [ [<-] // | oe es].
  t_xrbindP => ov hov ? h <-.
  case: es h => /= [ [<-] | ce es]; first by rewrite hov.
  t_xrbindP => cv hcv ? h <-.
  case: es h => /= [ [<-] | se es]; first by rewrite hov hcv.
  t_xrbindP => sv hsv ? h <-.
  case: es h => /= [ [<-] | ze es]; first by rewrite hov hcv hsv.
  t_xrbindP => zv hzv ? h <-.
  case: es h => /= [ [<-] /= | ??]; last first.
  + by t_xrbindP => ???? <-; rewrite /sem_opN /=; t_xrbindP.
  rewrite /sem_opN /=.
  t_xrbindP => b ob /to_boolI hob cb /to_boolI hcb sb /to_boolI hsb zb /to_boolI hzb hs <-.
  subst ov cv sv zv.
  move: hs; rewrite /sem_combine_flags heq /= /sem_cfc /neg_f => -[<-].
  set E := (X in snot X).
  set B := (B in ~~ B).
  have : sem_pexpr gd s E = ok (Vbool B).
  + rewrite /E /B; case: (cfc) => //.
    + by apply /snotE /sbeqE; rewrite /= hov hsv.
    + by apply/sorE.
    by apply/sorE => //; apply /snotE /sbeqE; rewrite /= hov hsv.
  by move=> h; case: (n) => //; apply /snotE.
Qed.

Lemma pi_eP_and : (forall e, P e) /\ (forall es, Q es).
Proof. 
  apply: pexprs_ind_pair; subst P Q; split => //=.  
  + by move=> e hrec es hrecs vs; t_xrbindP => ? /hrec-> ? /hrecs-> <-.
  + move=> x v; case: ifP => h //=.
    move=> hg; case heq : Mvar.get => [[e' fv m] | //].
    by move: hg; rewrite /get_gvar h => /(hvalid heq) /=.
  + move=> ?? x e hrec v; apply:on_arr_gvarP; rewrite /on_arr_var => n t ? -> /=.
    by t_xrbindP => i vi /hrec->/= ->/= ? -> <-.
  + move=> ??? x e hrec v; apply:on_arr_gvarP; rewrite /on_arr_var => n t ? -> /=.
    by t_xrbindP => ?? /hrec-> /= ->/= ? -> <-.
  + by move=> ??? hrec ?; t_xrbindP => ?? ->/= ->/= ?? /hrec->/= ->/= ? -> <-.
  + by move=> ?? hrec ?; t_xrbindP => ? /hrec->.
  + by move=> ?? hrec1 ? hrec2 v; t_xrbindP => ? /hrec1-> /= ? /hrec2->.
  + move=> o es hrec ?; t_xrbindP => ? /hrec.
    case: o => [wz pe | c] /=.
    + by rewrite /sem_pexprs => ->.
    by rewrite -/(pi_es pi es); apply scfcP.
  move=> ?? hrec ? hrec1 ? hrec2 v; t_xrbindP.
  by move=> ?? /hrec-> /= -> /= ?? /hrec1 -> /= -> /= ?? /hrec2 -> /= -> <-.
Qed.

Lemma pi_eP e v :
  sem_pexpr gd s e = ok v -> sem_pexpr gd s (pi_e pi e) = ok v.
Proof. case: pi_eP_and => h _; apply h. Qed.

Lemma pi_esP es vs : 
  sem_pexprs gd s es = ok vs -> sem_pexprs gd s (pi_es pi es) = ok vs.
Proof. case: pi_eP_and => _ h; apply h. Qed.

End Expr.

Lemma valid_set_var pi s x v vm : 
  wf_pimap pi -> 
  set_var (evm s) x v = ok vm -> valid_pi s pi -> valid_pi (with_vm s vm) (remove pi x).
Proof.
  move=> hwf hset hvalid y efv v' /=.
  rewrite removeP //; case: eqP => //=.
  case: Sv_memP => // hnin /eqP hne h hg.
  rewrite h /= in hnin.
  move: hg; have /= -> := (get_var_set_var y hset).
  rewrite (negbTE hne) => hg.
  have <- := hvalid _ _ _ h hg.
  apply eq_on_sem_pexpr => //=.
  move=> z hz; have hnez : x != z.
  + by apply/eqP => ?; subst z; apply hnin; have [-> _] := hwf _ _ h.
  by apply:set_varP hset => w hw <-; rewrite Fv.setP_neq.
Qed.

Section UseMem.

Context (s1 s2 : estate) (heq : evm s1 = evm s2).

Lemma use_memP e: 
  ~~use_mem e -> 
  sem_pexpr gd s1 e = sem_pexpr gd s2 e.
Proof.
  apply (pexpr_mut_ind (P := fun e => ~~use_mem e -> sem_pexpr gd s1 e = sem_pexpr gd s2 e)
                      (Q := fun e => ~~has use_mem e -> sem_pexprs gd s1 e = sem_pexprs gd s2 e)).
  split => //= {e}.
  + by move=> e hrec es hrecs; rewrite negb_or => /andP [] /hrec -> /hrecs ->. 
  + by move=> x _; rewrite heq.
  + by move=> ?? x e hrec /hrec ->; rewrite heq.
  + by move=> ??? x e hrec /hrec ->; rewrite heq.
  + by move=> ? e hrec /hrec ->.
  + by move=> ? e1 hrec1 e2 hrec2; rewrite negb_or => /andP[] /hrec1 -> /hrec2 ->.
  + by move=> ? es; rewrite /sem_pexprs => h/h->.
  by move=> ty e he e1 he1 e2 he2; rewrite !negb_or=> /andP[]/andP[] /he-> /he1-> /he2->.
Qed.

End UseMem.

Lemma pi_lvP pi s s' x v : 
  wf_pimap pi -> valid_pi s pi ->
  write_lval gd x v s = ok s' ->
  [/\ wf_pimap (pi_lv pi x).1,
      write_lval gd (pi_lv pi x).2 v s = ok s' &
      valid_pi s' (pi_lv pi x).1].
Proof.
  move=> hwf hvalid; case: x => /=.
  + move=> vi ty /write_noneP [] -> h; split => //.
    by rewrite /write_none; case: h => [ [? ->] | [-> ->]].
  + move=> x hx; split => //; first by apply wf_remove.
    move: hx; rewrite /write_var; t_xrbindP => vm hset <-.
    by apply: valid_set_var hset hvalid.
  + move=> ws x e; t_xrbindP => px vx gx hpx pe ve he hpe w hw m hwr <-.
    split; first by apply wf_remove_m.
    + by rewrite gx (pi_eP hvalid he) /= hpx hpe hw /= hwr.
    move=> y c vy /=; rewrite remove_mP //.
    case: ifP => //.
    move=> hm hy hgy; rewrite hy /= in hm.
    have <- := hvalid _ _ _ hy hgy.
    have [_ ] := hwf _ _ hy; rewrite hm => hn.
    by apply use_memP => //=; rewrite -hn.
  + move=> aa ws x e; apply on_arr_varP => n t hty hx.
    t_xrbindP => i ve he hi w hw t' ht' vm hset <-.  
    split; first by apply wf_remove.
    + by rewrite /on_arr_var hx (pi_eP hvalid he) /= hi hw /= ht' /= hset.
    by apply: valid_set_var hset hvalid.
  move=> aa ws len x e; apply on_arr_varP => n t hty hx.
  t_xrbindP => i ve he hi w hw t' ht' vm hset <-.  
  split; first by apply wf_remove.
  + by rewrite /on_arr_var hx (pi_eP hvalid he) /= hi hw /= ht' /= hset.
  by apply: valid_set_var hset hvalid.  
Qed.

Lemma pi_lvsP pi s s' xs vs : 
  wf_pimap pi -> valid_pi s pi ->
  write_lvals gd s xs vs = ok s' ->
  [/\ wf_pimap (pi_lvs pi xs).1,
      write_lvals gd s (pi_lvs pi xs).2 vs = ok s' &
      valid_pi s' (pi_lvs pi xs).1].
Proof.
  elim: xs vs pi s => [ | x xs hrec] [ | v vs] //= pi s hwf hvalid.
  + by move=> [<-].
  t_xrbindP => s1 /(pi_lvP hwf hvalid).
  case: pi_lv => pi1 x' [ hwf1 hw1 hvalid1].
  move=> /(hrec _ _ _ hwf1 hvalid1); case: pi_lvs => pi' xs' [hwf' hw' hvalid'].
  by rewrite /= hw1.
Qed.
  

Definition set_lv (pi:pimap) x tag ty (e:pexpr) :=
  if x is Lvar x then
    if (tag == AT_inline) && (x.(vtype) == ty) then set pi x e
    else pi
  else pi.

Module Import E.

  Definition pass : string := "propagate inline".

  Definition ii_loop_iterator := ii_loop_iterator pass.

  Definition error := pp_internal_error_s pass.

End E.

Section LOOP.

  Context (pi_i : pimap -> instr -> cexec (pimap * instr)). 

  (* TODO: add map_foldM in utils *)
  Fixpoint pi_c (pi:pimap) (c:cmd) := 
    match c with
    | [::] => ok (pi, [::])
    | i::c => 
      Let pii := pi_i pi i in 
      Let pic := pi_c pii.1 c in
      ok (pic.1, pii.2 :: pic.2)
    end.

  Context (ii:instr_info).
  Context (x:var) (c:cmd).

  Fixpoint loop_for (n:nat) (pi:pimap)  :=
    match n with
    | O => Error (E.ii_loop_iterator ii)
    | S n =>
      let pii := remove pi x in
      Let pic := pi_c pii c in
      if incl pi pic.1 then ok (pi, pic.2)
      else loop_for n (merge pi pic.1)
    end.

  Context (c1:cmd) (e:pexpr) (c2:cmd).

  Fixpoint loop_while (n:nat) (pi:pimap) :=
    match n with
    | O => Error (E.ii_loop_iterator ii)
    | S n =>
      (* c1; while e do c2; c1 *)
      Let pic1 := pi_c pi c1 in
      Let pic2 := pi_c pic1.1 c2 in
      if incl pi pic2.1 then ok (pic1.1, pic1.2, pi_e pic1.1 e, pic2.2)
      else loop_while n (merge pi pic2.1) 
    end.

End LOOP.

Fixpoint pi_i (pi:pimap) (i:instr) := 
  let (ii, ir) := i in
  match ir with
  | Cassgn x tag ty e =>
    let e := pi_e pi e in
    let (pi, x) := pi_lv pi x in 
    let pi := set_lv pi x tag ty e in
    ok (pi, MkI ii (Cassgn x tag ty e))

  | Copn xs tag o es => 
    let es := pi_es pi es in
    let (pi, xs) := pi_lvs pi xs in
    ok (pi, MkI ii (Copn xs tag o es))

  | Cif e c1 c2 => 
    let e := pi_e pi e in
    Let pic1 := pi_c pi_i pi c1 in
    Let pic2 := pi_c pi_i pi c2 in
    let pi := merge pic1.1 pic2.1 in
    ok (pi, MkI ii (Cif e pic1.2 pic2.2))

  | Cfor x (d,e1,e2) c => 
    let e1 := pi_e pi e1 in
    let e2 := pi_e pi e2 in
    Let pic := loop_for pi_i ii x c Loop.nb pi in
    ok (pic.1, MkI ii (Cfor x (d,e1,e2) pic.2))
    
  | Cwhile a c1 e c2 => 
    Let pic := loop_while pi_i ii c1 e c2 Loop.nb pi in
    let:(pi, c1, e, c2) := pic in
    ok (pi, MkI ii (Cwhile a c1 e c2))

  | Ccall inline xs f es =>
    let es := pi_es pi es in
    let (pi, xs) := pi_lvs pi xs in
    ok (pi, MkI ii (Ccall inline xs f es))

  end.

Section Section.

Context {T} {pT:progT T}.

Definition pi_fun  (f:fundef) :=
  let 'MkFun ii si p c so r ev := f in
  Let pic := pi_c pi_i piempty c in 
  ok (MkFun ii si p pic.2 so r ev).

Definition pi_prog (p:prog) := 
  Let funcs := map_cfprog pi_fun (p_funcs p) in
  ok {| p_extra := p_extra p; p_globs := p_globs p; p_funcs := funcs |}.

End Section.



