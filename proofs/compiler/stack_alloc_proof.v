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
From CoqWord Require Import ssrZ.
Require Import psem compiler_util constant_prop_proof.
Require Export psem stack_alloc.
Require Import Psatz.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.
Local Open Scope Z_scope.

Import Region.

(* --------------------------------------------------------------------------- *)
(*
Definition size_of (t:stype) :=
  match t with
  | sword sz => wsize_size sz
  | sarr n   => Zpos n
  | _        => 1
  end.

Section Section.

Variables (pmap:pos_map) (stk_size glob_size:Z).
Variables (rsp rip: pointer).
(* FIXME: we should be more flexible on the alignment of rsp and rip *)
Hypothesis (is_align_rsp: forall ws, is_align rsp ws) (is_align_rip: forall ws, is_align rip ws).

Hypothesis (rsp_bound : wunsigned rsp + stk_size <= wbase Uptr)
           (rip_bound : wunsigned rip + glob_size <= wbase Uptr).

Hypothesis disj_rsp_rip :
  0 < stk_size -> 0 < glob_size ->
  wunsigned rsp + stk_size <= wunsigned rip \/ wunsigned rip + glob_size <= wunsigned rsp.

Lemma valid_align m p ws :
  valid_pointer m p ws →
  is_align p ws.
Proof. by case/Memory.valid_pointerP. Qed.

Hint Resolve is_align_no_overflow valid_align.

Definition global_pos x := 
  omap (fun z => (z, vtype x)) (Mvar.get pmap.(globals) x).

Definition local_pos x := 
  match get_local pmap x with
  | Some (Pstack z) => Some (z, vtype x)
  | Some (Pstkptr z) => Some (z, sword Uptr)
  | _ => None 
  end.

Record wf_pos (get : var -> option (Z * stype)) size := {
  wfg_ofs   : forall x ofs ty, get x = Some (ofs, ty) -> 
             0 <= ofs /\ ofs + size_of ty <= size;
  wfg_disj  : forall x y xofs yofs xty yty,
             x <> y ->
             get x = Some (xofs, xty) -> get y = Some (yofs, yty) ->
             xofs + size_of xty <= yofs \/ yofs + size_of yty <= xofs;
}.

Class wf_regptr := {
  wt_rip   : vtype pmap.(vrip) = sword Uptr;
  wt_rsp   : vtype pmap.(vrsp) = sword Uptr;
  wt_rptr  : forall x p, get_local pmap x = Some (Pregptr p) -> vtype p = sword Uptr;
  wf_ptr   : forall x, (exists p, get_local pmap x = Some (Pregptr p)) \/
                       (exists z, get_local pmap x = Some (Pstkptr z)) ->
                       is_sarr (vtype x);
  disj_ptr : forall x xp, 
              get_local pmap x = Some (Pregptr xp) -> 
              [/\ xp <> pmap.(vrip), xp <> pmap.(vrsp), Sv.In xp pmap.(vnew) &
                  forall y yp, x <> y -> 
                               get_local pmap y = Some (Pregptr yp) -> xp <> yp];
}.

Class wf_pmap := {
  rip_in_new : Sv.In pmap.(vrip) pmap.(vnew);
  rsp_in_new : Sv.In pmap.(vrsp) pmap.(vnew);
  wt_regptr  :> wf_regptr;
  wf_globals :> wf_pos global_pos glob_size;
  wf_locals  :> wf_pos local_pos stk_size;
}.

Declare Instance wf_pmapI : wf_pmap.

Definition valid_mp mp ty := 
  exists x, 
    subtype ty (vtype x) /\
    if mp.(mp_s) == MSglob then get_global pmap x = ok mp.(mp_ofs)
    else get_local pmap x = Some (Pstack mp.(mp_ofs)).

Definition eq_vm (vm1 vm2:vmap) := 
  forall (x:var), get_local pmap x = None -> get_var vm1 x = get_var vm2 x.

Definition wptr ms := 
  if ms == MSglob then rip else rsp.

Definition wptr_size ms :=
  if ms == MSstack then stk_size else glob_size.

Definition disjoint_ptr m :=
  forall w sz ms,
    valid_pointer m w sz ->
    ~ ( wunsigned (wptr ms) < wunsigned w + wsize_size sz /\ wunsigned w < wunsigned (wptr ms) + wptr_size ms).

Definition mp_addr mp := 
  (wptr mp.(mp_s) + wrepr _ mp.(mp_ofs))%R.

Definition eq_mp_word (m2:mem) mp sz v := 
  exists w:word sz, 
    v = Vword w /\ read_mem m2 (mp_addr mp) sz = ok w.

Definition eq_mp_array (m2:mem) mp s v := 
  exists (a:WArray.array s),
   v = Varr a /\
   forall off, (0 <= off < Zpos s)%Z ->
     forall v, WArray.get AAscale U8 a off = ok v ->
     read_mem m2 (wptr mp.(mp_s) + (wrepr _ (off + mp.(mp_ofs)))) U8 = ok v.

Definition eq_mp_val ty (m2:mem) mp v := 
  match ty with
  | sword ws => eq_mp_word m2 mp ws v
  | sarr  s  => eq_mp_array m2 mp s v 
  | _        => True
  end.
  
Variable (P: uprog) (ev: extra_val_t (progT := progUnit)).
Notation gd := (p_globs P).

Definition valid_pk pk mp (s2:estate) := 
  match pk with
  | Pstack z => mp = {| mp_s := MSstack; mp_ofs := z |}
  | Pstkptr z => 
    read_mem s2.(emem) (mp_addr {| mp_s := MSstack; mp_ofs := z |}) Uptr = ok (mp_addr mp)
  | Pregptr p =>
    get_var s2.(evm) p = ok (Vword (mp_addr mp))
  end.
   
Definition check_gvalid rmap x := 
  if is_glob x then 
    omap (fun ofs => {| mp_s := MSglob; mp_ofs := ofs |}) (Mvar.get pmap.(globals) (gv x))
  else 
    match check_valid rmap (gv x) with
    | Ok mp => Some mp
    | _     => None 
    end.

(* wfr_get_v_mp : 
    forall x xs mp, Mmp.get rmap.(region_vars) mp = Some xs ->
                    Sv.In x xs -> Mvar.get rmap.(var_region) x = Some mp;*)

Definition wfr_VALID (rmap:regions) :=
   forall x mp, Mvar.get rmap.(var_region) x = Some mp -> valid_mp mp (vtype x).

Definition wfr_VAL (rmap:regions) (s1:estate) (s2:estate) :=
  forall x mp v, check_gvalid rmap x = Some mp -> 
    get_gvar gd s1.(evm) x = ok v ->
    eq_mp_val (vtype (gv x)) s2.(emem) mp v.

Definition wfr_PTR (rmap:regions) (s2:estate) :=
  forall x mp, Mvar.get (var_region rmap) x = Some mp ->
    exists pk, get_local pmap x = Some pk /\ valid_pk pk mp s2. 

Class wf_region (rmap:regions) (s1:estate) (s2:estate) := {  
  wfr_valid_mp :  wfr_VALID rmap;
  wfr_val : wfr_VAL rmap s1 s2;
  wfr_ptr : wfr_PTR rmap s2;
}.

Definition eq_glob (m1 m2:mem) := 
  forall w sz, valid_pointer m1 w sz -> read_mem m1 w sz = read_mem m2 w sz.

Definition eq_not_mod (m0 m2:mem) := 
  forall ofs, 
     0 <= ofs < stk_size ->
     (forall x xofs xty, 
        local_pos x = Some(xofs, xty) -> 
        xofs + size_of xty <= ofs \/ ofs + 1 <= xofs) ->
     read_mem m0 (rsp + (wrepr _ ofs)) U8 = 
     read_mem m2 (rsp + (wrepr _ ofs)) U8.

Class valid_state (rmap:regions) (m0:mem) (s1:estate) (s2:estate) := {
   vs_val_ptr : 
      forall s w, (0 <= wunsigned w < wptr_size s) -> valid_pointer (emem s2) (wptr s + w) U8;
   vs_disj      : disjoint_ptr (emem s1);
   vs_rip       : get_var (evm s2) pmap.(vrip) = ok (Vword rip);
   vs_rsp       : get_var (evm s2) pmap.(vrsp) = ok (Vword rsp);
   vs_top_frame : ohead (frames (emem s2)) = Some (rsp, stk_size);
   vs_eq_vm     : eq_vm s1.(evm) s2.(evm);
   vs_wf_region :> wf_region rmap s1 s2;
   vs_eq_mem    : eq_glob s1.(emem) s2.(emem);
   vs_eq_not_mod: eq_not_mod m0 s2.(emem);
}.

(* -------------------------------------------------------------------------- *)

Lemma get_globalP x z : get_global pmap x = ok z <-> Mvar.get pmap.(globals) x = Some z.
Proof.
  rewrite /get_global; case: Mvar.get; last by split.
  by move=> ?;split => -[->].
Qed.

Lemma get_gvar_glob gd x vm : is_glob x -> get_gvar gd vm x = sem.get_global gd (gv x).
Proof. by rewrite /get_gvar /is_lvar /is_glob => /eqP ->. Qed.

Lemma get_gvar_nglob gd x vm : ~~is_glob x -> get_gvar gd vm x = get_var vm (gv x).
Proof. by rewrite /get_gvar /is_lvar /is_glob; case: (gs x). Qed.

Lemma cast_ptrP gd s e i : sem_pexpr gd s e >>= to_int = ok i ->
  sem_pexpr gd s (cast_ptr e) = ok (Vword (wrepr U64 i)).
Proof. by t_xrbindP => v he hi ;rewrite /cast_ptr /cast_w /= he /sem_sop1 /= hi. Qed.

Lemma cast_wordP gd s e i : 
  sem_pexpr gd s e >>= to_int = ok i ->
  exists sz (w:word sz), sem_pexpr gd s (cast_word e) = ok (Vword w) /\
                         truncate_word U64 w = ok (wrepr U64 i).
Proof.
  move=> he.
  have : exists sz (w:word sz), 
              sem_pexpr gd s (cast_ptr e) = ok (Vword w) /\
                      truncate_word U64 w = ok (wrepr U64 i). 
  + exists U64, (wrepr U64 i); split; first by apply cast_ptrP.
    by rewrite truncate_word_u.
  case: e he => // -[] // [] //=.
  move=> e he _; move: he; rewrite /sem_sop1 /=; t_xrbindP => v v' -> w.
  move=> /to_wordI [sw [w' [hsw -> ->]]] <- [<-].
  by exists sw, w'; split => //; rewrite /truncate_word hsw wrepr_unsigned.
Qed.

Lemma mk_ofsP aa sz gd s2 ofs e i :
  sem_pexpr gd s2 e >>= to_int = ok i ->
  sem_pexpr gd s2 (mk_ofs aa sz e ofs) = ok (Vword (wrepr U64 (i * mk_scale aa sz + ofs)%Z)).
Proof.
  rewrite /mk_ofs; case is_constP => /= [? [->] //| {e} e he] /=.
  rewrite /sem_sop2 /=.
  have [sz' [w [-> /= -> /=]]]:= cast_wordP he.
  by rewrite !zero_extend_u wrepr_add wrepr_mul GRing.mulrC. 
Qed.

Lemma validr_valid_pointer (m1:mem) p ws : is_ok (validr m1 p ws) = valid_pointer m1 p ws.
Proof.
  case: (Memory.readV m1 p ws); rewrite Memory.readP /CoreMem.read.
  + by move=> [w]; case: validr.
  by case: validr => //= _ [];eauto.
Qed.

Lemma check_validP rmap x mp : 
  check_valid rmap x = ok mp <->
  (Mvar.get (var_region rmap) x = Some mp /\
   exists xs,  Mmp.get (region_vars rmap) mp = Some xs /\ Sv.In x xs).
Proof.
  rewrite /check_valid.
  case heq: Mvar.get => [mp' |]; last by intuition.
  case heq1 : Mmp.get => [xs | /=]; last by split => // -[] [?]; subst mp'; rewrite heq1 => -[] ?[].
  case: ifPn => /Sv_memP hin /=.
  + split => [ [?] | [[?] ]]; subst mp' => //.
    by split => //;exists xs.
  by split => // -[] [?]; subst mp'; rewrite heq1 => -[xs'] [[<-]] /hin.
Qed.

Section EXPR.
  Variables (rmap:regions) (m0:mem) (s:estate) (s':estate).
  Hypothesis (hvalid: valid_state rmap m0 s s').

  Lemma get_var_kindP x v:
    get_var_kind pmap x = ok None -> 
    get_gvar gd (evm s) x = ok v ->
    get_gvar [::] (evm s') x = ok v.
  Proof.
    rewrite /get_var_kind; case: ifPn => hglob; first by t_xrbindP.
    case hgl : get_local => // _.
    assert (heq := vs_eq_vm hgl). 
    by rewrite !get_gvar_nglob // heq.
  Qed.

  Lemma check_mk_addr_ptr (x:var_i) aa ws xi ei e1 i1 pk mp :
    sem_pexpr [::] s' e1 >>= to_int = ok i1 ->
    get_local pmap x = Some pk ->
    Mvar.get (var_region rmap) x = Some mp ->
    is_align (wrepr Uptr mp.(mp_ofs)) ws ->
    mk_addr_ptr pmap x aa ws pk e1 = ok (xi, ei) ->
    ∃ (wx wi : u64),
      [/\ Let x := get_var (evm s') xi in to_pointer x = ok wx,
          Let x := sem_pexpr [::] s' ei in to_pointer x = ok wi, (mp_addr mp + wrepr U64 (i1 * mk_scale aa ws))%R = (wx + wi)%R
          & is_align (mp_addr mp) ws].
  Proof.
    move=> he1 hloc hgetr hal.
    rewrite /mk_addr_ptr; assert (h := wfr_ptr hgetr).
    case: h => [pk' []]; rewrite hloc => -[?]; subst pk'.
    case: pk hloc => //[ ofs | p] hloc /= hvmk [<- <-].
    + exists rsp, (wrepr U64 ofs + wrepr U64 (i1 * mk_scale aa ws))%R. 
      subst mp; rewrite (mk_ofsP aa ws ofs he1) /= /mp_addr /wptr vs_rsp /= !truncate_word_u. 
      split => //.
      + by f_equal; rewrite !(wrepr_add, wrepr_mul); ssrring.ssring.
      + by ssrring.ssring.
      by apply is_align_add.
    exists (mp_addr mp), (wrepr U64 (i1 * mk_scale aa ws)).
    rewrite (mk_ofsP aa ws 0 he1) /= hvmk /= !truncate_word_u; split => //.
    + by f_equal; rewrite !(wrepr_add, wrepr_mul, wrepr0); ssrring.ssring.
    by case: (mp) hal => -[] /= ofs ?; apply is_align_add.
  Qed.

  Lemma check_mk_addr x vpk aa ws t xi ei e1 i1: 
    sem_pexpr [::] s' e1 >>= to_int = ok i1 ->
    get_var_kind pmap x = ok (Some vpk) ->
    check_vpk_word rmap (gv x) vpk ws = ok t ->
    mk_addr pmap (gv x) aa ws vpk e1 = ok (xi, ei) ->
    exists mp wx wi, 
    [/\ check_gvalid rmap x = Some mp,
        get_var (evm s') xi >>= to_pointer = ok wx,
        sem_pexpr [::] s' ei >>= to_pointer = ok wi, 
        (mp_addr mp + wrepr Uptr (i1 * mk_scale aa ws)%Z = wx + wi)%R & 
        is_align (mp_addr mp) ws].
  Proof.
    move=> he1; rewrite /get_var_kind /check_vpk_word /mk_addr /with_var.
    case: ifP => hglob.
    + t_xrbindP => ofs /get_globalP hget <- /assertP halign [<-] <-.
      exists {| mp_s := MSglob; mp_ofs := ofs |}, rip,
        (wrepr U64 ofs + wrepr U64 (i1 * mk_scale aa ws))%R. 
      rewrite /mp_addr /= /wptr vs_rip (mk_ofsP aa ws ofs he1) /= !truncate_word_u /check_gvalid hglob hget.
      split => //.
      + by f_equal; rewrite !(wrepr_add, wrepr_mul); ssrring.ssring.
      + by ssrring.ssring.
      by apply is_align_add. 
    move=> []; case hloc: get_local => [pk | //] [<-] hc ha.
    move: hc; rewrite /check; t_xrbindP => mp hcv.
    case /check_validP: (hcv) => [hgetr _] /assertP hal.
    have [wx [wi [*]]] := check_mk_addr_ptr he1 hloc hgetr hal ha.   
    exists mp, wx, wi; split => //.
    by rewrite /check_gvalid hglob hcv.
  Qed.

  Lemma ge0_wunsigned ws (w:word ws) : 0 <= wunsigned w.
  Proof. by case (wunsigned_range w). Qed.
  
  Lemma wunsigned_repr_le ws z : 0 <= z -> wunsigned (wrepr ws z) <= z. 
  Proof. by move=> hz; rewrite wunsigned_repr; apply Z.mod_le. Qed.

  Lemma arr_is_align p ws : WArray.is_align p ws -> is_align (wrepr _ p) ws.
  Proof.
    move=> /eqP h1; apply is_align_mod.
    have hn := wsize_size_pos ws.
    have hnz : wsize_size ws ≠ 0%Z by Psatz.lia.
    by rewrite wunsigned_repr -/(wbase Uptr) (cut_wbase_Uptr ws) Z.mul_comm mod_pq_mod_q.
  Qed.

  Lemma check_gvalid_mp x mp : 
    check_gvalid rmap x = Some mp ->
    valid_mp mp (vtype (gv x)).
  Proof.
    rewrite /check_gvalid; case:ifP => hglob.
    + case heq: Mvar.get => [ofs /= | //] [<-].
      by exists (gv x); rewrite /get_global heq; split => //; rewrite Z.leb_refl.
    case heq: check_valid => [mp' | //] [?]; subst mp'.
    move: heq; rewrite check_validP => -[hget _].
    by apply: wfr_valid_mp hget.
  Qed.

  Lemma check_gvalid_valid_pointer (n:positive) x mp aa ws i : 
    vtype (gv x) = sarr n ->
    check_gvalid rmap x = Some mp -> 
    is_align (mp_addr mp) ws ->
    0 <= i * mk_scale aa ws ->
    i * mk_scale aa ws + wsize_size ws <= n ->
    WArray.is_align (i * mk_scale aa ws) ws ->
    valid_pointer (emem s') (mp_addr mp + wrepr U64 (i * mk_scale aa ws))%R ws.
  Proof.
    move=> hty hcheck hal h0i hi hala.    
    apply Memory.is_align_valid_pointer.
    + by apply is_align_add => //; apply arr_is_align.
    move=> k hk; have := check_gvalid_mp hcheck.
    rewrite hty => -[x' [/subtypeEl /= [n' [hty' hnn']] hget]].
    rewrite /mp_addr -!GRing.addrA -!wrepr_add.
    apply vs_val_ptr; split; first by apply ge0_wunsigned.
    case: (mp) hget => -[] ofs /= hget;rewrite /wptr /wptr_size /=.
    + assert (h:= wfg_ofs wf_globals); move: (h x').
      move: hget; rewrite get_globalP => hget.
      rewrite /global_pos /wptr hget => /(_ _ _ erefl) [h0z].
      rewrite hty' /= => hbound; apply: Z.le_lt_trans. 
      + by apply wunsigned_repr_le; nia.
      lia.
    assert (h:= wfg_ofs wf_locals); move: (h x').
    rewrite /local_pos /wptr hget => /(_ _ _ erefl) [h0z].
    rewrite hty' /= => hbound; apply: Z.le_lt_trans. 
    + by apply wunsigned_repr_le; nia.
    lia.
  Qed.
   
  Lemma get_arr_read_mem (n:positive) (t : WArray.array n) mp aa ws i w x:
    vtype (gv x) = sarr n ->
    eq_mp_val (sarr n) (emem s') mp (Varr t) ->
    check_gvalid rmap x = Some mp ->
    WArray.get aa ws t i = ok w ->
    is_align (mp_addr mp) ws ->
    read_mem (emem s') (mp_addr mp + wrepr U64 (i * mk_scale aa ws)) ws = ok w.
  Proof.
    move=> hty heq hval hget hal.
    rewrite Memory.readP /CoreMem.read.
    have [hbound1 hbound2 hbound3] := WArray.get_bound hget.
    have := check_gvalid_valid_pointer hty hval hal hbound1 hbound2 hbound3. 
    rewrite -validr_valid_pointer => /is_okP [?] /= => hv; rewrite hv.
    case: heq => t' [] /Varr_inj [] heq.
    rewrite (Eqdep_dec.UIP_dec Pos.eq_dec heq erefl) /= => {heq} ? hgr;subst t'.
    move: (hget);rewrite /WArray.get /CoreMem.read; t_xrbindP => ? _ <-.
    do 2 f_equal; rewrite /CoreMem.uread.
    apply eq_map_ziota => k hk /=.
    have [v hget8]:= WArray.get_get8 AAscale hget hk.
    have /WArray.get_uget -> := hget8.
    move /hgr: hget8; rewrite Memory.readP /CoreMem.read.
    have h: 0 <= i * mk_scale aa ws + k ∧ i * mk_scale aa ws + k < n by lia.
    move=> /(_ h){h}; t_xrbindP => ? hvr.
    have -> : (wptr (mp_s mp) + wrepr U64 (i * mk_scale aa ws + k + mp_ofs mp))%R = 
              ((mp_addr mp + wrepr U64 (i * mk_scale aa ws)) + wrepr U64 k)%R.
    + by rewrite /mp_addr !wrepr_add; ssrring.ssring.
    by rewrite CoreMem.uread8_get Memory.addP => ->.
  Qed.

  Let X e : Prop :=
    ∀ e' v,
      alloc_e pmap rmap e = ok e' →
      sem_pexpr gd s e = ok v →
      sem_pexpr [::] s' e' = ok v.

  Let Y es : Prop :=
    ∀ es' vs,
      alloc_es pmap rmap es = ok es' →
      sem_pexprs gd s es = ok vs →
      sem_pexprs [::] s' es' = ok vs.

  Lemma check_varP (x:var_i) t: 
    check_var pmap x = ok t -> 
    get_var_kind pmap (mk_lvar x) = ok None.
  Proof. by rewrite /check_var /get_var_kind /=; case: get_local. Qed.

  Lemma check_e_esP : (∀ e, X e) * (∀ es, Y es).
  Proof.
    apply: pexprs_ind_pair; subst X Y; split => /=.
    + by move=> ?? [<-] [<-].
    + move=> e he es hes ??; t_xrbindP => e' /he{he}he es' /hes{hes}hes <- /=.
      by move=> v /he -> vs /hes -> <-.
    + by move=> z ?? [<-] [<-].
    + by move=> b ?? [<-] [<-].
    + by move=> n ?? [<-] [<-].
    + move=> x e' v; t_xrbindP => -[ vpk | ] hgvk; last first.
      + by move=> [<-]; apply: get_var_kindP hgvk.
      case hty: is_word_type => [ws | //]; move /is_word_typeP: hty => hty.
      t_xrbindP => ? hcheck [xi ei] haddr <- /=.
      have h0: Let x := sem_pexpr [::] s' 0 in to_int x = ok 0 by done.
      have [mp [wx [wi [hgval -> -> /= <- hal ]]]]:= check_mk_addr h0 hgvk hcheck haddr.
      by move=> /(wfr_val hgval); rewrite hty wrepr0 GRing.addr0 => -[ w [-> ->]].
    + move=> aa sz x e1 he1 e' v he'; apply: on_arr_gvarP => n t hty /= hget.
      t_xrbindP => i vi /he1{he1}he1 hvi w hw <-.
      move: he'; t_xrbindP => e1' /he1{he1}he1' _ _. 
      have h0 : sem_pexpr [::] s' e1' >>= to_int = ok i.
      + by rewrite he1'.
      move=> [vptr | ]; last first.
      + by move => /get_var_kindP -/(_ _ hget) h [<-] /=; rewrite h /= h0 /= hw.
      t_xrbindP => hgvk ? hcheck [xi ei] haddr <- /=.
      have [mp [wx [wi [hgval -> -> /= <- hal ]]]] := check_mk_addr h0 hgvk hcheck haddr.
      assert (h:= wfr_val hgval hget); move: h;rewrite hty => h.
      by rewrite (get_arr_read_mem hty h hgval hw hal).
    + move=> sz1 v1 e1 IH e2 v.
      t_xrbindP => ? /check_varP hc e1' /IH hrec <- wv1 vv1 /= hget hto' we1 ve1.
      move=> /hrec -> hto wr hr ?;subst v. 
      have := get_var_kindP hc hget; rewrite /get_gvar /= => -> /=.
      by rewrite hto' hto /= -(vs_eq_mem (read_mem_valid_pointer hr)) hr.
    + move=> o1 e1 IH e2 v.
      by t_xrbindP => e1' /IH hrec <- ve1 /hrec /= ->.
    + move=> o1 e1 H1 e1' H1' e2 v.
      by t_xrbindP => e1_ /H1 hrec e1'_ /H1' hrec' <- ve1 /hrec /= -> /= ve2 /hrec' ->.
    + move => e1 es1 H1 e2 v.
      t_xrbindP => es1' /H1{H1}H1 <- vs /H1{H1} /=.
      by rewrite /sem_pexprs => ->.
    move=> t e He e1 H1 e1' H1' e2 v.   
    t_xrbindP => e_ /He he e1_ /H1 hrec e1'_ /H1' hrec' <-.
    by move=> b vb /he /= -> /= -> ?? /hrec -> /= -> ?? /hrec' -> /= -> /= ->.
  Qed.

  Definition alloc_eP := check_e_esP.1.
  Definition alloc_esP := check_e_esP.2.

End EXPR.

Lemma check_diffP x t : check_diff pmap x = ok t -> ~Sv.In x (vnew pmap).
Proof. by rewrite /check_diff; case:ifPn => /Sv_memP. Qed.

Lemma get_var_eq x vm v : get_var vm.[x <- v] x = on_vu (pto_val (t:=vtype x)) undef_error v.
Proof. by rewrite /get_var Fv.setP_eq. Qed.

Lemma get_var_neq x y vm v : x <> y -> get_var vm.[x <- v] y = get_var vm y.
Proof. by move=> /eqP h; rewrite /get_var Fv.setP_neq. Qed.

Lemma get_var_set_eq vm1 vm2 (x y : var) v: 
  get_var vm1 y = get_var vm2 y ->
  get_var vm1.[x <- v] y = get_var vm2.[x <- v] y.
Proof.
  by case:( x =P y) => [<- | hne]; rewrite !(get_var_eq, get_var_neq).
Qed.

Lemma is_lvar_is_glob x : is_lvar x = ~~is_glob x.
Proof. by case: x => ? []. Qed.

Lemma get_gvar_eq gd x vm v : 
  ~is_glob x -> get_gvar gd vm.[gv x <- v] x = on_vu (pto_val (t:=vtype (gv x))) undef_error v.
Proof. 
  by move=> /negP => h; rewrite /get_gvar is_lvar_is_glob h get_var_eq.
Qed.

Lemma get_gvar_neq gd (x:var) y vm v : (~is_glob y -> x <> (gv y)) -> get_gvar gd vm.[x <- v] y = get_gvar gd vm y.
Proof. 
  move=> h; rewrite /get_gvar is_lvar_is_glob. 
  by case: negP => // hg; rewrite get_var_neq //; apply h.
Qed.

Lemma get_gvar_set_eq gd vm1 vm2 x y v: 
  get_gvar gd vm1 y = get_gvar gd vm2 y ->
  get_gvar gd vm1.[x <- v] y = get_gvar gd vm2.[x <- v] y.
Proof.
  case : (@idP (is_glob y)) => hg; first by rewrite !get_gvar_neq.
  case:( x =P (gv y)) => heq; last by rewrite !get_gvar_neq.
  by move: v; rewrite heq => v; rewrite !get_gvar_eq.
Qed.

Lemma get_localn_checkg_diff rmap mp s2 x y : 
  get_local pmap x = None ->
  wfr_PTR rmap s2 ->
  check_gvalid rmap y = Some mp ->
  (~is_glob y -> x <> (gv y)).
Proof.
  rewrite /check_gvalid /wfr_PTR; case:ifPn => // hg hl hwf.
  case heq: check_valid => [mp' | // ].
  move=> [?] _; subst mp'.
  have /check_validP [ /hwf [mpy [hy _]] _] := heq.
  by move=> hx; subst x; move: hy; rewrite hl.
Qed.

Lemma valid_state_set_var rmap m0 s1 s2 x v:
  valid_state rmap m0 s1 s2 ->
  get_local pmap x = None ->
  ¬ Sv.In x (vnew pmap) ->
  valid_state rmap m0 (with_vm s1 (evm s1).[x <- v]) (with_vm s2 (evm s2).[x <- v]).
Proof.
  case: s1 s2 => mem1 vm1 [mem2 vm2] [/=] hvptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm hget hnin.
  constructor => //=.
  + by rewrite get_var_neq //; assert (h:=rip_in_new); SvD.fsetdec.
  + by rewrite get_var_neq //; assert (h:=rsp_in_new); SvD.fsetdec.
  + by move=> y hy; apply get_var_set_eq; apply heqvm.
  rewrite /with_vm /=; case: hwfr => /= hgmp hval hptr.
  constructor => //=.
  + move=> y mp vy hy; have ? := get_localn_checkg_diff hget hptr hy.
    by rewrite get_gvar_neq //; apply hval.
  move=> y mp hy; have [pk [hgety hpk]]:= hptr y mp hy; exists pk; split => //.
  case: pk hgety hpk => //= yp hyp.  
  assert (h := disj_ptr hyp); case: h => _ _ hin _ <-.
  by rewrite get_var_neq //; SvD.fsetdec.
Qed.

Lemma set_wordP rmap x ws rmap': 
  set_word rmap x ws = ok rmap' ->
  exists mp,
  [/\ Mvar.get (var_region rmap) x = Some mp,
      mp_s mp = MSstack, 
      is_align (wrepr Uptr (mp_ofs mp)) ws &
      rmap' = rset_word rmap x mp]. 
Proof.
  rewrite /set_word.
  case heq : Mvar.get => [ [[] ofs] | ] //=.
  t_xrbindP => ? /assertP hal <-.
  by eexists; split; first reflexivity.
Qed.

Lemma wsize_size_le ws ws': (ws ≤ ws')%CMP -> (wsize_size ws <= wsize_size ws').
Proof. by case: ws ws' => -[]. Qed.

Lemma size_of_le ty ty' : subtype ty ty' -> size_of ty <= size_of ty'.
Proof.
  case: ty => [||p|ws]; case:ty' => [||p'|ws'] //.
  + by move=> /ZleP.
  by apply wsize_size_le.
Qed.
  
Lemma gt0_size_of ty : 0 < size_of ty.
Proof. by case: ty. Qed.

Lemma check_gvalid_rset_word rmap x y mp mpy: 
  mp_s mp = MSstack ->
  Mvar.get (var_region rmap) x = Some mp ->
  check_gvalid (rset_word rmap x mp) y = Some mpy ->
  [/\ ~is_glob y, x = (gv y) & mp = mpy] \/ 
  [/\ (~is_glob y -> x <> gv y), mp <> mpy &check_gvalid rmap y = Some mpy].
Proof.
  rewrite /check_gvalid /rset_word => hmps hgx.
  case:ifPn => ?.
  + move=> h; right;split => //.
    by case: Mvar.get h => // ? [<-] => ?; subst mp.
  case heq : check_valid => [mp1 | //] [?]; subst mp1.
  move:heq; rewrite check_validP => /= -[hgy [xs []]].
  rewrite Mmp.setP; case: eqP => [? [?]| ].
  + by subst mpy xs => /SvD.F.singleton_iff ?; left.
  move=> hd hg /Sv_memP hin; right; split => //.
  + by move=> _ ?; subst x; apply hd; move: hgy;rewrite hgx => -[].
  by rewrite /check_valid hgy hg hin.
Qed.

Lemma get_global_pos x ofs: 
  get_global pmap x = ok ofs ->
  global_pos x = Some (ofs, vtype x).
Proof. by rewrite get_globalP /global_pos => ->. Qed.

Lemma get_local_pos x ofs:
  get_local pmap x = Some (Pstack ofs) ->
  local_pos x = Some (ofs, vtype x).
Proof. by rewrite /local_pos => ->. Qed.

Lemma valid_mp_bound mp ty : 
  valid_mp mp ty ->
  0 <= mp_ofs mp ∧ 
  mp_ofs mp + size_of ty <= wptr_size (mp_s mp).
Proof.
  move=> [x [/size_of_le hsub hv]].
  case: eqP hv => heq.
  + rewrite heq => /get_global_pos hgp. 
    assert (h:= wfg_ofs wf_globals hgp); rewrite /wptr_size /=; lia.
  move=> /get_local_pos hgx.
  assert (h:= wfg_ofs wf_locals hgx).
  have -> : mp_s mp = MSstack by case: (mp_s mp) heq.
  rewrite /wptr_size /=; lia.
Qed.

Lemma valid_mp_addr mp ty: 
  valid_mp mp ty ->
  wunsigned (mp_addr mp) = wunsigned (wptr (mp_s mp)) + (mp_ofs mp).
Proof.
  move=> /valid_mp_bound; rewrite /mp_addr => h.
  apply wunsigned_add; have ? := gt0_size_of ty.
  have := @ge0_wunsigned Uptr (wptr (mp_s mp)).
  by case: (mp_s mp) h; rewrite /wptr /wptr_size /=; lia.
Qed.

Lemma valid_mp_addr_bound mp ty: 
  valid_mp mp ty ->
  wunsigned (wptr (mp_s mp)) <= wunsigned (mp_addr mp) /\
  wunsigned (mp_addr mp) + size_of ty <= wunsigned (wptr (mp_s mp)) + wptr_size (mp_s mp).
Proof.
  move=> h; rewrite (valid_mp_addr h); have := (valid_mp_bound h); lia.
Qed.

Lemma ms_bound s : wunsigned (wptr s) + wptr_size s <= wbase Uptr.
Proof. by case: s. Qed.

Lemma disjoint_eq_mp_val p mp ty mem1 mem2 ws w v: 
  valid_mp mp ty ->
  disjoint_zrange p (wsize_size ws) (mp_addr mp) (size_of ty) ->
  write_mem mem1 p ws w = ok mem2 ->
  eq_mp_val ty mem1 mp v → 
  eq_mp_val ty mem2 mp v.
Proof.
  have hba := @ms_bound (mp_s mp); have hge0 := @ge0_wunsigned Uptr (mp_addr mp).
  move=> /valid_mp_addr_bound.
  case: ty => // [pt | ws']; rewrite /size_of => hbound hd hw /=.
  + move=> [t] [-> heq]; exists t;split => // off hoff v1 /(heq _ hoff) <-.     
    apply: (Memory.writeP_neq hw).
    case: hd => hno1 hno2 hd; rewrite /disjoint_range /disjoint_zrange wsize8.
    rewrite wrepr_add (GRing.addrC (wrepr _ _)) GRing.addrA -/(mp_addr mp).
    have heqa : wunsigned (mp_addr mp + wrepr U64 off) = wunsigned (mp_addr mp) + off.
    + rewrite wunsigned_add //; lia.
    split => //; rewrite /no_overflow ?zify; lia.
  move=> [w1] [-> heq]; exists w1; split => //; rewrite -heq.
  by apply: (Memory.writeP_neq hw). 
Qed.

Lemma valid_mp_disjoint mp1 mp2 ty1 ty2: 
  valid_mp mp1 ty1 -> 
  valid_mp mp2 ty2 ->
  mp1 <> mp2 -> 
  wunsigned (mp_addr mp1) + size_of ty1 <= wunsigned (mp_addr mp2) ∨ 
  wunsigned (mp_addr mp2) + size_of ty2 <= wunsigned (mp_addr mp1).
Proof.
  move=> h1 h2; rewrite (valid_mp_addr h1) (valid_mp_addr h2).
  case: mp1 mp2 h1 h2 => [ms1 ofs1] [ms2 ofs2].
  move=> [x1 [/size_of_le hle1 /= hget1]] [x2 [/size_of_le hle2 /= hget2]].
  have ? := gt0_size_of (vtype x1); have ? := gt0_size_of (vtype x2).
  assert (wfg := wf_globals); assert (wfl := wf_locals).
  case: ms1 hget1 => /= [/get_global_pos | /get_local_pos] h1.
  + have hg1 := wfg_ofs wfg h1; have hg2 := wfg_disj wfg _ h1.
    case: ms2 hget2 => /= [/get_global_pos | /get_local_pos] h2 hd.
    + have hxd: x1 <> x2 by move=> h;apply hd; move: h2; rewrite -h h1 => -[->].
      by have:= hg2 _ _ _ hxd h2; lia.
    have hl2:=  wfg_ofs wfl h2; rewrite /wptr /wptr_size /=; lia.
  have hl1 := wfg_ofs wfl h1; have hl2 := wfg_disj wfl _ h1.
  case: ms2 hget2 => /= [/get_global_pos | /get_local_pos] h2 hd.
  + have hg2:=  wfg_ofs wfg h2; rewrite /wptr /wptr_size /=; lia.
  have hxd: x1 <> x2 by move=> h;apply hd; move: h2; rewrite -h h1 => -[->].
  by have:= hl2 _ _ _ hxd h2; lia.
Qed.

Lemma eq_mp_val_write_disj rmap m0 s1 s2 x y mp mpy mem2 v ws w p:
  valid_state rmap m0 s1 s2 ->  
  Mvar.get (var_region rmap) x = Some mp ->
  mp_s mp = MSstack ->
  between (mp_addr mp) (size_of (vtype x)) p ws ->
  check_gvalid rmap y = Some mpy ->
  mp ≠ mpy ->
  write_mem (emem s2) p ws w = ok mem2 ->
  eq_mp_val (vtype (gv y)) (emem s2) mpy v → 
  eq_mp_val (vtype (gv y)) mem2 mpy v.
Proof.
  move=> hvs hgx hs hb hcv hd.
  have hmpy := check_gvalid_mp hvs hcv; assert (hmp := wfr_valid_mp hgx).
  apply: disjoint_eq_mp_val => //.
  move: hb; rewrite /between !zify.
  have ? := valid_mp_addr_bound hmp; have ? := valid_mp_addr_bound hmpy.
  have ? := @ms_bound (mp_s mp); have ? := @ms_bound (mp_s mpy).
  split; rewrite /no_overflow ?zify. 
  + lia. + lia. 
  have := valid_mp_disjoint hmp hmpy hd; lia.
Qed.

Lemma get_local_pos_sptr x ofs : get_local pmap x = Some (Pstkptr ofs) -> local_pos x = Some(ofs, sword Uptr).
Proof. by rewrite /local_pos => ->. Qed.

Lemma sptr_addr x ofs: 
  local_pos x = Some (ofs, sword Uptr) ->
  wunsigned (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) = wunsigned rsp + ofs.
Proof.
  move=> h; assert (h1:= wfg_ofs wf_locals h).
  rewrite /mp_addr /wptr /=; apply wunsigned_add.
  move: (gt0_size_of (sword Uptr)) (@ge0_wunsigned Uptr rsp); lia.
Qed.

Lemma sptr_addr_bound x ofs:
  local_pos x = Some (ofs, sword Uptr) ->
  wunsigned rsp <= wunsigned (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) /\
  wunsigned (mp_addr {| mp_s := MSstack; mp_ofs := ofs |}) + wsize_size Uptr <= wunsigned rsp + stk_size.
Proof.
  move=> h; rewrite (sptr_addr h).
  assert (h1:= wfg_ofs wf_locals h); move: h1 => /=; lia.
Qed.

Lemma wfr_PTR_rset_word rmap m0 s1 s2 x mp p ws w mem2:
  valid_state rmap m0 s1 s2 ->  
  Mvar.get (var_region rmap) x = Some mp ->
  mp_s mp = MSstack ->
  between (mp_addr mp) (size_of (vtype x)) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  wfr_PTR rmap s2 ->
  wfr_PTR (rset_word rmap x mp) (with_mem s2 mem2).
Proof.
  move=> hvs hgx hms hb hw hwf y mpy /hwf [pk] [hgl hvpk]; exists pk;split => //.
  case: pk hgl hvpk => //= ofs hy <-.
  apply: (Memory.writeP_neq hw).
  assert (hmp := wfr_valid_mp hgx).
  case: (hmp) => x' [] /size_of_le hle; rewrite hms /= => hx.
  have hly:= get_local_pos_sptr hy; have hlx := get_local_pos hx.
  split.
  + by apply (is_align_no_overflow (Memory.valid_align (write_mem_valid_pointer hw))).
  + rewrite /no_overflow zify.
    have := sptr_addr_bound hly; lia.
  move: hb; rewrite /between !zify.
  assert (hwl := wf_locals).
  have hd : y <> x' by move=> heq;move: hy;rewrite heq hx.
  have /= := wfg_disj hwl hd hly hlx.
  rewrite (sptr_addr hly) (valid_mp_addr hmp) hms /wptr /=; lia.
Qed.

Lemma eq_glob_rset_word rmap m0 s1 s2 x mp p ws w mem2:
  valid_state rmap m0 s1 s2 ->  
  Mvar.get (var_region rmap) x = Some mp ->
  mp_s mp = MSstack ->
  between (mp_addr mp) (size_of (vtype x)) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  eq_glob (emem s1) (emem s2) ->
  eq_glob (emem s1) mem2.
Proof.
  move=> hvs hgx hms hb hw heg p1 ws1 hvp.
  rewrite (heg _ _ hvp); symmetry; apply: (Memory.writeP_neq hw).
  assert (hd:= vs_disj (ms:= mp_s mp) hvp); move:hd; rewrite hms /wptr /wptr_size /= => hd.
  assert (hmp := wfr_valid_mp hgx).
  case: (hmp) => x' [] /size_of_le hle; rewrite hms /= => hx.
  split.
  + by apply (is_align_no_overflow (Memory.valid_align (write_mem_valid_pointer hw))).
  + by apply: is_align_no_overflow (Memory.valid_align hvp).
  move: hb; rewrite /between !zify.
  assert (hwl := wfg_ofs wf_locals (get_local_pos hx)).
  rewrite (valid_mp_addr hmp) /wptr hms /=; lia.
Qed.

Lemma eq_not_mod_rset_word rmap m0 s1 s2 x mp p ws w mem2:
  valid_state rmap m0 s1 s2 ->  
  Mvar.get (var_region rmap) x = Some mp ->
  mp_s mp = MSstack ->
  between (mp_addr mp) (size_of (vtype x)) p ws ->
  write_mem (emem s2) p ws w = ok mem2 ->
  eq_not_mod m0 (emem s2) -> 
  eq_not_mod m0 mem2. 
Proof.
  move=> hvs hgx hms hb hw heg p1 ws1 hvp.
  rewrite (heg _ _ hvp) //; symmetry; apply: (Memory.writeP_neq hw).
  assert (hmp := wfr_valid_mp hgx).
  case: (hmp) => x' [] /size_of_le hle; rewrite hms /= => hx.
  split.
  + by apply (is_align_no_overflow (Memory.valid_align (write_mem_valid_pointer hw))).
  + by apply: is_align_no_overflow; apply is_align8.
  move: hb; rewrite /between !zify.
  have:= hvp _ _ _ (get_local_pos hx).
  rewrite wunsigned_add; last by have := @ge0_wunsigned _ rsp; lia.
  rewrite (valid_mp_addr hmp) /wptr hms wsize8 /=; lia.
Qed.

Lemma alloc_lvalP rmap r1 r2 v ty m0 (s1 s2: estate) :
  alloc_lval pmap rmap r1 ty = ok r2 -> 
  valid_state rmap m0 s1 s2 -> 
  type_of_val v = ty ->
  forall s1', write_lval gd r1 v s1 = ok s1' ->
  exists s2', write_lval [::] r2.2 v s2 = ok s2' /\ valid_state r2.1 m0 s1' s2'.
Proof.
  move=> ha hvs ?; subst ty.
  case: r1 ha => /=.
  (* Lnone *)
  + move=> vi ty1 [<-] /= s1' /write_noneP [->] h; exists s2; split => //.
    by rewrite /write_none; case: h => [ [? ->]| [-> ->]].

  (* Lvar *)
  + move=> x; case hlx: get_local => [pk | ]; last first.
    + t_xrbindP => ? /check_diffP hnnew <- s1'.
      rewrite /write_var; t_xrbindP => vm1 hvm1 <- /=.
      by apply: set_varP hvm1=> [v' hv <- | hb hv <-]; rewrite /write_var /set_var hv /= ?hb /=;
        eexists;(split;first by reflexivity); apply valid_state_set_var.
    case heq: is_word_type => [ws | //]; move /is_word_typeP : heq => hty.
    case: eqP => htyv //; rewrite /write_var.
    t_xrbindP => -[xi ei] ha rmap2 hsetw <- s1' vm1' hvm1' ?; subst s1' => /=.
    have he1 : sem_pexpr [::] s2 0 >>= to_int = ok 0 by done.
    have [mp [hgetr hins hal ->]] := set_wordP hsetw. 
    have [wx [wi [-> -> /= <- hmpal]]]:= check_mk_addr_ptr hvs he1 hlx hgetr hal ha.
    move: hvm1'; apply set_varP; last by rewrite {1}hty.
    move=> {ha hsetw}; case: x hty hlx hgetr => -[xty xn] xii /= ->.
    set x := {| vtype := sword ws; vname := xn |} => hlx hgetr /= w.
    move=> /(type_of_val_to_pword htyv) [w' [??]] ?; subst v vm1' => /=.
    rewrite truncate_word_u /= wrepr0 GRing.addr0.
    assert (hmp := wfr_valid_mp hgetr).
    have ha := valid_mp_addr hmp; have /= hab:= valid_mp_addr_bound hmp.
    have hmpb := valid_mp_bound hmp; have hmsb:= @ms_bound (mp_s mp).
    have hvp: valid_pointer (emem s2) (mp_addr mp) ws.
    + apply Memory.is_align_valid_pointer => //.
      move=> k hk.
      rewrite /mp_addr -GRing.addrA -wrepr_add.
      apply vs_val_ptr; split; first by apply ge0_wunsigned.
      by apply: Z.le_lt_trans; first apply wunsigned_repr_le; lia.
    have /Memory.writeV -/(_ w') [mem2 hmem2] := hvp.
    rewrite hmem2 /=; eexists;split;first by reflexivity.
    (* valid_state update word *)
    case:(hvs) => vptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm. 
    have hbet: between (mp_addr mp) (size_of (vtype x)) (mp_addr mp) ws.
    + by rewrite /between /x /= !Z.leb_refl.
    constructor => //=.
    + by move=> ???; rewrite (Memory.write_valid _ _ hmem2); apply vptr.
    + by rewrite -(ss_frames (Memory.write_mem_stable hmem2)).
    + move=> y hy; rewrite get_var_neq; first by apply heqvm.
      by move=> heq;move: hy; rewrite -heq hlx.
    + case: (hwfr) => h1 h2 h3; constructor => //=.
      + move=> y mpy v /(check_gvalid_rset_word hins hgetr) [].
        + move=> [ hng heq ?]; subst mpy.
          have -> : y = mk_lvar {|v_var := x; v_info := v_info (gv y) |}.
          + by case: y hng heq => -[yv vi] [] //= _ ->.
          have /= -> // := @get_gvar_eq gd (mk_lvar {| v_var := x; v_info := v_info (gv y) |}) (evm s1) (ok w).
          move=> [<-]; exists w';split;first by subst w.
          by apply: Memory.writeP_eq hmem2.
        move=> [hd hdm hcv]; rewrite get_gvar_neq // => /h2 -/(_ _ hcv) /=.
        by apply: (eq_mp_val_write_disj hvs hgetr) hmem2.
      by apply: wfr_PTR_rset_word hmem2 h3.
    + by apply: (eq_glob_rset_word hvs hgetr) hmem2 heqg.
    by apply: (eq_not_mod_rset_word hvs hgetr) hmem2 hnotm.

  (* Lmem *)
  + move=> ws x e1; t_xrbindP => ? /check_varP hx e1' /(alloc_eP hvs) he1 <-.
    move=> s1' xp ? hgx hxp w1 v1 /he1 he1' hv1 w hvw mem2 hw <- /=.
    have := get_var_kindP hvs hx; rewrite /get_gvar /= => /(_ _ hgx) -> /=.
    rewrite he1' hxp /= hv1 /= hvw /=.
    have hvp1 := write_mem_valid_pointer hw.
    have hvp2: valid_pointer (emem s2) (xp + w1) ws.
    + by apply /Memory.readV; assert (h := vs_eq_mem hvp1); rewrite -h; apply /Memory.readV.
    have /Memory.writeV  -/(_ w) [mem2' hmem2] := hvp2.
    rewrite hmem2 /=; eexists;split;first reflexivity.
    (* valid_state update mem *)
    case:(hvs) => vptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm. 
    have ha1 := Memory.valid_align hvp1.
    have hno1 := is_align_no_overflow ha1.
    constructor => //=.
    + by move=> ???; rewrite (Memory.write_valid _ _ hmem2); apply vptr.
    + by move=> ??; rewrite (Memory.write_valid _ _ hw); apply hdisj.
    + by rewrite -(ss_frames (Memory.write_mem_stable hmem2)).
    + case: (hwfr) => h1 h2 h3; constructor => //=.
      + move=> y mpy vy hcv hgy.
        have hmp := check_gvalid_mp hvs hcv.
        apply: (disjoint_eq_mp_val hmp _ hmem2 (h2 _ _ _ hcv hgy)).
        have hb1 := valid_mp_addr_bound hmp; have hb2 := @ms_bound (mp_s mpy).
        split => //.
        + by rewrite /no_overflow !zify; lia.
        by have:= hdisj _ _ (mp_s mpy) hvp1; lia.
      move=> y mpy hgy.
      have [pk [hgpk hvpk]] := h3 _ _ hgy; exists pk; split => //.
      case: pk hgpk hvpk => //= ofs /get_local_pos_sptr hgpk <-.
      apply: (Memory.writeP_neq hmem2).
      have h := sptr_addr_bound hgpk; split => //.
      + rewrite /no_overflow !zify; lia.
      by have:= hdisj _ _ MSstack hvp1; rewrite /wptr /wptr_size /=; lia.
    + move=> w2 sz; rewrite (Memory.write_valid _ _ hw) => hv.
      by apply: Memory.read_write_any_mem (hw) (hmem2) => //; apply heqg.
    move=> ofs hofs hl; rewrite hnotm //.
    symmetry; apply: (Memory.writeP_neq hmem2).
    split => //.
    + by rewrite /no_overflow zify wsize8; have := wunsigned_range (rsp + wrepr U64 ofs); lia.
    rewrite wsize8 wunsigned_add; last by have := @ge0_wunsigned _ rsp; lia.
    by have:= hdisj _ _ MSstack hvp1; rewrite /wptr /wptr_size /=; lia.
  
  (* Laset *)
  move=> aa ws x e1; t_xrbindP => e1' /(alloc_eP hvs) he1.
  move=> hr2 s1'; apply on_arr_varP => n t hty hxt.
  t_xrbindP => i1 v1 /he1 he1' hi1 w hvw t' htt' vm1 hvm1 ?; subst s1'.
  case hlx: get_local hr2 => [pk | ]; last first.
  + t_xrbindP => ? /check_diffP hnnew <-.
    have /get_var_kindP -/(_ _ hxt) : get_var_kind pmap (mk_lvar x) = ok None.
    + by rewrite /get_var_kind /= hlx.
    rewrite /get_gvar /= => hxt2.
    rewrite he1' /= hi1 hxt2 /= hvw /= htt' /=.
    apply: set_varP hvm1=> [v' hv <- | ]; last by rewrite {1} hty.
    rewrite /set_var hv /=.
    by eexists;(split;first by reflexivity); apply valid_state_set_var. 
  t_xrbindP => mp hc -[xi ei] ha rmap2 hsetw <- /=.
  have {he1} he1 : sem_pexpr [::] s2 e1' >>= to_int = ok i1 by rewrite he1'.
  have [mp' [hgetr hins hal ->]] := set_wordP hsetw. 
  have ? : mp = mp'.
  + by move /check_validP : hc; rewrite hgetr => -[[->]].
  subst mp'.
  have [wx [wi [-> -> /= <- hmpal]]]:= check_mk_addr_ptr hvs he1 hlx hgetr hal ha.
  move: hvm1; apply set_varP; last by rewrite {1}hty.
  move=> {ha hsetw}; case: x hty hlx hxt hc hgetr => -[xty xn] xii /= ->.
  set x := {| vtype := sarr n; vname := xn |} => hlx hxt hc hgetr /= ti [?] ?; subst ti vm1.
  rewrite hvw /=.
  have [hge0 hlen haa] := WArray.set_bound htt'.
  assert (hmp := wfr_valid_mp hgetr).
  have ha := valid_mp_addr hmp; have /= hab:= valid_mp_addr_bound hmp.
  have /= hmpb := valid_mp_bound hmp; have hmsb:= @ms_bound (mp_s mp).
  have hvp: valid_pointer (emem s2) (mp_addr mp + wrepr Uptr (i1 * mk_scale aa ws)) ws.
  + apply Memory.is_align_valid_pointer. 
    + by apply is_align_add => //; apply arr_is_align. 
    move=> k hk; rewrite /mp_addr -!GRing.addrA -!wrepr_add.
    apply vs_val_ptr; split; first by apply ge0_wunsigned.
    by apply: Z.le_lt_trans; first apply wunsigned_repr_le; lia.
  have /Memory.writeV -/(_ w) [mem2 hmem2] := hvp.
  rewrite hmem2 /=; eexists;split;first by reflexivity.
  (* valid_state update array *)
  have hgt0ws := wsize_size_pos ws; have ge0_mps := @ge0_wunsigned _ (wptr (mp_s mp)).
  have heqa : wunsigned (mp_addr mp + wrepr U64 (i1 * mk_scale aa ws)) = 
              wunsigned (mp_addr mp) + i1 * mk_scale aa ws.
  + by apply wunsigned_add; lia.
  case:(hvs) => vptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm. 
  have hbet: between (mp_addr mp) (size_of (vtype x)) (mp_addr mp + wrepr U64 (i1 * mk_scale aa ws)) ws.
  + by rewrite /between /x /= !zify; lia.
  constructor => //=.
  + by move=> ???; rewrite (Memory.write_valid _ _ hmem2); apply vptr.
  + by rewrite -(ss_frames (Memory.write_mem_stable hmem2)).
  + move=> y hy; rewrite get_var_neq; first by apply heqvm.
    by move=> heq;move: hy; rewrite -heq hlx.
  + case: (hwfr) => h1 h2 h3; constructor => //=.
    + move=> y mpy vy /(check_gvalid_rset_word hins hgetr) [].
      + move=> [ hng heq ?]; subst mpy.
        have -> : y = mk_lvar {|v_var := x; v_info := v_info (gv y) |}.
        + by case: y hng heq => -[yv vi] [] //= _ ->.
        set X := (mk_lvar {| v_var := x; v_info := v_info (gv y) |}).
        have /= -> // := @get_gvar_eq gd X (evm s1) (ok (WArray.inject n t')).
        move=> [<-]; eexists (WArray.inject n t');split => //.
        move=> off hoff v0.
        have -> :  WArray.get AAscale U8 (WArray.inject n t') off = WArray.get AAscale U8 t' off.
        + by rewrite /WArray.inject Z.ltb_irrefl.
        rewrite Z.add_comm wrepr_add GRing.addrA -/(mp_addr mp) (WArray.set_get8 off htt') /=.
        have -> /= := Memory.write_read8 (mp_addr mp + wrepr U64 off) hmem2.
        set t1 := (x in (if x then _ else _)).
        set t2 := (x in _ -> (if x then _ else _) = _).
        have <- : t1 = t2.
        + rewrite Bool.eq_iff_eq_true -/(is_true t1) -/(is_true t2) /t1 /t2 !zify.
          by rewrite !(@wunsigned_add _ (mp_addr mp)); lia.
        case:ifPn; rewrite /t1 !zify => hi {t1 t2}.
        + move=> [<-]; do 2 f_equal; rewrite !(@wunsigned_add _ (mp_addr mp)); lia.
        move=> hh; have hcg : check_gvalid rmap X = Some mp.
        + by rewrite /check_gvalid /= hc.
        have /= [t1 [/Varr_inj]]:= h2 _ _ _ hcg hxt.
        move=> [heq1]; rewrite (Eqdep_dec.UIP_dec Pos.eq_dec heq1 erefl) /= => ?; subst t1 => {heq1}.
        by move=> /(_ _ hoff _ hh) <-; rewrite Z.add_comm wrepr_add GRing.addrA -/(mp_addr mp).
      move=> [hd hdm hcv]; rewrite get_gvar_neq // => /h2 -/(_ _ hcv) /=.
      by apply: (eq_mp_val_write_disj hvs hgetr) hmem2.
    by apply: wfr_PTR_rset_word hmem2 h3.
  + by apply: (eq_glob_rset_word hvs hgetr) hmem2 heqg.
  by apply: (eq_not_mod_rset_word hvs hgetr) hmem2 hnotm.
Qed.

Lemma alloc_lvalsP rmap r1 r2 vs ty m0 (s1 s2: estate) :
  alloc_lvals pmap rmap r1 ty = ok r2 -> 
  valid_state rmap m0 s1 s2 -> 
  seq.map type_of_val vs = ty -> 
  forall s1', write_lvals gd s1 r1 vs = ok s1' ->
  exists s2', write_lvals [::] s2 r2.2 vs = ok s2' /\ valid_state r2.1 m0 s1' s2'.
Proof.
  elim: r1 r2 rmap ty vs s1 s2=> //= [|a l IH] r2 rmap [ | ty tys] // [ | v vs] //.
  + move=> s1 s2 [<-] Hvalid _ s1' [] <-; by exists s2; split.
  move=> vs's1 s2; t_xrbindP => -[a' r3] ha [l' r4] /IH hrec <-.
  move=> Hvalid [] hty htys s1' s1'' ha1 hl1.
  have [s2' [hs2' vs2']]:= alloc_lvalP ha Hvalid hty ha1.
  have [s2'' [hs2'' vs2'']]:= hrec _ _ _ vs2' htys _ hl1.
  by exists s2''; split => //=; rewrite hs2'.
Qed.



(*Hypothesis P

Let P' : sprog := 
    {| p_globs := [::];
       p_funcs := SP;
       p_extra := {|
         sp_rip := gm.(stack_alloc.rip); 
         sp_globs := data; 
         sp_stk_id := nrsp |}
    |}. *)

Variable (P' : sprog).
Hypothesis P'_globs : P'.(p_globs) = [::].
Variable (m0:mem).

Let Pi_r s1 (i1:instr_r) s2 :=
  forall rmap1 rmap2 ii1 ii2 i2, alloc_i pmap rmap1 (MkI ii1 i1) = ok (rmap2, MkI ii2 i2) ->
  forall s1', valid_state rmap1 m0 s1 s1' ->
  exists s2', sem_i (sCP:= sCP_stack) P' rip s1' i2 s2' /\ valid_state rmap2 m0 s2 s2'.

Let Pi s1 (i1:instr) s2 :=
  forall rmap1 rmap2 i2, alloc_i pmap rmap1 i1 = ok (rmap2, i2) ->
  forall s1', valid_state rmap1 m0 s1 s1' ->
  exists s2', sem_I (sCP:= sCP_stack) P' rip s1' i2 s2' /\ valid_state rmap2 m0 s2 s2'.

Let Pc s1 (c1:cmd) s2 :=
  forall rmap1 rmap2 c2,  fmapM (alloc_i pmap) rmap1 c1 = ok (rmap2, c2) ->
  forall s1', valid_state rmap1 m0 s1 s1' ->
  exists s2', sem (sCP:= sCP_stack) P' rip s1' c2 s2' /\ valid_state rmap2 m0 s2 s2'.

Let Pfor (i1: var_i) (vs: seq Z) (s1: estate) (c: cmd) (s2: estate) := True.

Let Pfun (m1: mem) (fn: funname) (vargs: seq value) (m2: mem) (vres: seq value) := True.

Local Lemma Hskip : sem_Ind_nil Pc.
Proof.
  move=> s rmap1 rmap2 /= c2 [??] s' hv;subst rmap1 c2.
  exists s'; split => //; exact: Eskip. 
Qed.

Local Lemma Hcons : sem_Ind_cons P ev Pc Pi.
Proof.
  move=> s1 s2 s3 i c _ Hi _ Hc sm1 _sm3 c1 /=;t_xrbindP => -[sm2 i'] hi [sm3 c'] hc /= ?? s1' hv. 
  subst c1 _sm3.
  have [s2' [si hv2]]:= Hi _ _ _ hi _ hv.
  have [s3' [sc hv3]]:= Hc _ _ _ hc _ hv2.
  exists s3'; split => //; apply: Eseq; [exact: si|exact: sc].
Qed.

Local Lemma HmkI : sem_Ind_mkI P ev Pi_r Pi.
Proof.
  move=> ii i s1 s2 _ Hi sm1 sm2 [ii' ir'] ha s1' hv.
  by have [s2' [Hs2'1 Hs2'2]] := Hi _ _ _ _ _ ha _ hv; exists s2'; split.
Qed.
(*
Lemma alloc_assgnP s1 s2 x tag ty e v v' ii1 ii2 i2 sm1 sm2:
  sem_pexpr gd s1 e = ok v -> 
  truncate_val ty v = ok v' -> 
  write_lval gd x v' s1 = ok s2 -> 
  Let ir := alloc_assgn nrsp gm sm1 ii1 x tag ty e in ok (ir.1, MkI ii1 ir.2) = ok (sm2, MkI ii2 i2) ->
  forall s1', valid sm1 s1 s1' → 
   ∃ s2', sem_i (sCP:= sCP_stack) P' rip s1' i2 s2' ∧ valid sm2 s2 s2'.
Proof.
  move=> hv htr Hw; rewrite /alloc_assgn.
  t_xrbindP => -[sm i'] e'; apply: add_iinfoP => he [sm' x'].
  apply: add_iinfoP => ha /= [?] ???? s1' hs1; subst i' sm sm' ii1 i2.
  have [v1 [He' Uvv1]] := alloc_eP he hs1 hv.
  have [v1' htr' Uvv1']:= truncate_value_uincl Uvv1 htr.
  have hty := truncate_val_has_type htr.
  have [s2' [Hw' Hs2']] := alloc_lvalP ha hs1 hty Uvv1' Hw.
  by exists s2'; split=> //;apply: Eassgn;eauto.
Qed.

  Lemma is_arr_typeP ty : is_arr_type ty -> exists n, ty = sarr n.
  Proof. case ty => //;eauto. Qed.

  Lemma is_varP e y: is_var e = Some y -> e = Pvar y.
  Proof. by case e => // ? [->]. Qed.

  Lemma find_gvar_set sm x ap z: 
    find_gvar gm (Mvar.set sm x ap) z = 
      if is_lvar z && (x == gv z) then Some (mp_of_ap ap) else find_gvar gm sm z.
  Proof.
    by rewrite /find_gvar; case: ifP => //= ?; rewrite Mvar.setP; case: ifP.
  Qed.
*)

Lemma is_sarrP ty : reflect (exists n, ty = sarr n) (is_sarr ty).
Proof.
  case: ty => /= [||n|ws]; constructor; try by move => -[].
  by exists n.
Qed.

Lemma get_set_region rmap x mp y :
  Mvar.get (var_region (set rmap x mp)) y = 
  if x == y then Some mp else Mvar.get (var_region rmap) y.
Proof. rewrite /set /= Mvar.setP; case: ifPn => // hne. Qed.

Lemma set_VALID rmap x mp: 
  valid_mp mp (vtype x) -> wfr_VALID rmap -> wfr_VALID (set rmap x mp).    
Proof.
  by move=> hv hV y mpy; rewrite get_set_region; case: eqP => [<- [<-]| _ /hV ].
Qed.

Lemma check_gvalid_set rmap x mp y: 
  check_gvalid (set rmap x mp) y = 
    if (x == (gv y)) && ~~is_glob y then Some mp 
    else check_gvalid rmap y.
Proof.
  rewrite /check_gvalid; case: ifPn => ? /=; first by rewrite andbF.
  rewrite andbT /check_valid get_set_region; case: eqP => [-> | hne].
  + by rewrite /set /= Mmp.setP_eq SvP.add_mem_1.
  case: Mvar.get => // mpy.
  rewrite /set /= Mmp.setP; case: eqP => // <-.
  by rewrite SvD.F.add_neq_b //; case: Mmp.get.
Qed.

Lemma set_VAL rmap x mp v s s': 
  eq_mp_val (vtype x) (emem s') mp (pto_val v) ->
  wfr_VAL rmap s s' -> 
  wfr_VAL (set rmap x mp) (with_vm s (evm s).[x <- ok v]) s'.
Proof.
  move=> hv hV y mpy vy; rewrite check_gvalid_set.
  case: ifPn => [ /andP[]/eqP heq /negP ? [<-]| ].
  + by subst x; rewrite get_gvar_eq /= => [[<-]| ].
  move=> h /hV hc;rewrite get_gvar_neq => [/hc // |/negP hn ].
  by move: h;rewrite hn andbT => /eqP. 
Qed.

Lemma type_of_get_var x vm v: get_var vm x = ok v → subtype (type_of_val v) (vtype x).
Proof.
  rewrite /get_var; apply on_vuP => // v' _ <-; apply subtype_type_of_val.
Qed.

Lemma type_of_get_gvar x gd vm v: get_gvar gd vm x = ok v → subtype (type_of_val v) (vtype (gv x)).
Proof.
  by rewrite /get_gvar; case: ifPn => [ ? /type_of_get_var | ? /type_of_get_global ->].
Qed.

Definition lea_ptr' y ptr ofs := 
  add (Pvar (mk_lvar (with_var y ptr))) (cast_const ofs).

Lemma get_addrP s1 s1' rmap1 rmap2 i2 x dx y:
  valid_state rmap1 m0 s1 s1' ->
  get_addr pmap rmap1 x dx y = ok (rmap2, i2) ->
  exists mp, 
    [/\ check_gvalid rmap1 y = Some mp,
        rmap2 = set rmap1 x mp &
        forall s2', write_lval [::] dx (Vword (mp_addr mp)) s1' = ok s2' ->
                     sem_i P' rip s1' i2 s2'].
Proof.
  move=> hvs; rewrite /get_addr /check_gvalid.   
  case: ifPn => hglob.             
  + t_xrbindP => ofs /get_globalP -> <- <- /=.
    exists {| mp_s := MSglob; mp_ofs := ofs |}.
    split => //= s2' hs; constructor.
    by rewrite /sem_sopn /= P'_globs /get_gvar /= vs_rip /= /sem_sop2 /= !zero_extend_u hs.
  case heq: get_local => [pk | //].         
  rewrite /set_move; t_xrbindP => rmap2' mp hva <- <- <-; rewrite hva.
  case /check_validP : hva => hgmp _.
  assert (h := wfr_ptr hgmp); case: h => pk' [];rewrite heq => -[?] hvp {heq}; subst pk'.
  exists mp; split => // s2' hs .
  case: pk hvp => /= [ofs | p | ofs] h.
  + subst mp; constructor.
    by rewrite /sem_sopn /= P'_globs /get_gvar /= vs_rsp /= /sem_sop2 /= !zero_extend_u hs.
  + by constructor; rewrite /sem_sopn /= P'_globs /get_gvar /= h /= !zero_extend_u hs.
  by constructor; rewrite /sem_sopn /= P'_globs vs_rsp /= !zero_extend_u h /= !zero_extend_u hs.
Qed.

Lemma alloc_array_moveP s1 s2 s1' rmap1 rmap2 x e v v' n i2 : 
  valid_state rmap1 m0 s1 s1' ->
  sem_pexpr gd s1 e = ok v ->
  truncate_val (sarr n) v = ok v' ->
  write_lval gd x v' s1 = ok s2 ->
  alloc_array_move pmap rmap1 x e = ok (rmap2, i2) → 
  ∃ s2' : estate, sem_i P' rip s1' i2 s2' ∧ valid_state rmap2 m0 s2 s2'.
Proof.
  move=> hvs he htr hw.
  rewrite /alloc_array_move.
  case: x hw => //= x.
  rewrite /write_var; t_xrbindP => vm1 hvm1 <- /=.
  have hu := value_uincl_truncate_val htr.
  have /type_of_val_arr := truncate_val_has_type htr.
  case => -[t ?];subst v'.
  + apply: set_varP hvm1.
    + by move=> ? /pof_val_undef_ok. 
    by move=> /is_sboolP h1 h2; elimtype False; move: h2; rewrite h1.
  apply: set_varP hvm1; last first.
  by move=> /is_sboolP h1 h2; elimtype False; move: h2; rewrite h1.
  case: x => -[[]// sx xn] xii /= t' [?] ?; subst t' vm1.
  set x := {|vname := xn|}.
  case: e he => //= y hy.
  have [sy [htyy hsy]]: exists sy, vtype (gv y) = sarr sy /\ n <= sy. 
  + have /= := subtype_trans (value_uincl_subtype hu) (type_of_get_gvar hy) .
    by case: vtype => // => sy /ZleP ?;eauto.
  have [sv [tv ? htv]] := value_uinclE hu; subst v.

  have heqma: forall mp, eq_mp_array (emem s1') mp sy (Varr tv) → 
                   eq_mp_array (emem s1') mp sx (Varr (WArray.inject sx t)).
  + rewrite /eq_mp_array => mp [tv' []] /Varr_inj [?]; subst sv => /= ? hgtv; subst tv'.
     eexists; split;first reflexivity.
     move=> off hoff v0 hget.
     have [hoffsy hgettv]: (off < sy)%Z /\  @WArray.get sy AAscale U8 tv off = ok v0.
     + move: hget; rewrite /WArray.get /CoreMem.read /= /wsize_size Z.mul_1_r /WArray.validr /WArray.validw /=.
       rewrite Z.add_0_r !andbT /CoreMem.uread /= /WArray.uget /WArray.add Z.add_0_r.
       rewrite WArray.zget_inject //; t_xrbindP => ??? /assertP hr /assertP -> /assertP.
       case: ZltP => // hlt hget hdec.  
       have -> /= : (WArray.in_range sy off U8).
       + move: hr;rewrite /WArray.in_range !zify /wsize_size; lia.
       case: htv => _ h; case heq: Mz.get hget hdec => [w | ] //= _.
       by rewrite (h _ _ _ heq); [ move=> <- /=;split => // | ]; lia.
     by apply hgtv => //; lia.

  case hglx : get_local => [[ofs | p | ofs] | //].
  + t_xrbindP => _ /assertP; rewrite is_lvar_is_glob => /negP hngy mpy hcvy.
    move=> _ /assertP -/eqP ???; subst mpy rmap2 i2.
    exists s1';split;first by constructor.
    case: (hvs) => vptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm. 
    constructor => //.
    + move=> x1 hx1; rewrite -heqvm // get_var_neq //.
      by move=> heq;move: hx1;rewrite -heq hglx.
    case: (hwfr) => h1 h2 h3; constructor => //=.
    + by apply: set_VALID => //; exists x; split.
    + apply: set_VAL => //=.
      have : check_gvalid rmap1 y = Some {| mp_s := MSstack; mp_ofs := ofs |}.
      + by move/negP:hngy; rewrite /check_gvalid hcvy => /negbTE ->.
      by move=> /h2 -/(_ _ hy); rewrite htyy /=; apply heqma.
    move=> x1 mp1; rewrite get_set_region; case: eqP => [<- [<-]| _ /h3 //].
    rewrite hglx; move /check_validP: hcvy => [] /h3 [pk] [] ???.
    by exists (Pstack ofs).

  + move=> /get_addrP => -[mp [hcmp ?]]; subst rmap2.
    rewrite /write_lval /write_var /= /set_var.
    assert (hp := wt_rptr hglx) => {hglx}.
    rewrite (var_surj p) hp /=.
    move=> /(_ _ erefl) ?;eexists;split; first by eauto.
    case: (hvs) => vptr hdisj hrip hrsp hf heqvm hwfr heqg hnotm. 
    constructor => //.
    + assert (h:=disj_ptr).
    + 
    + move=> x1 hx1; rewrite -heqvm // get_var_neq //.
      by move=> heq;move: hx1;rewrite -heq hglx.
    case: (hwfr) => h1 h2 h3; constructor => //=.
    + by apply: set_VALID => //; exists x; split.
    + apply: set_VAL => //=.
      have : check_gvalid rmap1 y = Some {| mp_s := MSstack; mp_ofs := ofs |}.
      + by move/negP:hngy; rewrite /check_gvalid hcvy => /negbTE ->.
      by move=> /h2 -/(_ _ hy); rewrite htyy /=; apply heqma.
    move=> x1 mp1; rewrite get_set_region; case: eqP => [<- [<-]| _ /h3 //].
    rewrite hglx; move /check_validP: hcvy => [] /h3 [pk] [] ???.
    by exists (Pstack ofs).
    case: p hp => pty pn.
Search vtype.
Search set_var.
Search write_var.

  get_addrP
Print instr_r.

  + rewrite /get_addr.
   
       

Search g

Search _ check_valid.

hv hV y mpy; rewrite get_set_region; case: eqP => [<- [<-]| _ /hV ].
Print wfr_PTR.
          rewrite /eq_mp_array. => -[tv' []] /Varr_inj [?]. subst sv => /= ? hgtv; subst tv'.
          eexists; split;first reflexivity.
          move=> off hoff v0 hget.
  

          apply hgtv; first admit. 
Set Printing Implicit.
Set Printing Coer
          move: hget; rewrite /WArray.get /CoreMem.read /= /wsize_size Z.mul_1_r /WArray.validr /WArray.validw /=.
          rewrite Z.add_0_r !andbT /CoreMem.uread /= /WArray.uget /WArray.add Z.add_0_r.
          rewrite WArray.zget_inject //; t_xrbindP => ??? /assertP hr /assertP hal /assertP.
          case: ZltP => // hlt hget hdec.       
          have -> : (WArray.in_range sy off U8).
          + move: hr;rewrite /WArray.in_range !zify; lia.
          case:ifP =
            

Search WArray.inject.
          have : off < sy /\ WArray.get AAscale U8 t off = ok v0.
          + move: 
Print WArray.uincl.
          case: (ZltP off sy) => hoffsy.
          + apply hgtv. lia. 
            move: hget; rewrite /WArray.get /CoreMem.read /= /wsize_size Z.mul_1_r /WArray.validr /WArray.validw /=.
            rewrite /CoreMem.uread WArray.zget_inject Z.

Search WArray.inject.



sy < sx 

t : arr n
tv : arr sy

Print subtype.
          have := htv.          
rewrite /WArray.uincl.
Print WArray.inject.
          rewrite /WArray.get /CoreMem.read /= /wsize_size Z.mul_1_r.
          t_xrbindP.
          
Search CoreMem.read.
 hget.

Search WArray.get.
Search WArray.validr. 

          have /= []:= WArray.get_bound hget.
          rewrite /wsize_size.

          have := WArray.get_uget hget. rewrite /WArray.uget.
          Search WArray.uget.
Search eq_mp_val.
Print WArray.uincl.
Search _ value_uincl.

Search WArray.inject.
          have := h2 y.
rewrite /eq_mp_array.
Search eq_mp_val.

        + move=> x1 mp1 v1.

  get_gvar 
Print check_valid.
admit.
move=> ?.

  exists xs, 

 have := h2 x1 mp1 v1; rewrite /check_gvalid.
        case: ifPn => [ hg h /h| hng ]; first by rewrite get_gvar_neq ?hg.
        rewrite /check_valid.
admit.        
      + move=> x1.



        Print check_valid.
Lemma rm_setP x
Print rm_set.        
Print 
Search rm_set.

          + apply h1 => //. by apply /eqP.
          have := h1 _.
        Search _ Mvar.get Mvar.remove.
        case: 
Print get_local.
        Search remove.
Print valid_mp.
exists (mk_lvar {|v_var := x; v_info := xii|}).
Print valid_mp.
Search _ Mvar.get Mvar.set.
Check wfr_PTR_rset_word.
Print rset_word.
      + move=> y mpy v /(check_gvalid_rset_word hins hgetr) [].
        + move=> [ hng heq ?]; subst mpy.
          have -> : y = mk_lvar {|v_var := x; v_info := v_info (gv y) |}.
          + by case: y hng heq => -[yv vi] [] //= _ ->.
          have /= -> // := @get_gvar_eq gd (mk_lvar {| v_var := x; v_info := v_info (gv y) |}) (evm s1) (ok w).
          move=> [<-]; exists w';split;first by subst w.
          by apply: Memory.writeP_eq hmem2.
        move=> [hd hdm hcv]; rewrite get_gvar_neq // => /h2 -/(_ _ hcv) /=.
        by apply: (eq_mp_val_write_disj hvs hgetr) hmem2.
      by apply: wfr_PTR_rset_word hmem2 h3.
    + by apply: (eq_glob_rset_word hvs hgetr) hmem2 heqg.
    by apply: (eq_not_mod_rset_word hvs hgetr) hmem2 hnotm.


Search _ is_lvar.
Print is_Pvar.
Search _ is_Pvar.
Print is_lv_var.
Search _ is_lv_var.
*)
(*
Local Lemma Hassgn : sem_Ind_assgn P Pi_r.
Proof.
  move=> s1 s2 x tag ty e v v' hv htr hw rmap1 rmap2 ii1 ii2 i2 /=.
  t_xrbindP => -[rmap2' i2'] h /= ??? s1' hvs; subst rmap2' ii1 i2'.
  have htyv':= truncate_val_has_type htr.
  case: ifPn h => [/is_sarrP [n ?]| _ ].
  + subst ty; apply: add_iinfoP.


    admit.
  t_xrbindP => e'; apply: add_iinfoP => /(alloc_eP hvs) he [rmap2' x'].
  apply: add_iinfoP => hax /= ??; subst rmap2' i2.
  have [s2' [/= hw' hvs']]:= alloc_lvalP hax hvs htyv' hw.
  exists s2';split => //.
  apply: Eassgn; eauto; rewrite P'_globs; auto.
Qed.
  assert (hx := alloc_lvalP hax).
Check add_iinfoP.

Search add_iinfo.
    case:x hv htr Hw => [??| x|???|????]; try by apply: alloc_assgnP.
(*    case: ifP => hty. last by apply: alloc_assgnP.
    case he : is_var => [y | ]; last by apply: alloc_assgnP.
    case: ifP => hsubty; last by apply: alloc_assgnP.
    case hf : find_gvar => [mp | ]; last by apply: alloc_assgnP.
    move=> hv htr Hw; have [n htyx] := is_arr_typeP hty; have ? := is_varP he; subst e.
    set x' := {| v_var := _ |}.
    t_xrbindP => -[_sm2 _i2] _tt; apply: add_iinfoP=> /check_vfresh_lvalP [hnrsp hnrip] [??] /= ??? s1' hva.
    subst _sm2 ii1 _i2 i2 sm2; have := valid_s hva y. 
    rewrite hf => -[h1 h2].
    set s2' := {| emem := emem s1';
                  evm := (evm s1').[x' <- ok (@Build_pword U64 U64 
                                               (wptr (mp_s mp) + wrepr U64 (mp_ofs mp))
                                               (erefl true))] |}.
    exists s2'; split.
    + case hid: mp_id h1 => [idx | ] /= h1.
      + apply: S.Eassgn => /=;eauto.
        + by rewrite /truncate_val /= zero_extend_u; auto.
        done.
      apply: S.Eopn; rewrite /sem_sopn /= /get_gvar /= (get_vptr hva) /= /s2'. 
      by do 5! f_equal;rewrite !zero_extend_u wrepr0 wrepr1; ssrring.ssring.
    move: Hw; apply rbindP =>vm1 /=; apply: set_varP;rewrite /set_var; last by rewrite {1}htyx.
    move=> t ht ?[?]; subst vm1 s2.
    move: hv; rewrite /= /s2' /x' => {s2' x'}.
    case: x hnrsp hnrip hty htyx hsubty t ht => -[xty xn] xi /= hnrsp hnrip hty htyx hsubty t ht /=.
    subst xty; case: v' htr ht => // n' a'; last first.
    + by rewrite /pof_val /=; case: (n').
    rewrite /truncate_val; t_xrbindP; case: ty => //= n1 yt.
    case: v => //=;last by case.
    move=> ny ty1 /=; rewrite /WArray.cast; case: ifP => // /ZleP hn1 [?].
    move=> /Varr_inj [?]; subst n1 => /= ? [?] hgety; subst yt t a'. 
    have hyty: vtype (gv y) = sarr ny.  
    + move: hgety; rewrite /get_gvar; case: ifP => ?.
      + rewrite /get_var; apply on_vuP => //.
        by case: (gv y) => -[] [] //= p ???? /Varr_inj [?]; subst p. 
      by rewrite /get_global; case: get_global_value => // ?; case: eqP => // <- [->].
    move: hsubty; rewrite hyty /= => /ZleP hsubty.
    case: hva => hd her hdef hvm hrip hrsp htop hfr hs hm hg {h1 he}; split => //=.
    + move=> z /= /Sv_memP hin; rewrite !Fv.setP_neq; first last.
      + by apply /eqP; SvD.fsetdec. + by apply /eqP; SvD.fsetdec.
      by apply: hvm; apply /Sv_memP; SvD.fsetdec.
    + by rewrite get_var_neq // => h; move: hnrip; rewrite h /is_vrip eq_refl.
    + by rewrite get_var_neq // => h; move: hnrsp; rewrite h /is_vrsp eq_refl.
    + move=> z; case heq: find_gvar => [mpz | //]; move: heq.
      rewrite find_gvar_set; case: andP => [ [hlv /eqP heq] [?]| hna].
      + subst mpz => /=; split; first by rewrite /get_var Fv.setP_eq.
        move: h2; rewrite -heq /= hyty => h off hoff.
        have hoff' : 0 <= off ∧ off < ny by lia.
        have [h1 /(_ _ _ hgety) h2]:= h _ hoff'; split => //.
        rewrite /get_gvar hlv -heq /get_var Fv.setP_eq /= => s' a hok. 
        have /Varr_inj [? {hok}]:= ok_inj hok.
        subst s' => /= ? v hv; subst a; apply h2. 
        apply: WArray.uincl_get hv; split => // i vi hi.
        by rewrite WArray.zget_inject //=; case: ifP.
      move=> /find_gvar_keep [hz hdiff] /=.
      have := hs z; rewrite hz => -[hz1 hz2]; split.
      + case: mp_id hdiff hz1 => // id hne.
        by rewrite get_var_neq // => -[eid]; apply hne;rewrite eid.
      case: vtype hz2 => //.
      + move=> p hp off; rewrite get_gvar_neq; first by apply hp.
        by move=> his; apply /negP => he;auto.
      move=> w [hw1 hw2]; split => // v; rewrite get_gvar_neq; first by apply hw2.
      by move=> his; apply /negP => he;auto.
    move=> z mpz; have := hm _ _ hf; rewrite hyty => -[nn [[?]]]; subst nn.
    move=> [hmp1 hmp2 hmp3 hmp4].
    rewrite find_gvar_set;case: andP => [ [hlv /eqP heq] [?]| hna].
    + subst mpz => /=; exists n; rewrite -heq /=; split => //; split => //; first by lia.
      move=> z1 mpz1 sz1;rewrite find_gvar_set;case: andP => [ [hlv1 /eqP heq1] [?]| hna1].
      + by subst mpz1; rewrite /= eq_refl -heq1 /= => ?? [].
      move=> /find_gvar_keep [hz1 hdiff] /= hsz hms. 
      have := hmp4 _ _ _ hz1 hsz hms; case:eqP;last by lia.
      move=> ? h1 [ //| hh1]; have heq1 := h1 (or_intror hh1).
      by move: hh1; rewrite -heq1 hyty.
    move=> /find_gvar_keep [hz1 hdiff].
    have [sz1 [hsz1 [hmpz1 hmpz2 hmpz3 hmpz4]]]:= hm _ _ hz1; exists sz1; split => //; split => //.
    move => s mps ss;rewrite find_gvar_set;case: andP => [ [hlv1 /eqP heq1] [?]| hna1].
    + subst mps => /=; rewrite -heq1 /= => -[?] h1; subst ss.
      have := hmp4 _ _ _ hz1 hsz1; rewrite h1 => /(_ erefl); rewrite eq_sym.
      case: eqP => ?; last lia.
      move=> h [ hh1| //]; have heq2 := h (or_intror hh1).
      by move: hh1; rewrite -heq2 hyty.
    move=> /find_gvar_keep [hh1 hh2 hh3 hh4].
    by apply: hmpz4 hh1 hh3 hh4. *)
  Qed.
  
  Local Lemma Hopn : sem_Ind_opn P Pi_r.
  Proof.
    move => s1 s2 t o xs es.
    rewrite /sem_sopn;t_xrbindP => vs va He Hop Hw sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] es'; apply: add_iinfoP => he [sm4 x']; apply: add_iinfoP => ha /= [??] ??? s1' hv.
    subst i' sm3 sm4 ii1 i2.
    have [va' [He' Uvv']] := (alloc_esP he hv He). 
    have [w' [Hop' Uww']]:= vuincl_exec_opn Uvv' Hop.
    have [s2' [Hw' Hvalid']] := alloc_lvalsP ha hv (sopn_toutP Hop) Uww' Hw.
    exists s2'; split=> //.
    by apply: Eopn;rewrite /sem_sopn He' /= Hop'.
  Qed.

  Lemma valid_incl sm1 sm2 s s' :
    incl sm1 sm2 -> valid sm2 s s' -> valid sm1 s s'.
  Proof.
    rewrite /incl => /andP [] /allP hall 
      /Sv.subset_spec hsub [hd her hdef hvm hrip hrsp htopf hs hm hg].
    have h: forall x mpx, find_gvar gm sm1 x = Some mpx -> find_gvar gm sm2 x = Some mpx.
    + move=> x mpx; rewrite /find_gvar; case: ifP => //.
      case heq: (Mvar.get sm1 (gv x)) => [ap | //].
      have /hall : (v_var (gv x), ap) \in Mvar.elements sm1.(mstk) by apply /Mvar.elementsP.
      by rewrite /incl_alloc_pos /=; case : Mvar.get => // ap' /eqP <-.
    split => //.
    + by move=> x /Sv_memP hin; apply hvm; apply /Sv_memP; SvD.fsetdec.
    + move=> x; have := hs x; case heq : (find_gvar gm sm1 x) => [mp |// ].
      by rewrite (h _ _ heq).
    move=> x mpx /h hf; have [sx [? [??? h1]]]:= hm x mpx hf.
    by exists sx;split => //;split => // y mpy sy /h; apply h1.
  Qed.
    
  Lemma incl_merge_l sm1 sm2 : incl (merge sm1 sm2) sm1.
  Proof.
    rewrite /merge; apply /andP => /=; split; last by apply SvP.inter_subset_1.
    apply /allP => -[x ap] /Mvar.elementsP.
    rewrite Mvar.map2P //= /incl_alloc_pos.
    case: Mvar.get => [ap1| //]; case: Mvar.get => [ap2 | ] //=.
    by case: eqP => [-> | //] [->].
  Qed.

  Lemma incl_merge_r sm1 sm2 : incl (merge sm1 sm2) sm2.
  Proof.
    rewrite /merge; apply /andP => /=; split; last by apply SvP.inter_subset_2.
    apply /allP => -[x ap] /Mvar.elementsP.
    rewrite Mvar.map2P //= /incl_alloc_pos.
    case: Mvar.get => [ap1| //]; case: Mvar.get => [ap2 | ] //=.
    by case: eqP => [-> | //] [->].
  Qed.

  Lemma incl_refl sm : incl sm sm.
  Proof.
    apply /andP; split; last by apply SvP.subset_refl.
    apply /allP => -[x ap] /Mvar.elementsP /= h.
    by rewrite /incl_alloc_pos h.
  Qed.

  Lemma incl_trans sm1 sm2 sm3: incl sm1 sm2 -> incl sm2 sm3 -> incl sm1 sm3.
  Proof.
    move=> /andP [/allP a1 s1] /andP [/allP a2 s2]; apply /andP; split.
    + apply /allP => -[x ap] /a1 /=; rewrite /incl_alloc_pos.
      case heq :  Mvar.get => [ap2| //] /eqP ?;subst ap2.
      by apply: (a2 (x, ap)); apply /Mvar.elementsP.
    apply: SvP.subset_trans s1 s2.
  Qed.

  Local Lemma Hif_true : sem_Ind_if_true P ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] e'; apply: add_iinfoP => he [sm4 c1'] hc1 [sm5 c2'] hc2 /= [??]??? s1' hv.
    subst sm3 i' sm2 ii1 i2.
    have [b [he']]:= alloc_eP he hv Hse.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s2' [Hsem Hvalid']] := Hc _ _ _ hc1 _ hv.
    exists s2'; split; first by apply: Eif_true.
    by apply: valid_incl Hvalid'; apply incl_merge_l.
  Qed.

  Local Lemma Hif_false : sem_Ind_if_false P ev Pc Pi_r.
  Proof.
    move=> s1 s2 e c1 c2 Hse ? Hc sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] e'; apply: add_iinfoP => he [sm4 c1'] hc1 [sm5 c2'] hc2 /= [??]??? s1' hv.
    subst sm3 i' sm2 ii1 i2.
    have [b [he']]:= alloc_eP he hv Hse.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s2' [Hsem Hvalid']] := Hc _ _ _ hc2 _ hv.
    exists s2'; split; first by apply: Eif_false.
    by apply: valid_incl Hvalid'; apply incl_merge_r.
  Qed.

  Lemma loop2P ii check_c2 n sm sm' e' c1' c2': 
    loop2 ii check_c2 n sm = ok (sm', (e', (c1', c2'))) ->
    exists sm1 sm2, incl sm1 sm /\ check_c2 sm1 = ok ((sm', sm2), (e', (c1', c2'))) /\ incl sm1 sm2.
  Proof.
    elim: n sm => //= n hrec sm; t_xrbindP => -[[sm1 sm2] [e1 [c11 c12]]] hc2 /=; case: ifP.
    + move=> hi [] ????;subst.
      by exists sm; exists sm2;split => //; apply incl_refl.
    move=> _ /hrec [sm3 [sm4 [h1 [h2 h3]]]]; exists sm3, sm4; split => //.
    by apply: (incl_trans h1); apply incl_merge_l.
  Qed.

  Local Lemma Hwhile_true : sem_Ind_while_true P ev Pc Pi_r.
  Proof.
    move=> s1 s2 s3 s4 a c1 e c2 _ Hc1 Hv ? Hc2 ? Hwhile sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] [sm4 [e' [c1' c2']]] /loop2P [sm5 [sm6 [hincl1 []]]].
    t_xrbindP => -[sm7 c11] hc1 /= e1; apply: add_iinfoP => he [sm8 c22] /= hc2 ????? hincl2 [??]???.
    subst i2 ii1 sm3 sm4 i' sm7 sm8 e1 c11 c22 => s1' /(valid_incl hincl1) hv. 
    have [s2' [hs1 hv2]]:= Hc1 _ _ _ hc1 _ hv.
    have [b [he']] := alloc_eP he hv2 Hv.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    have [s3' [hs2 /(valid_incl hincl2) hv3]]:= Hc2 _ _ _ hc2 _ hv2.
    have /= := Hwhile sm5 sm2 ii2 ii2 (Cwhile a c1' e' c2').
    rewrite Loop.nbP /= hc1 /= he /= hc2 /= hincl2 /= => /(_ erefl _ hv3) [s4'] [hs3 hv4].
    by exists s4';split => //; apply: Ewhile_true; eauto.
  Qed.

  Local Lemma Hwhile_false : sem_Ind_while_false P ev Pc Pi_r.
  Proof.
    move=> s1 s2 a c1 e c2 _ Hc1 Hv sm1 sm2 ii1 ii2 i2 /=.
    t_xrbindP => -[sm3 i'] [sm4 [e' [c1' c2']]] /loop2P [sm5 [sm6 [hincl1 []]]].
    t_xrbindP => -[sm7 c11] hc1 /= e1; apply: add_iinfoP => he [sm8 c22] /= hc2 ????? hincl2 [??]???.
    subst i2 ii1 sm3 sm4 i' sm7 sm8 e1 c11 c22 => s1' /(valid_incl hincl1) hv. 
    have [s2' [hs1 hv2]]:= Hc1 _ _ _ hc1 _ hv.
    have [b [he']] := alloc_eP he hv2 Hv.
    move=> /value_uincl_bool /= -/(_ _ erefl) [_ ?];subst b.
    by exists s2';split => //; apply: Ewhile_false; eauto.
  Qed.

  Local Lemma Hfor : sem_Ind_for P ev Pi_r Pfor.
  Proof. by []. Qed.

  Local Lemma Hfor_nil : sem_Ind_for_nil Pfor.
  Proof. by []. Qed.

  Local Lemma Hfor_cons : sem_Ind_for_cons P ev Pc Pfor.
  Proof. by []. Qed.

  Local Lemma Hcall : sem_Ind_call P ev Pi_r Pfun.
  Proof. by []. Qed.

  Local Lemma Hproc : sem_Ind_proc P ev Pc Pfun.
  Proof. by []. Qed.

  Lemma check_cP s1 c s2: sem P ev s1 c s2 -> Pc s1 c s2.
  Proof.
    apply (@sem_Ind _ _ _ P ev Pc Pi_r Pi Pfor Pfun Hskip Hcons HmkI Hassgn Hopn
             Hif_true Hif_false Hwhile_true Hwhile_false Hfor Hfor_nil Hfor_cons Hcall Hproc).
  Qed.
End PROOF.

Definition valid_map1 (m:Mvar.t Z) (size:Z) :=
  forall x px, Mvar.get m x = Some px -> 
     exists sx, size_of (vtype x) = ok sx /\
     [/\ 0 <= px, px + sx <= size,
      aligned_for (vtype x) px &
         forall y py sy, x != y -> 
           Mvar.get m y = Some py -> size_of (vtype y) = ok sy ->
           px + sx <= py \/ py + sy <= px].

Lemma init_mapP l sz m :
  init_map sz l = ok m -> 
  valid_map1 m sz.
Proof.
  rewrite /init_map.
  set f1 := (f in foldM f _ _ ).
  set g := (g in foldM _ _ _ >>= g). 
  have : forall p p',
    foldM f1 p l = ok p' -> 
    valid_map1 p.1 p.2 -> 0 <= p.2 ->
    (forall y py sy, Mvar.get p.1 y = Some py ->
        size_of (vtype y) = ok sy -> py + sy <= p.2) ->
    (p.2 <= p'.2 /\ valid_map1 p'.1 p'.2).
  + elim:l => [|[v pn] l Hrec] p p'//=.
    + by move=>[] <- ???;split=>//;omega.
    case:ifPn=> //= /Z.leb_le Hle.
    case: ifP => // Hal.
    case Hs : size_of=> [svp|]//= /Hrec /= {Hrec}Hrec H2 H3 H4. 
    have Hpos := size_of_pos Hs.
    case:Hrec.
    + move=> x px;rewrite Mvar.setP;case:ifPn => /eqP Heq.
      + move=> [] ?;subst;exists svp;split=>//;split => //.
        + omega. + omega.
        move=> y py sy Hne.
        by rewrite Mvar.setP_neq // => /H4 H /H ?;omega.
      move=> /H2 [sx] [Hsx] [] Hle0 Hpx Hal' Hy;exists sx;split=>//;split=>//.
      + omega.
      move=> y py sy Hne;rewrite Mvar.setP;case:eqP=> [?[]? |].
      + subst;rewrite Hs => -[] ?;subst; omega.
      by move=> Hney;apply Hy.
    + omega.
    + move=> y py sy;rewrite Mvar.setP;case:eqP=> [?[]?|].
      + subst;rewrite Hs => -[] ->;omega.
      move=> ? /H4 H /H ?;omega.
    move=> Hle2 H';split=>//;first by omega.
  move=> H;case Heq : foldM => [p'|]//=.
  case: (H _ _ Heq)=> //= Hp' Hv.
  rewrite /g; case:ifP => //= /Z.leb_le Hp [<-].
  move=> x px Hx.
  case :(Hv x px Hx) => //= sx [] Hsx [] H1 H2 H3 H4.
  by exists sx;split=>//;split=>//;omega.
Qed.

Lemma getfun_alloc nrsp oracle oracle_g (P:uprog) (SP:sprog) :
  alloc_prog nrsp oracle oracle_g P = ok SP ->
  exists lg mglob, 
    [/\ init_map (Z.of_nat (size SP.(p_extra).(sp_globs))) lg = ok mglob,
        check_globs (p_globs P) mglob SP.(p_extra).(sp_globs) &
        forall fn fd,
        get_fundef (p_funcs P) fn = Some fd ->
        exists fd', 
           get_fundef SP.(p_funcs) fn = Some fd' /\
           alloc_fd nrsp SP.(p_extra).(sp_rip) mglob oracle (fn, fd) = ok (fn,fd')].
Proof.
  rewrite /alloc_prog.
  case: (oracle_g P) => -[data rip] l.
  t_xrbindP => mglob; apply: add_err_msgP => heq.
  case heq1: check_globs => //; t_xrbindP => sfd hm ?; subst SP => /=.
  exists l, mglob;split => //.
  elim: (p_funcs P) sfd hm => [ | [fn1 fd1] fs hrec sfd] //=.
  t_xrbindP => -[fn2 fd2] fd2' H [??]; subst fn2 fd2'.
  move => sfds /hrec hm ?; subst sfd.
  move=> fn3 fd3 /=.
  case: eqP => ? .
  + by move=> [?]; subst fn3 fd3; exists fd2; rewrite H.
  by move=> /hm.
Qed.
*)
Definition extend_mem (m1:mem) (m2:mem) (rip:pointer) (data: seq u8) :=
  let glob_size := Z.of_nat (size data) in
  [/\ wunsigned rip + glob_size <= wbase U64 /\
      (forall ofs s, is_align (rip + wrepr _ ofs)%R s = is_align (wrepr _ ofs) s), 
      (forall w sz, validw m1 w sz -> read m1 w sz = read m2 w sz),
      (forall w sz, validw m1 w sz ->
          ~((wunsigned rip <? wunsigned w + wsize_size sz) && (wunsigned w <? wunsigned rip + glob_size))),
      (forall w sz, validw m2 w sz = 
         validw m1 w sz || (between rip glob_size w sz && is_align w sz)) &
      (forall i, 
         0 <= i < glob_size ->
         read m2 (rip + wrepr U64 i)%R U8 = ok (nth (wrepr U8 0) data (Z.to_nat i)))].
(*
Lemma all_In (T:Type) (P: T -> bool) (l:seq T) x :
  all P l ->
  List.In x l -> P x.
Proof. by elim: l => //= x' l hi /andP [] hp /hi h -[<- | /h]. Qed.

Lemma valid_top (P : uprog) nrsp (stk_size : Z) (rsp : u64) (glob_size : Z) 
         (rip : u64) (data : seq u8) (gm : gmap) (sm : smap) 
         s1 s2 :
         valid P nrsp stk_size rsp glob_size rip data gm sm s1 s2 ->
 top_stack (emem s2) = rsp.
Proof.
  by move=> /valid_top_frame; rewrite /top_stack; case: frames => //= ?? [->].
Qed.

Lemma alloc_prog_stk_id nrsp oracle oracle_g P SP :
  alloc_prog nrsp oracle oracle_g P = ok SP →
  sp_stk_id SP.(p_extra) = nrsp.
Proof.
  by rewrite /alloc_prog; case: (oracle_g _) => - []; t_xrbindP => ?????; case: ifP => // _; t_xrbindP => ?? <-.
Qed.

Lemma alloc_fdP nrsp oracle oracle_g (P:uprog) SP fn fd fd':
  alloc_prog nrsp oracle oracle_g P = ok SP ->
  get_fundef (p_funcs P) fn = Some fd ->
  get_fundef (p_funcs SP) fn = Some fd' ->
  forall ev m1 va m1' vr rip, 
    sem_call P ev m1 fn va m1' vr ->
    forall m2, extend_mem m1 m2 rip SP.(p_extra).(sp_globs) ->
    (exists p, alloc_stack m2 (sf_stk_sz fd'.(f_extra)) = ok p) ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      extend_mem m1' m2' rip SP.(p_extra).(sp_globs) /\
      sem_call (sCP:=sCP_stack) SP rip m2 fn va m2' vr'.
Proof.
  move=> hap get Sget. 
  have ? := alloc_prog_stk_id hap; subst nrsp.
  have [lg [mglob [higlob hcheck hf]]]:= getfun_alloc hap.
  have [fd1 [] {hf}]:= hf _ _ get.
  rewrite Sget => -[?];subst fd1.
  rewrite /alloc_fd.
  case: (oracle (fn, fd)) => -[stk_size lv] ptrreg_of_reg .
  t_xrbindP => fd1 mstk; rewrite /add_err_fun.
  case histk : init_map => [mstk1 | //] [?]; subst mstk1.
  set gm := {| rip := _ |}; set sm0 := {| mstk := _ |}.
  move=> sm1; case hfold : foldM => [sm1' | //] [?]; subst sm1'.
  move=> [sme c]; apply: add_finfoP => hc /=.
  case: andP => // -[] hneq hres [?] ?;subst fd1 fd' => /=.
  move=> ev m1 vargs m1' vres rip hcall m2 hm2 [m2s ha].
  pose glob_size := Z.of_nat (size (sp_globs SP.(p_extra))).
  have Hstk: ptr_ok (top_stack m2s) stk_size.
  + by move: ha=> /Memory.alloc_stackP [].
  have Hglob: ptr_ok rip (Z.of_nat (size (sp_globs SP.(p_extra)))).
  + by rewrite /ptr_ok; case hm2.

  have hv : valid_map gm sm0 stk_size glob_size.
  + rewrite /sm0 => x mpx; rewrite /find_gvar /=; case:ifP => his.
    + rewrite Mvar.mapP; case heq: Mvar.get => [ofsx | // ] [?]; subst mpx.
      have [sx [h1 [h2 h3 h4 h5]]] := init_mapP histk heq.
      exists sx;split => //; split => //.
      move=> y mpy sy; case: ifP => his'.
      + rewrite  Mvar.mapP; case heq': Mvar.get => [ofsy | // ] [?]; subst mpy => /=.
        move=> hsy _; case: (v_var (gv x) =P gv y).
        + by move => heq1; move: heq'; rewrite -heq1 heq => -[->]; rewrite eq_refl.
        move=> /eqP => heq1; have := h5 _ _ _ heq1 heq' hsy; case: eqP => //.
        by have := size_of_pos h1; have := size_of_pos hsy; lia.
      by case: Mvar.get => [ofsy | //] [<-].
    case heq: Mvar.get => [ofsx' | // ] [?]; subst mpx => /=.
    have [sx [h1 [h2 h3 h4 h5]]] := init_mapP higlob heq.
    exists sx;split => //; split => //.
    move=> y mpy sy; case: ifP => his'.
    + by rewrite  Mvar.mapP; case heq': Mvar.get => [ofsy | // ] [?]; subst mpy.
    case heq': Mvar.get => [ofsy | //] [?] hsy _; subst mpy => /=.
    case: (v_var (gv x) =P gv y).
    + by move => heq1; move: heq'; rewrite -heq1 heq => -[->]; rewrite eq_refl.
    move=> /eqP => heq1; have := h5 _ _ _ heq1 heq' hsy; case: eqP => //.
    by have := size_of_pos h1; have := size_of_pos hsy; lia.
  have heq_init :
    init_state (semCallParams := sCP_stack) {| sf_stk_sz := stk_size; sf_extra := ptrreg_of_reg |} 
                          SP.(p_extra) rip {| emem := m2; evm := vmap0 |} = 
    ok {| emem := m2s; evm := vmap0.[vrsp (sp_stk_id SP.(p_extra)) <- ok (pword_of_word (top_stack m2s))]
                                             .[vrip gm <- ok (pword_of_word rip)] |}.
  + rewrite /init_state /= /init_stk_state ha /= /with_vm //=. 
    f_equal; f_equal; f_equal; [f_equal | ]; f_equal; rewrite /pword_of_word;
    f_equal; apply (Eqdep_dec.UIP_dec Bool.bool_dec).
    
  have hvalid : 
    valid P (sp_stk_id SP.(p_extra)) stk_size (top_stack m2s) 
            (Z.of_nat (size (sp_globs SP.(p_extra)))) rip (sp_globs SP.(p_extra)) gm sm0
              {| emem := m1; evm := vmap0 |}
              {| emem := m2s; evm := vmap0.[vrsp (sp_stk_id SP.(p_extra)) <- ok (pword_of_word (top_stack m2s))]
                                             .[vrip gm <- ok (pword_of_word rip)] |}.
  + case: hm2 => halign2 hread_eq hdisj hval hglob.
    have [hin hread_eqs hvals hal hdisjs htopf]:= Memory.alloc_stackP ha.
    constructor => //=.
    + move=> w sz hw; split; last by apply hdisj.
      by have := hdisjs w sz; rewrite hval hw /= => /(_ erefl) -[] h; apply /negP /nandP;
        [left|right];apply /ZltP; lia.
    + by move=> w sz hw; rewrite (hread_eq _ _ hw) hread_eqs // hval hw.
    + by move=> w sz; rewrite hvals hval -orbA (orbC (_ && _)) orbA.
(*    + by move=> x hnin hnrsp hnrip;rewrite !Fv.setP_neq // eq_sym. *)
    + by rewrite /get_var Fv.setP_eq.
    + rewrite /get_var Fv.setP_neq ? Fv.setP_eq //.
      by apply/eqP => -[k]; move/eqP: hneq; rewrite k.
    + by rewrite htopf. 
    + move=> x; rewrite /find_gvar.
      case: ifP => his. 
      + rewrite Mvar.mapP; case heq: Mvar.get => [ofs /=| //];split => //.
        have := init_mapP histk heq. 
        case Htype: (vtype (gv x))=> [| |n| sz] // [sx /= [[?] [h1 h2 h3 h4]]]; subst sx.
        + move=> off hoff; rewrite hvals; split.
          + apply /orP; right; rewrite is_align8 andbT.
            rewrite /between wsize8 /ptr_size /wptr /= (wunsigned_rsp_add Hstk); [ | nia | nia ].
            by apply/andP; split; apply/ZleP; nia.
          move=> s' a; rewrite /get_gvar his /get_var Fv.get0 /on_vu /pundef_addr Htype /= => hok.
          by have /Varr_inj [e ?]:= ok_inj hok; subst s' a; rewrite WArray.get0.
        split.
        + rewrite hvals; apply /orP; right.
          have heq2 : v_var (gv x) = {| vtype := sword sz; vname := vname (gv x) |}.
          + by case: (v_var (gv x)) Htype => /= ?? ->.
          rewrite heq2 in heq. have /(_ sz (vname (gv x)) ofs):= valid_get_w Hstk Hglob hv. 
          by rewrite /sm0 /= Mvar.mapP heq /= /wptr /= => /(_ erefl).
        by move=> ?;rewrite /get_gvar his /get_var Fv.get0 /on_vu /pundef_addr Htype.
      rewrite /gm /=; case heq: Mvar.get => [ofs /=| //]; split => //.
      have := init_mapP higlob heq. 
      case Htype: (vtype (gv x))=> [| |n| sz] // [sx /= [[?] [h1 h2 h3 h4]]]; subst sx.
      + move=> off hoff; rewrite hvals.
        have hvalid : valid_pointer m2 (wptr (top_stack m2s) rip MSglob + wrepr U64 (off + ofs)) U8.
        + rewrite hval; apply /orP; right; rewrite is_align8 andbT.
          rewrite /between wsize8 /ptr_size /wptr (wunsigned_rip_add Hglob).
          + by apply/andP; split; apply/ZleP; nia.
          + nia.
          by move: (size _) hoff h2 h1; clear=> *;lia. 
        split; first by rewrite hvalid.
        move=> s' a; rewrite /get_gvar his /get_global /get_global_value.
        case heq1 : xseq.assoc => [ []//= | //]; case: eqP => //.
(*
        rewrite Htype => -[?] heq2; subst n'; have /Varr_inj [e ?] := ok_inj heq2; subst n a => /=.
        have := all_In hcheck (xseq.assoc_mem' heq1).
        rewrite /check_glob /= heq => /andP [hle /allP hall] v hget. 
        have := hall (Z.to_nat off); rewrite mem_iota /= Z2Nat.id; last by lia.
        rewrite hget.
        match goal with |- (?A -> _) -> _ => have hh: A end.
        + by apply /ltP; case: hoff => ? /Z2Nat.inj_lt;apply.
        move=> /(_ hh) {hh} /eqP <-.
        rewrite /wptr -hread_eqs;last by move: hvalid; rewrite /wptr /=.
        rewrite hglob; last by lia. 
        rewrite Z.add_comm Z2Nat.z2nD;first last.
        + by apply /lezP;rewrite -ssrring.z0E;lia.
        + by apply /lezP;rewrite -ssrring.z0E;lia. 
        by rewrite -nth_drop wrepr0. *)
      rewrite /valid_ptr_word /get_gvar /wptr his.
      have hvalid : valid_pointer m2 (rip + wrepr U64 ofs) sz.
      + rewrite hval; apply /orP; right.
        case: halign2 => hh1 hh2; rewrite /between hh2 h3 andbT.
        rewrite (wunsigned_rip_add Hglob) //.
        + apply /andP;split; apply /ZleP;lia.
        move: (size _) (@wsize_size_pos sz) h2 => *; lia. 
      rewrite hvals hvalid;split => // v. 
      rewrite -hread_eqs // /get_global /get_global_value Htype.
      case heq1 : xseq.assoc => [[ sz' w] //= | //]; case: eqP => // -[?] [?]; subst sz' v.
      exists w => //; rewrite Memory.readP /CoreMem.read.
      have := validr_valid_pointer m2 (rip + wrepr U64 ofs)%R sz.
      rewrite hvalid => /is_okP => -[? ->] /=.
      have := all_In hcheck (xseq.assoc_mem' heq1).
Opaque Z.to_nat.
      rewrite /check_glob heq /= => /andP [hh1 /eqP hh2];subst w.
      f_equal; f_equal.
      rewrite /CoreMem.uread; apply: (@eq_from_nth _ (wrepr U8 0)).
      have hw := @le0_wsize_size sz.
      + rewrite size_map size_ziota size_take size_drop.
        case: ifPn => // /ltP; rewrite Nat2Z.inj_lt Z2Nat.id // Nat2Z.n2zB; last first. 
        rewrite -(Nat2Z.id (size _)); apply /leP; rewrite -Z2Nat.inj_le; lia.
        rewrite -subZE Z2Nat.id // => hh. 
        have -> : (wsize_size sz) = Z.of_nat (size (sp_globs SP.(p_extra))) - ofs.
        + by move:(size _) h2 hh => *; lia.
        by rewrite Z2Nat.inj_sub // Nat2Z.id.
      move=> i; rewrite size_map size_ziota => hi.
      rewrite (nth_map 0) ?size_ziota // nth_take // nth_drop nth_ziota // Memory.addP /=.
      rewrite -GRing.addrA -wrepr_add.
      move /ltP: hi; rewrite Nat2Z.inj_lt Z2Nat.id // => hi.
      have : 0 <= ofs + Z.of_nat i ∧ ofs + Z.of_nat i < Z.of_nat (size (sp_globs SP.(p_extra))).
      + by move:(size _) h2 => *; lia.
      move=> /hglob; rewrite Memory.readP /CoreMem.read CoreMem.uread8_get. 
      t_xrbindP => ?? ->; rewrite Z2Nat.inj_add //; last by apply Zle_0_nat.
      by rewrite Nat2Z.id addP.
    move=> i [hi1 hi2]; rewrite -hread_eqs; first by apply hglob.
    rewrite hval is_align8 andbT;apply /orP;right.
    apply /andP;rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP; lia.
Transparent Z.to_nat.
  inversion_clear hcall.
  case: H1 (* init_state ... *) => ?;subst s0.
  move: H;rewrite get => -[?];subst f.
  have uvargs0 : List.Forall2 value_uincl vargs0 vargs0.
  + by apply List_Forall2_refl.
  have [s1' [hwargs hvalid2 ]] := check_lvarsP hvalid hfold uvargs0 H2.
  have hdisj : 0 < stk_size -> 0 < Z.of_nat (size (sp_globs SP.(p_extra))) ->
       ((wunsigned (top_stack m2s) + stk_size <=? wunsigned rip)
                || (wunsigned rip + Z.of_nat (size (sp_globs SP.(p_extra))) <=? wunsigned (top_stack m2s))).
  + case: hm2 =>  _ _ _ hvm2 _ hss hsg. 
    have [_ _ _ _ hh _]:= Memory.alloc_stackP ha.
    have /hh : valid_pointer m2 rip U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between Z.leb_refl /= wsize8; apply /ZleP. 
      by move: (size _) hsg => *;lia.
    have /hh : valid_pointer m2 (rip + wrepr Uptr (Z.of_nat (size (sp_globs SP.(p_extra))) - 1)) U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between (wunsigned_rip_add Hglob); [ | lia | lia]. 
      by rewrite wsize8; apply /andP; split; apply /ZleP; by move: (size _) hsg => *; lia.
    rewrite wsize8 (wunsigned_rip_add Hglob); [ | lia | lia]. 
    move=> a1 a2;apply /orP.
    rewrite /is_true !Z.leb_le. 
    case: a1; first by lia.
    case: a2; last by lia.
    move=> h_1 h_2.
    have u1 : stk_size < Z.of_nat (size (sp_globs SP.(p_extra))) by lia.
    have /hh : valid_pointer m2 (top_stack m2s) U8.
    + rewrite hvm2 is_align8 andbT;apply /orP;right.
      rewrite /between wsize8; apply /andP.
      move: (size _) h_1 h_2 => *; split; apply /ZleP; lia.
    by rewrite wsize8; lia.   
  have [s3 [hssem hvalid3]] := check_cP (P:= P) SP.(p_funcs) Hstk Hglob hdisj H3 hc hvalid2.
  have [vres1 [H1' uincl1]]:= check_varsP hres (valid_vm hvalid3) H4.
  have [vres2 htr uincl2]:= mapM2_truncate_val H5 uincl1.
  exists (free_stack (emem s3) stk_size), vres2.
  split => //; split.
  + have /Memory.free_stackP [h1 h2 h3 h4 (* h5 *)]: 
     omap snd (ohead (frames(emem s3))) = Some stk_size.
    + by rewrite (valid_top_frame hvalid3).
    have [u1 u2 u3 u4 u5] := hm2.
    have vdisj: forall w sz, valid_pointer m1' w sz ->  disjoint_zrange (top_stack m2s) stk_size w (wsize_size sz).
    + subst m1'; move=> w sz hw; have [ /negP /andP] := valid_disj hvalid3 hw.
      rewrite {1 2}/is_true !Z.ltb_lt => ??; split.
      + by apply /ZleP; case: Hstk.
      + by apply is_align_no_overflow; apply (Memory.valid_align hw).
      lia.
    subst m1';split => //.
    + move=> w sz hw.
      rewrite (valid_eq hvalid3) // h1 // h2 (valid_def hvalid3) /= hw /=; split=> //.
      by rewrite (valid_top hvalid3); apply vdisj.
    + by move=> w sz /(valid_disj hvalid3) [].
    + move=> w sz. 
      apply Bool.eq_iff_eq_true; have := h2 w sz.
      rewrite {1}/is_true => ->.
      rewrite (valid_def hvalid3) /= (valid_top hvalid3); split.
      + move=> [] /orP [].
        + move=> /orP [-> //| ].
          move=> /andP [] /andP [] /ZleP ? /ZleP ?? [???].
          by have := wsize_size_pos sz;lia.
        by move=> /andP [-> ->] /=;rewrite orbT.         
      move=> /orP [ hw | /andP [hb hal]]. 
      + by rewrite hw /=;split => //; apply: vdisj.
      rewrite hb hal !orbT;split => //; split.
      + by apply /ZleP; case: Hstk.
      + by apply is_align_no_overflow.
      have : valid_pointer m2 w sz by rewrite u4 hb hal /= orbT.
      have [_ _ _ _ h _]:= Memory.alloc_stackP ha.
      by move=> /h; lia.
    move=> i [hi1 hi2].
    rewrite -h1.
    + by rewrite (valid_glob hvalid3).
    rewrite h2 (valid_top hvalid3) (valid_def hvalid3) is_align8 !andbT; split.
    + apply /orP;right; apply /andP.
      rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP.
      lia. move: hi1 hi2; rewrite /h4; move: (size _) => *;lia.
    split.
    + by apply /ZleP; case: Hstk.
    + by apply is_align_no_overflow; apply is_align8.
    have :  valid_pointer m2 (rip + wrepr U64 i) U8.
    + rewrite u4 is_align8 andbT; apply /orP;right.
      by apply /andP; rewrite (wunsigned_rip_add Hglob) // wsize8;split;apply /ZleP;lia.
    have [_ _ _ _ h _]:= Memory.alloc_stackP ha.
    by move=> /h;lia.
  econstructor;eauto.
  move: hap hssem => /=; rewrite /alloc_prog.
  by case: oracle_g => -[???]; t_xrbindP => ??; case:ifP => // ?; t_xrbindP => ?? <-.
Qed.
*)

Definition alloc_ok (SP:sprog) fn m2 :=
  forall fd, get_fundef (p_funcs SP) fn = Some fd ->
  allocatable_stack m2 fd.(f_extra).(sf_stk_max).

Lemma alloc_progP nrip data oracle_g oracle (P: uprog) (SP: sprog) fn:
  alloc_prog nrip data oracle_g oracle P = ok SP ->
  forall ev m1 va m1' vr rip, 
    sem_call (sCP := sCP_unit) P ev m1 fn va m1' vr ->
    forall m2, extend_mem m1 m2 rip SP.(p_extra).(sp_globs) ->
    alloc_ok SP fn m2 ->
    exists m2' vr',
      List.Forall2 value_uincl vr vr' /\
      extend_mem m1' m2' rip SP.(p_extra).(sp_globs) /\
      sem_call (sCP := sCP_stack) SP rip m2 fn va m2' vr'.
Proof.
Admitted.
(*
  move=> Hcheck ev m1 va m1' vr rip hsem m2 he ha.
  have [fd hget]: exists fd, get_fundef (p_funcs P) fn = Some fd.
  + by case: hsem=> ??? fd *;exists fd.
  have [lg [mglob [higlob hcheck hf]]]:= getfun_alloc Hcheck.
  have [fd' [hgetS ?]]:= hf _ _ hget.
  by apply: (alloc_fdP Hcheck hget hgetS hsem he (ha _ hgetS)).
Qed.
*)