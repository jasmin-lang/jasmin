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
Require Import Coq.Logic.Eqdep_dec.
Require Import strings word utils gen_map type var expr low_memory sem.
Require Import constant_prop compiler_util allocation byteset.
Require Import ZArith.
Import x86_variables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Definition size_of (t:stype) :=
  match t with
  | sword sz => wsize_size sz
  | sarr n   => Zpos n
  | sbool | sint => 0%Z
  end.

Local
Definition cerror {A} msg :=
  @cerror (Cerr_stk_alloc msg) A.

Local
Definition cferror {A} fn msg :=
  @Error _ A (Ferr_fun fn (Cerr_stk_alloc msg)).

Definition mem_space := var.

Record mem_pos := 
  { mp_s : var; 
    mp_p : var; 
    mp_align : wsize;             (* the alignment of the corresponding region *)
    mp_writable : bool;           (* the region is writable or not             *)
  }.

Definition mem_pos_beq (mp1 mp2:mem_pos) := 
  [&& mp1.(mp_s)        == mp2.(mp_s), 
      mp1.(mp_p)        == mp2.(mp_p), 
      mp1.(mp_align)    == mp2.(mp_align) &
      mp1.(mp_writable) == mp2.(mp_writable)].

Definition mem_pos_same (mp1 mp2:mem_pos) := 
  (mp1.(mp_s) == mp2.(mp_s)).

Lemma mem_pos_axiom : Equality.axiom mem_pos_beq.
Proof.
  rewrite /mem_pos_beq => -[xs1 xp1 xa1 xw1] [xs2 xp2 xa2 xw2].
  by apply:(iffP and4P) => /= [[/eqP -> /eqP -> /eqP -> /eqP ->] | [-> -> -> ->]].
Qed.

Definition mem_pos_eqMixin     := Equality.Mixin mem_pos_axiom.
Canonical  mem_pos_eqType      := Eval hnf in EqType mem_pos mem_pos_eqMixin.

Module CmpMp.

  Definition t := [eqType of mem_pos].

  Definition cmp (mp1 mp2: t) := 
    Lex (bool_cmp mp1.(mp_writable) mp2.(mp_writable))
     (Lex (wsize_cmp mp1.(mp_align) mp2.(mp_align))
         (Lex (var_cmp mp1.(mp_s) mp2.(mp_s))
              (var_cmp mp1.(mp_p) mp2.(mp_p)))).

  Instance cmpO : Cmp cmp.
  Proof.
    constructor => [x y | y x z c | [????] [????]]; rewrite /cmp !Lex_lex.
    + by repeat (apply lex_sym; first by apply cmp_sym); apply cmp_sym.
    + by repeat (apply lex_trans=> /=; first by apply cmp_ctrans); apply cmp_ctrans.
    move=> /lex_eq [] /= h1 /lex_eq [] /= h2 /lex_eq [] /= h3 h4.
    by rewrite (cmp_eq h1) (cmp_eq h2) (cmp_eq h3) (cmp_eq h4).
  Qed.

End CmpMp.

Module Mmp :=  Mmake CmpMp.

(* ------------------------------------------------------------------ *)
Record sub_mp := {
  smp_ofs : Z;
  smp_len : Z;
}.

Scheme Equality for sub_mp.

Lemma sub_mp_eq_axiom : Equality.axiom sub_mp_beq.
Proof.
  move=> x y;apply:(iffP idP).
  + by apply: internal_sub_mp_dec_bl.
  by apply: internal_sub_mp_dec_lb.
Qed.

Definition sub_mp_eqMixin := Equality.Mixin sub_mp_eq_axiom.
Canonical sub_mp_eqType := EqType sub_mp sub_mp_eqMixin.

Module CmpSub.

  Definition t := [eqType of sub_mp].

  Definition cmp (sub1 sub2: t) := 
    Lex (Z.compare sub1.(smp_ofs) sub2.(smp_ofs))
        (Z.compare sub1.(smp_len) sub2.(smp_len)).

  Instance cmpO : Cmp cmp.
  Proof.
    constructor => [x y | y x z c | [??] [??]]; rewrite /cmp !Lex_lex.
    + by apply lex_sym; apply cmp_sym.
    + by apply lex_trans=> /=; apply cmp_ctrans.
    move=> /lex_eq [] /= h1 h2.
    by rewrite (cmp_eq h1) (cmp_eq h2).
  Qed.

End CmpSub.

Module Msmp := Mmake (CmpSub).
Module Ssmp := Smake (CmpSub).
 
Definition disjoint_sub_mp smp1 smp2 := 
  (((smp1.(smp_ofs) + smp1.(smp_len))%Z <= smp2.(smp_ofs)) || 
   ((smp2.(smp_ofs) + smp2.(smp_len))%Z <= smp1.(smp_ofs)))%CMP.

(* ------------------------------------------------------------------ *)
Record mem_pos_sub := {
    mps_mp : mem_pos;
    mps_sub: sub_mp;
  }.

Definition mem_pos_sub_beq mps1 mps2 := 
  (mps1.(mps_mp) == mps2.(mps_mp)) && (mps1.(mps_sub) == mps2.(mps_sub)).

Lemma mem_pos_sub_eq_axiom : Equality.axiom mem_pos_sub_beq.
Proof.
  rewrite /mem_pos_sub_beq => -[mp1 sub1] [mp2 sub2].
  by apply:(iffP andP) => /= [[/eqP -> /eqP ->] | [-> ->]].
Qed.

Definition mem_pos_sub_eqMixin := Equality.Mixin mem_pos_sub_eq_axiom.
Canonical mem_pos_sub_eqType := EqType mem_pos_sub mem_pos_sub_eqMixin.

Module CmpMps.
  Definition t := [eqType of mem_pos_sub].

  Definition cmp (mps1 mps2: t) := 
    Lex (CmpMp.cmp mps1.(mps_mp) mps2.(mps_mp))
        (CmpSub.cmp mps1.(mps_sub) mps2.(mps_sub)).

  Instance cmpO : Cmp cmp.
  Proof.
    constructor => [x y | y x z c | [??] [??]]; rewrite /cmp !Lex_lex.
    + by apply lex_sym; apply cmp_sym.
    + by apply lex_trans=> /=; apply cmp_ctrans.
    move=> /lex_eq [] /= h1 h2.
    by rewrite (cmp_eq h1) (cmp_eq h2).
  Qed.

End CmpMps.

Module Mmps := Mmake(CmpMps).
Module Smps := Smake(CmpMps).

(* ------------------------------------------------------------------ *)
Variant ptr_kind_init :=
| PIstack  of var & sub_mp
| PIglob   of var & sub_mp
| PIregptr of var
| PIstkptr of var & sub_mp & var.

Variant ptr_kind :=
| Pstack  of var & Z & wsize & sub_mp
| Pglob   of var & Z & wsize & sub_mp
| Pregptr of var
| Pstkptr of var & Z & wsize & sub_mp & var.

Record param_info := { 
  pp_ptr      : var;
  pp_writable : bool;
  pp_align    : wsize;
}.

Record pos_map := {
  vrip    : var;
  vrsp    : var;
  globals : Mvar.t (Z * wsize);
  locals  : Mvar.t ptr_kind;
  vnew    : Sv.t;
}.

Definition check_align mps ws :=
  Let _ := assert (ws <= mps.(mps_mp).(mp_align))%CMP
                  (Cerr_stk_alloc "unaligned offset") in
  assert (Z.land mps.(mps_sub).(smp_ofs) (wsize_size ws - 1) == 0)%Z
               (Cerr_stk_alloc "unaligned sub offset").

Definition writable mp := 
  assert mp.(mp_writable)
   (Cerr_stk_alloc "Cannot write a constant pointer").

Module Region.

Definition bytes_map := Mvar.t ByteSet.t.

Definition sub_map := Msmp.t bytes_map.

Record regions := {
  var_region : Mvar.t mem_pos_sub;  (* The region where the value is initialy stored            *)
  region_var : Mmp.t  sub_map;  (* The set of source variables whose value is in the region *)
}.

Definition empty_bytes_map := Mvar.empty ByteSet.t.

Definition empty_sub_map := Msmp.empty bytes_map.

Definition empty := {|
  var_region := Mvar.empty _;
  region_var := Mmp.empty sub_map;
|}.

Definition get_mps (rmap : regions) (x:var) := 
  match Mvar.get rmap.(var_region) x with
  | Some mps => ok mps
  | None => cerror "no associated region"
  end.

Definition get_sub_map mp rmap := 
  odflt empty_sub_map (Mmp.get rmap.(region_var) mp).

Definition get_bytes_map sub sub_map := 
  odflt empty_bytes_map (Msmp.get sub_map sub). 

Definition get_bytes x bytes_map := 
  odflt ByteSet.empty (Mvar.get bytes_map x).

Definition interval_of_sub sub := 
  {| imin := sub.(smp_ofs); imax := sub.(smp_ofs) + sub.(smp_len) |}.
 
Definition sub_ofs sub ofs len := 
  match ofs with
  | None => sub
  | Some ofs => {| smp_ofs := sub.(smp_ofs) + ofs; smp_len := len |}
  end.
 
Definition interval_ofs sub ofs len := 
  interval_of_sub (sub_ofs sub ofs len).

Definition check_valid (rmap:regions) (x:var) ofs len := 
  Let mps := get_mps rmap x in
  let sm := get_sub_map mps.(mps_mp) rmap in
  let bm := get_bytes_map mps.(mps_sub) sm in
  let bytes := get_bytes x bm in 
  let sub_ofs  := sub_ofs mps.(mps_sub) ofs len in
  let isub_ofs := interval_of_sub sub_ofs in 
  Let _   := assert (ByteSet.mem bytes isub_ofs) 
                    (Cerr_stk_alloc "check_valid: the region is partial") in
  ok {| mps_mp := mps.(mps_mp); mps_sub := sub_ofs |}.

Definition clear_bytes i (x:var) bytes := 
  let bytes := ByteSet.remove bytes i in
  if ByteSet.is_empty bytes then None else Some bytes.

Definition clear_bytes_map sub i sub' bm := 
  if disjoint_sub_mp sub sub' then Some bm
  else 
    let bm := Mvar.filter_map (clear_bytes i) bm in
    if Mvar.is_empty bm then None else Some bm.

Definition clear_sub_map sub sm := 
  let i := interval_of_sub sub in
  Msmp.filter_map (clear_bytes_map sub i) sm.

Definition set_stack_ptr rmap x rsp align ofs x' := 
  let mp := {| mp_s := x; mp_p := rsp; mp_align := align; mp_writable := true |} in
  let sub := {| smp_ofs := ofs; smp_len := wsize_size Uptr |} in
  let i := interval_of_sub sub in
  let sm := get_sub_map mp rmap in
  (* clear all bytes correspondint to sub *) 
  let sm := clear_sub_map sub sm in
  let bm := get_bytes_map sub sm in
  let bm := Mvar.set bm x' (ByteSet.full i) in
  let sm := Msmp.set sm sub bm in
  {| var_region := rmap.(var_region);
     region_var := Mmp.set rmap.(region_var) mp sm |}.

Definition check_stack_ptr rmap x rsp align ofs x' := 
  let mp := {| mp_s := x; mp_p := rsp; mp_align := align; mp_writable := true |} in
  let sub := {| smp_ofs := ofs; smp_len := wsize_size Uptr |} in
  let i := interval_of_sub sub in
  let sm := get_sub_map mp rmap in
  let bm := get_bytes_map sub sm in
  let bytes := get_bytes x' bm in 
  Let _   := assert (ByteSet.mem bytes i) 
                    (Cerr_stk_alloc "check_stack_ptr: the region is partial") in
  ok tt.

Definition set_mps rmap x mps :=
  let sub := mps.(mps_sub) in
  let i := interval_of_sub sub in
  let sm := get_sub_map mps.(mps_mp) rmap in
  (* clear all bytes correspondint to sub *) 
  let sm := clear_sub_map sub sm in
  let bm := get_bytes_map sub sm in
  let bm := Mvar.set bm x (ByteSet.full i) in
  let sm := Msmp.set sm sub bm in
  {| var_region := Mvar.set rmap.(var_region) x mps;
     region_var := Mmp.set rmap.(region_var) mps.(mps_mp) sm |}.

(* Precondition size_of x = ws && length mps.mps_sub = wsize_size ws *)
Definition set_word rmap x mps ws :=
  Let _ := writable mps.(mps_mp) in
  Let _ := check_align mps ws in
  ok (set_mps rmap x mps).

Definition set_arr_word rmap x ofs ws :=
  let len := wsize_size ws in
  Let mps := get_mps rmap x in
  let mp  := mps.(mps_mp) in
  Let _ := writable mp in
  Let _ := check_align mps ws in
  let sub  := mps.(mps_sub) in
  let sub1 := sub_ofs sub ofs len in
  let i    := interval_of_sub sub1 in
  let sm := get_sub_map mps.(mps_mp) rmap in
  let bm := get_bytes_map sub sm in
  let bytes := ByteSet.add i (get_bytes x bm) in
  (* clear all bytes correspondint to sub1 *)
  let sm := clear_sub_map sub1 sm in
  (* set the bytes *)
  let bm := get_bytes_map sub sm in
  let bm := Mvar.set bm x bytes in 
  let sm := Msmp.set sm sub bm in
  ok {| var_region := rmap.(var_region); 
        region_var := Mmp.set rmap.(region_var) mps.(mps_mp) sm |}.

Definition set_arr_call rmap x mps := set_mps rmap x mps.

Definition set_arr_sub rmap x ofs len mps_from := 
  Let mps := get_mps rmap x in
  let sub := mps.(mps_sub) in
  let sub_ofs := {| smp_ofs := sub.(smp_ofs) + ofs; smp_len := len |} in
  let sm := get_sub_map mps.(mps_mp) rmap in
  let bm := get_bytes_map sub sm in
  let bytes := get_bytes x bm in
  Let _ := assert (mem_pos_same mps.(mps_mp) mps_from.(mps_mp))
                  (Cerr_stk_alloc "set array: source and destination are not equal") in
  Let _ := assert (sub_ofs == mps_from.(mps_sub))
                  (Cerr_stk_alloc "set array: sub are not equal") in
  let bm := Mvar.set bm x (ByteSet.add (interval_of_sub sub_ofs) bytes) in
  let sm := Msmp.set sm sub bm in
  ok {| var_region := rmap.(var_region); 
     region_var := Mmp.set rmap.(region_var) mps.(mps_mp) sm |}.
 
Definition set_move rmap x mps := 
  let sub := mps.(mps_sub) in
  let i := interval_of_sub sub  in
  let sm := get_sub_map mps.(mps_mp) rmap in
  let bm := get_bytes_map sub sm in
  let bm := Mvar.set bm x (ByteSet.full i) in
  let sm := Msmp.set sm sub bm in
  {| var_region := Mvar.set rmap.(var_region) x mps;
     region_var := Mmp.set rmap.(region_var) mps.(mps_mp) sm |}.

Definition set_arr_init rmap x mps := set_move rmap x mps.

Definition set_full rmap x mp := 
  let len := size_of x.(vtype) in
  let sub := {| smp_ofs := 0;  smp_len := len |} in
  let mps := {| mps_mp  := mp; mps_sub := sub |} in
  set_move rmap x mps.

Definition incl_bytes_map (sub: sub_mp) (bm1 bm2: bytes_map) := 
  Mvar.incl (fun x => ByteSet.subset) bm1 bm2.

Definition incl_sub_map (mp:mem_pos) (sm1 sm2: sub_map) :=
  Msmp.incl incl_bytes_map sm1 sm2.

Definition incl (r1 r2:regions) := 
  Mvar.incl (fun x mp1 mp2 => mp1 == mp2) r1.(var_region) r2.(var_region) &&
  Mmp.incl incl_sub_map r1.(region_var) r2.(region_var).

Definition merge_bytes (x:var) (bytes1 bytes2: option ByteSet.t) := 
  match bytes1, bytes2 with
  | Some bytes1, Some bytes2 => 
    let bytes := ByteSet.inter bytes1 bytes2 in
    if ByteSet.is_empty bytes then None
    else Some bytes
  | _, _ => None
  end.

Definition merge_bytes_map (sub:sub_mp) (bm1 bm2: option bytes_map) :=
  match bm1, bm2 with
  | Some bm1, Some bm2 => 
    let bm := Mvar.map2 merge_bytes bm1 bm2 in
    if Mvar.is_empty bm then None
    else Some bm
  | _, _ => None
  end.

Definition merge_sub_map (mp:mem_pos) (sm1 sm2: option sub_map) :=
  match sm1, sm2 with
  | Some sm1, Some sm2 =>
    let sm := Msmp.map2 merge_bytes_map sm1 sm2 in
    if Msmp.is_empty sm then None
    else Some sm
  | _, _ => None
  end.

Definition merge (r1 r2:regions) := 
  {| var_region := 
       Mvar.map2 (fun _ omp1 omp2 =>
        match omp1, omp2 with
        | Some mp1, Some mp2 => if mp1 == mp2 then omp1 else None
        | _, _ => None
        end) r1.(var_region) r2.(var_region);
     region_var := Mmp.map2 merge_sub_map r1.(region_var) r2.(region_var) |}.
  
End Region.

Import Region.

Definition mul := Papp2 (Omul (Op_w Uptr)).
Definition add := Papp2 (Oadd (Op_w Uptr)).

Definition cast_word e := 
  match e with
  | Papp1 (Oint_of_word U64) e1 => e1
  | _  => cast_ptr e
  end.

Definition mk_ofs aa ws e1 ofs := 
  let sz := mk_scale aa ws in
  if is_const e1 is Some i then 
    cast_const (i * sz + ofs)%Z
  else 
    add (mul (cast_const sz) (cast_word e1)) (cast_const ofs).

Definition mk_ofsi aa ws e1 := 
  if is_const e1 is Some i then Some (i * (mk_scale aa ws))%Z
  else None.

Section Section.

Variables (pmap:pos_map).

Section ALLOC_E.

Variables (rmap: regions).

Definition get_global (x:var) := 
  match Mvar.get pmap.(globals) x with
  | None => cerror "unallocated global variable: please report"
  | Some z => ok z
  end.

Definition get_local (x:var) := Mvar.get pmap.(locals) x.

Definition check_diff (x:var) :=
  if Sv.mem x pmap.(vnew) then cerror "the code write new variables, please report"
  else ok tt.

Definition check_var (x:var) := 
  match get_local x with
  | None => ok tt
  | Some _ => cerror "not a reg variable"
  end.

Inductive vptr_kind := 
  | VKglob of Z * wsize
  | VKptr  of ptr_kind.

Definition var_kind := option vptr_kind.

Definition with_var xi x := 
  {| v_var := x; v_info := xi.(v_info) |}.

Definition mk_addr_ptr x aa ws (pk:ptr_kind) (e1:pexpr) := 
  match pk with
  | Pstack _ z _ sub => ok (with_var x pmap.(vrsp), mk_ofs aa ws e1 (z + sub.(smp_ofs)))
  | Pglob  _ z _ sub => ok (with_var x pmap.(vrip), mk_ofs aa ws e1 (z + sub.(smp_ofs)))
  | Pregptr p        => ok (with_var x p,    mk_ofs aa ws e1 0)
  | Pstkptr _ _ _ _ _ => cerror "stack pointer in expression"
  end.

Definition mk_addr x aa ws (pk:vptr_kind) (e1:pexpr) := 
  match pk with
  | VKglob zws => ok (with_var x pmap.(vrip), mk_ofs aa ws e1 zws.1)
  | VKptr pk => mk_addr_ptr x aa ws pk e1
  end.
 
Definition get_var_kind x :=
  let xv := x.(gv) in
  if is_glob x then
    Let z := get_global xv in
    ok (Some (VKglob z))
  else 
    ok (omap VKptr (get_local xv)).

Definition mp_glob x (ofs_align: Z * wsize) :=
  {| mp_s := x; mp_p := pmap.(vrip); mp_align := ofs_align.2; mp_writable := false |}.

Definition check_vpk_word rmap x vpk ws :=
  Let mps :=
    match vpk with
    | VKglob z =>
      let mp  := mp_glob x z in
      let sub := {| smp_ofs := 0; smp_len := wsize_size ws |} in
      ok {| mps_mp := mp; mps_sub := sub |}
    | VKptr pk => 
      check_valid rmap x (Some 0%Z) (wsize_size ws)
    end in
  check_align mps ws.

Fixpoint alloc_e (e:pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e
  | Pvar   x =>
    let xv := x.(gv) in
    Let vk := get_var_kind x in
    match vk with
    | None => ok e
    | Some vpk => 
      if is_word_type (vtype xv) is Some ws then
        Let _ := check_vpk_word rmap xv vpk ws in
        Let pofs := mk_addr xv AAdirect ws vpk (Pconst 0) in
        ok (Pload ws pofs.1 pofs.2)
      else cerror "not a word variable in expression, please report"
    end

  | Pget aa ws x e1 =>
    let xv := x.(gv) in
    Let e1 := alloc_e e1 in
    Let vk := get_var_kind x in
    match vk with
    | None => ok (Pget aa ws x e1)
    | Some vpk => 
      Let _ := check_vpk_word rmap xv vpk ws in
      Let pofs := mk_addr xv aa ws vpk e1 in
      ok (Pload ws pofs.1 pofs.2)
    end             
  | Psub aa ws len x e1 =>
    cerror "Psub"

  | Pload ws x e1 =>
    Let _ := check_var x in
    Let e1 := alloc_e e1 in
    ok (Pload ws x e1)

  | Papp1 o e1 =>
    Let e1 := alloc_e e1 in
    ok (Papp1 o e1)
   
  | Papp2 o e1 e2 =>
    Let e1 := alloc_e e1 in
    Let e2 := alloc_e e2 in
    ok (Papp2 o e1 e2)

  | PappN o es => 
    Let es := mapM alloc_e es in
    ok (PappN o es)  

  | Pif t e e1 e2 =>
    Let e := alloc_e e in
    Let e1 := alloc_e e1 in
    Let e2 := alloc_e e2 in
    ok (Pif t e e1 e2)
  end.

  Definition alloc_es := mapM alloc_e.
 
End ALLOC_E.

Definition mps_stack x rsp align sub :=
  let mp := {| mp_s := x; mp_p := rsp; mp_align := align; mp_writable := true |} in
  {| mps_mp := mp; mps_sub := sub |}.

Definition mps_pk pk :=
  match pk with
  | Pstack x ofs align sub => ok (mps_stack x pmap.(vrsp) align sub)
  | _                => cerror "not a pointer to stack: please report"
  end.

Definition alloc_lval (rmap: regions) (r:lval) ty := 
  match r with
  | Lnone _ _ => ok (rmap, r)

  | Lvar x =>
    match get_local x with 
    | None => Let _ := check_diff x in ok (rmap, r)
    | Some pk => 
      if is_word_type (vtype x) is Some ws then 
        if ty == sword ws then 
          Let pofs := mk_addr_ptr x AAdirect ws pk (Pconst 0) in
          Let mps  := mps_pk pk in
          let r := Lmem ws pofs.1 pofs.2 in
          Let rmap := Region.set_word rmap x mps ws in
          ok (rmap, r)
        else cerror "invalid type for assignment"
      else cerror "not a word variable in assignment"
    end

  | Laset aa ws x e1 =>
    Let e1 := alloc_e rmap e1 in
    match get_local x with
    | None => Let _ := check_diff x in ok (rmap, Laset aa ws x e1)
    | Some pk => 
      let ofs := mk_ofsi aa ws e1 in 
      Let rmap := set_arr_word rmap x ofs ws in
      Let pofs := mk_addr_ptr x aa ws pk e1 in
      let r := Lmem ws pofs.1 pofs.2 in
      ok (rmap, r)
    end   
  | Lasub aa ws len x e1 =>
    cerror "Lasub"
  | Lmem ws x e1 =>
    Let _ := check_var x in
    Let e1 := alloc_e rmap e1 in
    ok (rmap, Lmem ws x e1)
  end.

Definition nop := Copn [::] AT_none Onop [::]. 

Definition lea_ptr x y ofs := 
  Copn [::x] AT_none (Ox86 (LEA Uptr)) [:: add y (cast_const ofs)].

Definition mov_ptr x y :=
  Copn [:: x] AT_none (Ox86 (MOV Uptr)) [::y].

Inductive mov_kind := 
  | MK_LEA 
  | MK_MOV.

Definition mov_ofs x mk y ofs := 
  if mk is MK_LEA then lea_ptr x y ofs 
  else
    if ofs == 0%Z then mov_ptr x y else lea_ptr x y ofs.

Definition is_nop is_spilling rmap x mpy : bool :=
  if is_spilling then
    if Mvar.get rmap.(var_region) x is Some mpx then mpx == mpy
    else false
  else false.

Definition get_addr is_spilling rmap x dx mpy mk y ofs := 
  let ir := 
    if is_nop is_spilling rmap x mpy then nop
    else mov_ofs dx mk y ofs in
  let rmap := Region.set_move rmap x mpy in
  (rmap, ir).

Definition get_ofs_sub aa ws e1 := 
  match mk_ofsi aa ws e1 with
  | None     => cerror "cannot take/set a subarray on a unknown starting position" 
  | Some ofs => ok ofs
  end.

Definition get_Lvar_sub lv := 
  match lv with
  | Lvar x => ok (x, None)
  | Lasub aa ws len x e1 =>
    Let ofs := get_ofs_sub aa ws e1 in
    ok (x, Some (ofs, arr_size ws len))
  | _      => cerror "variable/subarray excepted : 1"
  end.

Definition get_Pvar_sub e := 
  match e with
  | Pvar x => ok (x, None)
  | Psub aa ws len x e1 =>
    Let ofs := get_ofs_sub aa ws e1 in
    ok (x, Some (ofs, arr_size ws len))
  | _      => cerror "variable/subarray excepted : 2" 
  end.

(* Precondition is_sarr ty *)
Definition alloc_array_move rmap r e :=
  Let xsub := get_Lvar_sub r in
  Let ysub := get_Pvar_sub e in
  let '(x,subx) := xsub in
  let '(y,suby) := ysub in

  Let mpyl := 
    let vy := y.(gv) in
    Let vk := get_var_kind y in
    let (ofs, len) := 
      match suby with
      | None => (0%Z, size_of vy.(vtype))
      | Some p => p
      end in
    match vk with
    | None => cerror "alloc_array_move"
    | Some (VKglob (ofsy, ws)) =>
      let mpy := 
        {| mps_mp := mp_glob vy (ofsy, ws); mps_sub := {| smp_ofs := ofs; smp_len := len |} |} in
      ok (mpy, MK_LEA, Plvar (with_var vy pmap.(vrip)), (ofsy + ofs)%Z)
    | Some (VKptr pk) =>
      Let mpy := Region.check_valid rmap vy (Some ofs) len in
      Let mklofs := 
        match pk with
        | Pstack _ ofsy _ sub => 
          ok (MK_MOV, Plvar (with_var vy pmap.(vrsp)), (ofsy + sub.(smp_ofs) + ofs)%Z)
        | Pglob  _ ofsy _ sub => 
          ok (MK_LEA, Plvar (with_var vy pmap.(vrip)), (ofsy + sub.(smp_ofs) + ofs)%Z)
        | Pregptr p           => 
          ok (MK_MOV, Plvar (with_var vy p), ofs)
        | Pstkptr slot ofsy ws sub x' => 
          Let _ := Region.check_stack_ptr rmap slot pmap.(vrsp) ws sub.(smp_ofs) x' in
          ok (MK_MOV, Pload Uptr (with_var vy pmap.(vrsp)) (cast_const ofsy), ofs)
        end in
      let '(mk, l, ofs) := mklofs in
      ok (mpy, mk, l, ofs) 
     end in
  let '(mpy, mk, ey, ofs) := mpyl in
  match subx with
  | None =>
    match get_local (v_var x) with
    | None    => cerror "register array remains" 
    | Some pk => 
      match pk with
      | Pstack x' _ _ subx =>
        Let _  := assert (is_lvar y)
                         (Cerr_stk_alloc "invalid move: global to stack") in 
        Let _  := assert ((x' == mpy.(mps_mp).(mp_s)) && (subx == mpy.(mps_sub)))
                         (Cerr_stk_alloc "invalid source 1") in
        let rmap := Region.set_move rmap x mpy in
        ok (rmap, nop)
      | Pglob x' _ _ subx => 
        Let _  := assert ((x' == mpy.(mps_mp).(mp_s)) && (mpy.(mps_mp).(mp_p) == pmap.(vrip))
                                                      && (subx == mpy.(mps_sub)))
                         (Cerr_stk_alloc "invalid source 2") in
        let rmap := Region.set_move rmap x mpy in
        ok (rmap, nop)
      | Pregptr p =>
        ok (get_addr false rmap x (Lvar (with_var x p)) mpy mk ey ofs)
      | Pstkptr slot z ws sub x' =>
        let: (rmap, ir) :=
          get_addr true rmap x (Lmem Uptr (with_var x pmap.(vrsp)) (cast_ptr z)) mpy mk ey ofs in
        ok (Region.set_stack_ptr rmap slot pmap.(vrsp) ws sub.(smp_ofs) x', ir)
      end
    end
  | Some (ofs, len) =>
    match get_local (v_var x) with
    | None   => cerror "register array remains 2"
    | Some _ => 
      Let rmap := Region.set_arr_sub rmap x ofs len mpy in
      ok (rmap, nop)
    end
  end.

Definition is_array_init e := 
  match e with
  | Parr_init _ => true
  | _ => false
  end.

Definition alloc_array_move_init rmap r e :=
  if is_array_init e then
    Let xsub := get_Lvar_sub r in
    let '(x,subx) := xsub in
    let (ofs, len) := 
      match subx with
      | None => (0%Z, size_of (v_var x).(vtype))
      | Some p => p
      end in
    Let mps := 
      match get_local (v_var x) with
      | None    => cerror "register array remains" 
      | Some pk => 
        match pk with
        | Pstack x' _ ws sub =>
          let sub := {| smp_ofs := sub.(smp_ofs) + ofs; smp_len := len |} in
          ok (mps_stack x' pmap.(vrsp) ws sub)
        | Pglob x' _ ws sub =>
          cerror "array init glob"
        | _ => 
          Let mps := get_mps rmap x in
          let sub := {| smp_ofs := mps.(mps_sub).(smp_ofs) + ofs; smp_len := len |} in
          ok {| mps_mp := mps.(mps_mp); mps_sub := sub |}
        end
      end in
    let rmap := Region.set_arr_init rmap x mps in
    ok (rmap, nop)
  else alloc_array_move rmap r e.
 
Definition bad_lval_number := Cerr_stk_alloc "invalid number of lval".

Definition alloc_lvals rmap rs tys := 
  fmapM2 bad_lval_number alloc_lval rmap rs tys.

Section LOOP.

 Variable ii:instr_info.

 Variable check_c2 : regions -> ciexec ((regions * regions) * (pexpr * (seq instr * seq instr)) ).

 Fixpoint loop2 (n:nat) (m:regions) := 
    match n with
    | O => cierror ii (Cerr_Loop "stack_alloc")
    | S n =>
      Let m' := check_c2 m in
      if incl m m'.1.2 then ok (m'.1.1, m'.2)
      else loop2 n (merge m m'.1.2)
    end.

End LOOP.

Record stk_alloc_oracle_t :=
  { sao_align : wsize 
  ; sao_size: Z
  ; sao_params : seq (option param_info)  (* Allocation of pointer params *)
  ; sao_return : seq (option nat)         (* Where to find the param input region *)
  ; sao_slots : seq (var * wsize * Z)  
  ; sao_alloc: seq (var * ptr_kind_init)   (* Allocation of local variables without params, and stk ptr *)
  ; sao_to_save: seq (var * Z)
  ; sao_rsp: saved_stack
  ; sao_return_address: return_address_location
  }.

Section PROG.

Context (local_alloc: funname -> stk_alloc_oracle_t).

Definition get_Pvar e := 
  match e with
  | Pvar x => ok x
  | _      => cerror "get_Pvar: variable excepted" 
  end.

Definition alloc_call_arg rmap (sao_param: option param_info) (e:pexpr) := 
  Let x := get_Pvar e in
  Let _ := assert (~~is_glob x) 
                  (Cerr_stk_alloc "global variable in argument of a call") in
  let xv := gv x in
  match sao_param, get_local xv with
  | None, None =>  
    ok (None, Pvar x)
  | None, Some _ => cerror "argument not a reg" 
  | Some pi, Some (Pregptr p) => 
    Let mps := Region.check_valid rmap xv (Some 0%Z) (size_of xv.(vtype))in
    Let _  := if pi.(pp_writable) then writable mps.(mps_mp) else ok tt in
    Let _  := check_align mps pi.(pp_align) in
    ok (Some (pi.(pp_writable),mps), Pvar (mk_lvar (with_var xv p)))
  | Some _, _ => cerror "the argument should be a reg ptr" 
  end.

Definition disj_mps mps1 mps2 :=
  ~~(mem_pos_same mps1.(mps_mp) mps2.(mps_mp)) || 
  disjoint_sub_mp mps1.(mps_sub) mps2.(mps_sub).

Fixpoint check_all_disj (notwritables writables:seq mem_pos_sub) (mps:seq (option (bool * mem_pos_sub) * pexpr)) := 
  match mps with
  | [::] => true
  | (None, _) :: mps => check_all_disj notwritables writables mps
  | (Some (writable, mp), _) :: mps => 
    if all (disj_mps mp) writables then 
      if writable then 
        if all (disj_mps mp) notwritables then 
          check_all_disj notwritables (mp::writables) mps
        else false 
      else check_all_disj (mp::notwritables) writables mps
    else false 
  end.

Definition alloc_call_args rmap (sao_params: seq (option param_info)) (es:seq pexpr) := 
  Let es  := mapM2 (Cerr_stk_alloc "bad params info:please report") (alloc_call_arg rmap) sao_params es in
  Let _ := assert (check_all_disj [::] [::] es) 
           (Cerr_stk_alloc "some writable reg ptr are not disjoints") in
  ok es.

Definition check_lval_reg_call (r:lval) := 
  match r with
  | Lnone _ _ => ok tt
  | Lvar x =>
    match get_local x with 
    | None   => Let _ := check_diff x in ok tt
    | Some _ => cerror "call result should be stored in reg"
    end
  | Laset aa ws x e1 => cerror "array assignement in lval of a call"
  | Lasub aa ws len x e1 => cerror "sub array assignement in lval of a call"
  | Lmem ws x e1     => cerror "call result should be stored in reg"
  end.

Definition check_is_Lvar r (x:var) :=
  match r with
  | Lvar x' => x == x' 
  | _       => false 
  end.

Definition get_regptr (x:var_i) := 
  match get_local x with
  | Some (Pregptr p) => ok (with_var x p)
  | _ => cerror "variable should be a reg ptr" 
  end.

Definition get_Lvar lv := 
  match lv with
  | Lvar x => ok x
  | _      => cerror "get_Lvar variable excepted"
  end.

Definition alloc_lval_call (mps:seq (option (bool * mem_pos_sub) * pexpr)) rmap (r: lval) (i:option nat) :=
  match i with
  | None => 
    Let _ := check_lval_reg_call r in
    ok (rmap, r)
  | Some i => 
    match nth (None, Pconst 0) mps i with
    | (Some (_,mp), _) =>
      Let x := get_Lvar r in
      Let p := get_regptr x in
      let rmap := Region.set_arr_call rmap (v_var x) mp in
      ok (rmap, Lvar p)
    | (None, _) => cerror "alloc_r_call : please report"
    end
  end.

Definition alloc_call_res rmap mps ret_pos rs := 
  fmapM2 bad_lval_number (alloc_lval_call mps) rmap rs ret_pos.

Definition alloc_call rmap ini rs fn es := 
  let sao := local_alloc fn in
  Let es  := alloc_call_args rmap sao.(sao_params) es in
  Let rs  := alloc_call_res  rmap es sao.(sao_return) rs in
  let es  := map snd es in
  ok (rs.1, Ccall ini rs.2 fn es).

Fixpoint alloc_i (rmap:regions) (i: instr) : result instr_error (regions * instr) :=
  let (ii, ir) := i in
  Let ir :=
    match ir with
    | Cassgn r t ty e => 
      if is_sarr ty then add_iinfo ii (alloc_array_move_init rmap r e) 
      else
        Let e := add_iinfo ii (alloc_e rmap e) in
        Let r := add_iinfo ii (alloc_lval rmap r ty) in
        ok (r.1, Cassgn r.2 t ty e)

    | Copn rs t o e => 
      Let e  := add_iinfo ii (alloc_es rmap e) in
      Let rs := add_iinfo ii (alloc_lvals rmap rs (sopn_tout o)) in
      ok (rs.1, Copn rs.2 t o e)               
  
    | Cif e c1 c2 => 
      Let e := add_iinfo ii (alloc_e rmap e) in
      Let c1 := fmapM alloc_i rmap c1 in
      Let c2 := fmapM alloc_i rmap c2 in
      let rmap:= merge c1.1 c2.1 in
      ok (rmap, Cif e c1.2 c2.2)
  
    | Cwhile a c1 e c2 => 
      let check_c rmap := 
        Let c1 := fmapM alloc_i rmap c1 in
        let rmap1 := c1.1 in
        Let e := add_iinfo ii (alloc_e rmap1 e) in
        Let c2 := fmapM alloc_i rmap1 c2 in
        ok ((rmap1, c2.1), (e, (c1.2, c2.2))) in
      Let r := loop2 ii check_c Loop.nb rmap in
      ok (r.1, Cwhile a r.2.2.1 r.2.1 r.2.2.2)

    | Ccall ini rs fn es =>
      add_iinfo ii (alloc_call rmap ini rs fn es) 

    | Cfor _ _ _  => cierror ii (Cerr_stk_alloc "don't deal with for loop")
    | Ccopy r e => 
      add_iinfo ii (alloc_array_move_init rmap r e)
    end in
  ok (ir.1, MkI ii ir.2).

End PROG.

End Section.

Definition init_stack_layout fn (ws_align: wsize) (l: seq (var * wsize * Z)) := 
  let add (xsr: var * wsize * Z) 
          (slp:  Mvar.t (wsize * Z) * Z) := 
    let '(stack, p) := slp in
    let '(x,ws,ofs) := xsr in
    if Mvar.get stack x is Some _ then cferror fn "duplicate stack region, please report"
    else
      if (p <= ofs)%CMP then
        let len := size_of x.(vtype) in
        if (ws <= ws_align)%CMP then
          let stack := Mvar.set stack x (ws, ofs) in
          ok (stack, (ofs + len)%Z)
        else cferror fn "bad stack alignment" 
      else cferror fn "stack region overlap" in
  foldM add (Mvar.empty _, 0%Z) l.

Definition init_local_map vrip vrsp fn globals sao := 
  Let sp := init_stack_layout fn sao.(sao_align) sao.(sao_slots) in
  let '(stack, size) := sp in
  if (size <= sao.(sao_size))%CMP then
    let add_alloc (xpk:var * ptr_kind_init) (lrx: Mvar.t ptr_kind * regions * Sv.t) :=
      let '(locals, rmap, sv) := lrx in
      let '(x, pk) := xpk in
      if Sv.mem x sv then cferror fn "invalid reg pointer, please report"
      else
        Let svrmap := 
          match pk with
          | PIstack x' sub => 
             match Mvar.get stack x' with
             | None => cferror fn "unknown stack region, please report"
             | Some (ws', ofs') =>
               if [&& (size_of x.(vtype) <= sub.(smp_len))%CMP, (0%Z <= sub.(smp_ofs))%CMP &
                      ((sub.(smp_ofs) + sub.(smp_len))%Z <= size_of x'.(vtype))%CMP] then 
                 let mps := mps_stack x' vrsp ws' sub in
                 ok (sv, Pstack x' ofs' ws' sub, Region.set_arr_init rmap x mps)
               else cferror fn "invalid stack slot, please report"
             end
          | PIglob x' sub => 
            match Mvar.get globals x' with
            | None => cferror fn "unknown global region, please report"
            | Some (ofs', ws') =>
              if [&&  (size_of x.(vtype) <= sub.(smp_len))%CMP, (0%Z <= sub.(smp_ofs))%CMP & 
                      ((sub.(smp_ofs) + sub.(smp_len))%Z <= size_of x'.(vtype))%CMP] then 
                ok (sv, Pglob x' ofs' ws' sub, rmap)
              else cferror fn "invalid global slot, please report"
             end
          | PIstkptr x' sub xp =>
            match Mvar.get stack x' with
            | None => cferror fn "unknown stack region, please report"
            | Some (ws', ofs') =>
              if Sv.mem xp sv then cferror fn "invalid stk ptr (not uniq), please report"
              else                
                if [&& (Uptr <= ws')%CMP,
                    (0%Z <= sub.(smp_ofs))%CMP & 
                    ((sub.(smp_ofs) + sub.(smp_len))%Z <= size_of x'.(vtype))%CMP] then
                  ok (Sv.add xp sv, Pstkptr x' ofs' ws' sub xp, rmap)
              else cferror fn "invalid ptr kind, please report"
            end
          | PIregptr p => 
            if Sv.mem p sv then cferror fn "invalid reg pointer already exists, please report"
            else if vtype p != sword Uptr then cferror fn "invalid pointer type, please report"
            else ok (Sv.add p sv, Pregptr p, rmap) 
          end in
        let '(sv,pk, rmap) := svrmap in
        let locals := Mvar.set locals x pk in
        ok (locals, rmap, sv) in
    let sv := Sv.add vrip (Sv.add vrsp Sv.empty) in
    Let aux := foldM add_alloc (Mvar.empty _, Region.empty, sv) sao.(sao_alloc) in
    let '(locals, rmap, sv) := aux in
    ok (stack, locals, rmap, sv)
  else cferror fn "stack size, please report".

(* TODO : move *)
Definition add_err_fun (A : Type) (f : funname) (r : cexec A) :=
  match r with
  | ok _ a => ok a
  | Error e => Error (Ferr_fun f e)
  end.

(** For each function, the oracle returns:
  - the size of the stack block;
  - an allocation for local variables;
  - an allocation for the variables to save;
  - where to save the stack pointer (of the caller); (* TODO: merge with above? *)
  - how to pass the return address (non-export functions only)

  It can call back the partial stack-alloc transformation that given an oracle (size of the stack block and allocation of stack variables)
  will transform the body of the current function.

  The oracle is implemented as follows:
   1/ stack allocation
   2/ Reg allocation
   3/ if we have remaining register to save the stack pointer we use on those register
      else
        4/ we restart stack allocation and we keep one position in the stack to save the stack pointer
        5/ Reg allocation
*)

Definition check_result pmap rmap params oi (x:var_i) := 
  match oi with
  | Some i =>
    match nth None params i with
    | Some mp => 
      Let mps := check_valid rmap x (Some 0%Z) (size_of x.(vtype))in
      Let _   := assert (mp == mps.(mps_mp)) (Cerr_stk_alloc "invalid reg ptr in result") in
      Let p   := get_regptr pmap x in
      ok p
    | None => cerror "invalid function info:please report"
    end
  | None => 
    Let _ := check_var pmap x in
    ok x
  end.

Definition check_results pmap rmap params oi res := 
  mapM2 (Cerr_stk_alloc "invalid function info:please report")
        (check_result pmap rmap params) oi res.

Definition init_param accu pi (x:var_i) := 
  let: (disj, lmap, rmap) := accu in
  match pi with
  | None => ok (accu, (None, x))
  | Some pi => 
    Let _ := assert (vtype pi.(pp_ptr) == sword Uptr) (Cerr_stk_alloc "bad ptr type: please report") in
    Let _ := assert (~~Sv.mem pi.(pp_ptr) disj) (Cerr_stk_alloc "duplicate region: please report") in
    let mp := 
      {| mp_s := pi.(pp_ptr); mp_p := pi.(pp_ptr);
         mp_align := pi.(pp_align); mp_writable := pi.(pp_writable) |} in
    ok (Sv.add pi.(pp_ptr) disj, 
        Mvar.set lmap x (Pregptr pi.(pp_ptr)),
        Region.set_full rmap x mp, 
        (Some mp, with_var x pi.(pp_ptr)))
  end. 

Definition init_params disj lmap rmap sao_params params :=
  fmapM2 (Cerr_stk_alloc "invalid function info:please report")
    init_param (disj, lmap, rmap) sao_params params.
   
Definition alloc_fd_aux p_extra mglob (local_alloc: funname -> stk_alloc_oracle_t) sao (f: _ufun_decl) : cfexec _ufundef :=
  let: (fn, fd) := f in
  let vrip := {| vtype := sword Uptr; vname := p_extra.(sp_rip) |} in
  let vrsp := var_of_register RSP in
  Let mstk := init_local_map vrip vrsp fn mglob sao in
  let '(stack, locals, rmap, disj) := mstk in
  (* adding params to the map *)
  Let rparams := 
    add_err_fun fn (init_params disj locals rmap sao.(sao_params) fd.(f_params)) in
  let: (sv, lmap, rmap, alloc_params) := rparams in
  let paramsi := map fst alloc_params in
  let params : seq var_i := map snd alloc_params in
  let pmap := {|
        vrip    := vrip;
        vrsp    := vrsp;
        globals := mglob;
        locals  := lmap;
        vnew    := sv;
      |} in
  Let rbody := add_finfo fn fn (fmapM (alloc_i pmap local_alloc) rmap fd.(f_body)) in
  let: (rmap, body) := rbody in
  Let res := 
      add_err_fun fn (check_results pmap rmap paramsi sao.(sao_return) fd.(f_res)) in
  ok {|
    f_iinfo := f_iinfo fd;
    f_tyin := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_params) fd.(f_tyin); 
    f_params := params;
    f_body := body;
    f_tyout := map2 (fun o ty => if o is Some _ then sword Uptr else ty) sao.(sao_return) fd.(f_tyout);
    f_res := res;
    f_extra := f_extra fd |}.

Definition alloc_fd p_extra mglob (local_alloc: funname -> stk_alloc_oracle_t) (f: ufun_decl) :=
  let: sao := local_alloc f.1 in
  Let fd := alloc_fd_aux p_extra mglob local_alloc sao f in
  let f_extra := {|
        sf_align  := sao.(sao_align);
        sf_stk_sz := sao.(sao_size);
        sf_to_save := sao.(sao_to_save);
        sf_save_stack := sao.(sao_rsp);
        sf_return_address := sao.(sao_return_address);
      |} in
  ok (f.1, swith_extra fd f_extra). 

Definition check_glob (m: Mvar.t (Z*wsize)) (data:seq u8) (gd:glob_decl) := 
  let x := gd.1 in
  match Mvar.get m x with
  | None => false 
  | Some (z, _) =>
    let n := Z.to_nat z in
    let data := drop n data in
    match gd.2 with
    | @Gword ws w =>
      let s := Z.to_nat (wsize_size ws) in 
      (s <= size data) && 
      (LE.decode ws (take s data) == w)
    | @Garr p t =>
      let s := Z.to_nat p in
      (s <= size data) &&
      all (fun i => 
             match WArray.get AAdirect U8 t (Z.of_nat i) with
             | Ok w => nth 0%R data i == w
             | _    => false
             end) (iota 0 s)
    end
  end.

Definition check_globs (gd:glob_decls) (m:Mvar.t (Z*wsize)) (data:seq u8) := 
  all (check_glob m data) gd.

Definition init_map (sz:Z) (l:list (var * wsize * Z)) : cexec (Mvar.t (Z*wsize)) :=
  let add (vp:var * wsize * Z) (mp:Mvar.t (Z*wsize) * Z) :=
    let '(v, ws, p) := vp in
    if (mp.2 <=? p)%Z then
      let ty := vtype v in
      if is_align (wrepr _ p) ws then
        let s := size_of ty in
        cok (Mvar.set mp.1 v (p,ws), p + s)%Z
      else cerror "bad global alignment: please report"
    else cerror "global overlap: please report" in
  Let mp := foldM add (Mvar.empty (Z*wsize), 0%Z) l in
  if (mp.2 <=? sz)%Z then cok mp.1
  else cerror "global size:please report".

Definition alloc_prog rip global_data global_alloc local_alloc (P:_uprog) : cfexec _sprog :=
  Let mglob := add_err_msg (init_map (Z.of_nat (size global_data)) global_alloc) in
  let p_extra :=  {|
    sp_rip   := rip;
    sp_globs := global_data;
  |} in
  if rip == string_of_register RSP then Error (Ferr_msg (Cerr_stk_alloc "rip and rsp clash, please report"))
  else if check_globs P.(p_globs) mglob global_data then
    Let p_funs := mapM (alloc_fd p_extra mglob local_alloc) P.(p_funcs) in
    ok  {| p_funcs  := p_funs;
           p_globs := [::];
           p_extra := p_extra;
        |}
  else 
     Error (Ferr_msg (Cerr_stk_alloc "invalid data: please report")).
