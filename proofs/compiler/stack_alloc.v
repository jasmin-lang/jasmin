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
Require Import strings word utils type var expr low_memory sem.
Require Import constant_prop.
Require Import compiler_util.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope vmap.
Local Open Scope seq_scope.

Variant saved_stack :=
| SavedStackNone
| SavedStackReg of var
| SavedStackStk of Z.

Definition saved_stack_beq (x y : saved_stack) :=
  match x, y with
  | SavedStackNone, SavedStackNone => true
  | SavedStackReg v1, SavedStackReg v2 => v1 == v2
  | SavedStackStk z1, SavedStackStk z2 => z1 == z2
  | _, _ => false
  end.

Lemma saved_stack_eq_axiom : Equality.axiom saved_stack_beq.
Proof.
  move=> [ | v1 | z1] [ | v2 | z2] /=; try constructor => //.
  + apply (@equivP (v1 = v2)); first by apply eqP.
    by intuition congruence.
  apply (@equivP (z1 = z2)); first by apply eqP.
  by intuition congruence.
Qed.

Definition saved_stack_eqMixin   := Equality.Mixin saved_stack_eq_axiom.
Canonical  saved_stack_eqType      := Eval hnf in EqType saved_stack saved_stack_eqMixin.

Record sfundef := MkSFun {
  sf_iinfo  : instr_info;
  sf_stk_sz : Z;
  sf_tyin   : seq stype;
  sf_params : seq var_i;
  sf_body   : cmd;
  sf_tyout  : seq stype;
  sf_res    : seq var_i;
  sf_extra  : list var * saved_stack;
}.

Definition sfundef_beq fd1 fd2 :=
  match fd1, fd2 with
  | MkSFun ii1 sz1 ti1 p1 c1 to1 r1 e1, MkSFun ii2 sz2 ti2 p2 c2 to2 r2 e2=>
    (ii1 == ii2) && (sz1 == sz2) &&
    (ti1 == ti2) && (p1 == p2) && (c1 == c2) && (to1 == to2) && (r1 == r2) && (e1 == e2)
  end.

Lemma sfundef_eq_axiom : Equality.axiom sfundef_beq.
Proof.
  move=> [i1 s1 ti1 p1 c1 to1 r1 e1] [i2 s2 ti2 p2 c2 to2 r2 e2] /=.
  apply (@equivP ((i1 == i2) && (s1 == s2) && (ti1 == ti2) && (p1 == p2) && (c1 == c2) && (to1 == to2) && (r1 == r2) && (e1 == e2)));first by apply idP.
  by split=> [ /andP[] /andP[] /andP[] /andP[] /andP[] /andP[] /andP[] | [] ] /eqP -> /eqP->/eqP->/eqP->/eqP->/eqP->/eqP->/eqP->.
Qed.

Definition sfundef_eqMixin   := Equality.Mixin sfundef_eq_axiom.
Canonical  sfundef_eqType      := Eval hnf in EqType sfundef sfundef_eqMixin.

Record sprog := 
  { sp_rip   : Ident.ident;
    sp_globs : seq u8;
    sp_stk_id: Ident.ident;
    sp_funcs : seq (funname * sfundef) }.

Variant mem_space := 
  | MSglob 
  | MSstack.

Scheme Equality for mem_space. 

Lemma mem_space_axiom : Equality.axiom mem_space_beq. 
Proof. 
  move=> x y;apply:(iffP idP).
  + by apply: internal_mem_space_dec_bl.
  by apply: internal_mem_space_dec_lb.
Qed.

Definition mem_space_eqMixin     := Equality.Mixin mem_space_axiom.
Canonical  mem_space_eqType      := Eval hnf in EqType mem_space mem_space_eqMixin.

Variant alloc_pos := 
  | APmem of Z
  | APreg of Ident.ident & mem_space & Z.

Definition alloc_pos_beq (ap1 ap2: alloc_pos) := 
  match ap1, ap2 with
  | APmem z1, APmem z2 => z1 == z2
  | APreg x1 m1 z1, APreg x2 m2 z2 => [&& x1 == x2, m1 == m2 & z1 == z2]
  | _, _ => false
  end.

Lemma alloc_pos_axiom : Equality.axiom alloc_pos_beq. 
Proof. 
  move=> [z1 | x1 m1 z1] [z2 | x2 m2 z2] /=; try by constructor.
  + by apply (equivP eqP); split => [ | []] ->.
  by apply (equivP and3P); split => [[/eqP -> /eqP -> /eqP ->] | [-> -> ->]].
Qed.

Definition alloc_pos_eqMixin     := Equality.Mixin alloc_pos_axiom.
Canonical  alloc_pos_eqType      := Eval hnf in EqType alloc_pos alloc_pos_eqMixin.

Record mem_pos := 
  { mp_s : mem_space;
    mp_ofs : Z;
    mp_id : option Ident.ident;
  }.

Record gmap := MkGMap
  { rip : Ident.ident;
    mglob: Mvar.t Z;
  }.                 

Record smap := MkSMap
  { mstk  :> Mvar.t alloc_pos;
    meqon : Sv.t; 
  }.

Definition size_of (t:stype) :=
  match t with
  | sword sz => ok (wsize_size sz)
  | sarr n   => ok (Zpos n)
  | _      => cerror (Cerr_stk_alloc "size_of")
  end.

Definition aligned_for (ty: stype) (ofs: Z) : bool :=
  match ty with
  | sarr _ => true
  | sword sz => is_align (wrepr _ ofs) sz
  | sbool | sint => false
  end.

Definition init_map (sz:Z) (l:list (var * Z)) : cexec (Mvar.t Z) :=
  let add (vp:var*Z) (mp:Mvar.t Z * Z) :=
      let '(v, p) := vp in
    if (mp.2 <=? p)%Z then
      let ty := vtype v in
      if aligned_for ty vp.2 then
      Let s := size_of ty in
      cok (Mvar.set mp.1 v p, p + s)%Z
    else cerror (Cerr_stk_alloc "not aligned")
    else cerror (Cerr_stk_alloc "overlap") in
  Let mp := foldM add (Mvar.empty Z, 0%Z) l in
  if (mp.2 <=? sz)%Z then cok mp.1
  else cerror (Cerr_stk_alloc "stack size").

Section NRSP.

Context (nrsp: Ident.ident).

Definition vrsp := {| vtype := sword Uptr; vname := nrsp |}.

Definition is_vrsp (m:gmap) (x:var) :=
  x == vrsp.

Definition vrip (m:gmap) :=  {|vtype := sword Uptr; vname := m.(rip)|}.

Definition is_vrip (m:gmap) (x:var) :=
  x == (vrip m).

Definition check_var sm (x:var_i) := Sv.mem x sm.(meqon).


(* TODO: move *)
Definition cast_w ws := Papp1 (Oword_of_int ws).

Definition cast_ptr := cast_w Uptr.

Definition cast_const z := cast_ptr (Pconst z).

Definition mul := Papp2 (Omul (Op_w Uptr)).
Definition add := Papp2 (Oadd (Op_w Uptr)).

Definition cast_word e := 
  match e with
  | Papp1 (Oint_of_word U64) e1 => e1
  | _  => cast_ptr e
  end.

(* End TODO *)

Definition check_vfresh sm  x := 
  if is_glob x then cerror (Cerr_stk_alloc "global variable remain")
  else if Sv.mem x.(gv) sm.(meqon) then ok tt
  else cerror (Cerr_stk_alloc ("invalid variable access " ++ x.(gv).(vname))).

Definition check_vfresh_lval gm x := 
  if is_vrsp gm x then cerror (Cerr_stk_alloc "the stack variable is not fresh")
  else if is_vrip gm x then cerror (Cerr_stk_alloc "the instruction pointer variable is not fresh")
  else ok tt.

Definition not_aligned {A} :=
  @cerror (Cerr_stk_alloc "array variable not aligned") A.

Definition invalid_var {A} := 
  @cerror (Cerr_stk_alloc "invalid variable") A.

Definition not_a_word_v {A} := 
  @cerror (Cerr_stk_alloc "not a word variable") A.

Definition mk_ofs ws e1 ofs := 
  let sz := mk_scale ws in
  if is_const e1 is Some i then 
    cast_const (i * sz + ofs)%Z
  else 
    add (mul (cast_const sz) (cast_word e1)) (cast_const ofs).

Definition mp_of_ap ap := 
  match ap with
  | APmem ofs => {| mp_s := MSstack; mp_ofs := ofs; mp_id := None |}
  | APreg r m ofs => {| mp_s := m; mp_ofs := ofs; mp_id := Some r |}
  end.

Definition find_gvar (gm:gmap) (mstk: Mvar.t alloc_pos) (x:gvar) := 
  if is_lvar x then 
    match Mvar.get mstk x.(gv) with
    | Some ap => Some (mp_of_ap ap)
    | None => None
    end
  else
    match Mvar.get gm.(mglob) x.(gv) with
    | Some ofs => Some {| mp_s := MSglob; mp_ofs := ofs; mp_id := None |}
    | None     => None
    end.

(* Definition vptr m (x:gvar) := if is_lvar x then vrsp m else vrip m. *)

Definition vptr gm mp := 
  match mp with
  | MSglob => vrip gm
  | MSstack => vrsp
  end.

Fixpoint alloc_e (gm:gmap) (sm:smap) (e: pexpr) := 
  match e with
  | Pconst _ | Pbool _ | Parr_init _ => ok e
  | Pvar   x =>
    match find_gvar gm sm x with 
    | Some mp =>
      if mp.(mp_id) is None then
        let xv := x.(gv) in
        if is_word_type (vtype xv) is Some ws then
          let ofs := cast_const mp.(mp_ofs) in
          let stk := {| v_var := vptr gm mp.(mp_s); v_info := xv.(v_info) |} in
          ok (Pload ws stk ofs)
        else not_a_word_v 
      else cerror (Cerr_stk_alloc "var expr in reg")
    | None     =>
      Let _ := check_vfresh sm x in
      ok e
    end
  | Pget ws x e1 =>
    Let e1 := alloc_e gm sm e1 in
    match find_gvar gm sm (mk_lvar x) with 
    | Some mp =>
      let ofs := mp.(mp_ofs) in      
      if is_align (wrepr _ ofs) ws then
        let ptr :=
          if mp.(mp_id) is Some r then {| vname := r; vtype := sword Uptr|}
          else vptr gm mp.(mp_s) in
        let x := {| v_var := ptr; v_info := x.(v_info) |} in
        
        let ofs := mk_ofs ws e1 (if mp.(mp_id) is None then mp.(mp_ofs) else 0) in
        ok (Pload ws x ofs)
      else not_aligned
    
    | None =>
      Let _ := check_vfresh sm (mk_lvar x) in
      ok (Pget ws x e1)
    end

  | Pload ws x e1 =>
    if check_var sm x then
      Let e1 := alloc_e gm sm e1 in
      ok (Pload ws x e1)
    else invalid_var 

  | Papp1 o e1 =>
    Let e1 := alloc_e gm sm e1 in
    ok (Papp1 o e1)
   
  | Papp2 o e1 e2 =>
    Let e1 := alloc_e gm sm e1 in
    Let e2 := alloc_e gm sm e2 in
    ok (Papp2 o e1 e2)

  | PappN o es => 
    Let es := mapM (alloc_e gm sm) es in
    ok (PappN o es)  

  | Pif t e e1 e2 =>
    Let e := alloc_e gm sm e in
    Let e1 := alloc_e gm sm e1 in
    Let e2 := alloc_e gm sm e2 in
    ok (Pif t e e1 e2)
  end.

Definition Mvar_filter (A:Type) (f:var -> A -> bool) (m:Mvar.t A) := 
  Mvar.fold (fun x a m => if f x a then Mvar.set m x a else m) m (Mvar.empty A).

Definition keep_addrvar id (x:var) ap :=
  match ap with
  | APmem z => true 
  | APreg id' _ _ => id != id'
  end.

Definition map_remove sm x :=
  let mstk := 
    match is_word_type x.(vtype) with
    | Some ws =>
      if (ws == Uptr) then
        Mvar_filter (keep_addrvar x.(vname)) sm.(mstk) 
      else sm.(mstk)
    | _ => sm.(mstk)
    end in
  {| mstk := Mvar.remove mstk x;
     meqon := Sv.add x sm.(meqon) |}.
      
Definition keep_z (x:var) ofs (x':var) ap := 
  (x == x') || 
  match ap with 
  | APmem ofs' => ofs != ofs'
  | APreg _ MSstack ofs' => ofs != ofs'
  | APreg _ MSglob _     => true
  end.

Definition check_lvar gm (x:var_i) sm :=
  Let _ := check_vfresh_lval gm x in
  ok (map_remove sm x).

Definition alloc_lval (gm:gmap) (sm:smap) (r:lval) ty := 
  match r with
  | Lnone _ _ => ok (sm, r)

  | Lvar x =>

    match Mvar.get sm.(mstk) x with 
    | Some (APmem ofs) => 
      if is_word_type (vtype x) is Some ws then
        if ty == sword ws then  
          let ofs := cast_const ofs in
          let stk := {| v_var := vrsp; v_info := x.(v_info) |} in
          let sm := {| mstk := sm.(mstk); meqon := Sv.remove x sm.(meqon) |} in
          ok (sm, Lmem ws stk ofs)
        else cerror (Cerr_stk_alloc "invalid type for Lvar")
      else not_a_word_v 

    | Some (APreg _ _ _) => 
      cerror (Cerr_stk_alloc "lval in reg addr")

    | None     =>
      Let sm := check_lvar gm x sm in 
      ok (sm, r)
    end

  | Lmem ws x e1 =>
    if check_var sm x then
      Let e1 := alloc_e gm sm e1 in
      ok (sm, Lmem ws x e1)
    else invalid_var
    
  | Laset ws x e1 =>
    Let e1 := alloc_e gm sm e1 in
    match Mvar.get sm.(mstk) x with 
    | Some ap =>
      let mp := mp_of_ap ap in
      if mp.(mp_s) == MSstack then
        if is_align (wrepr _ mp.(mp_ofs)) ws then
          let sm := 
              {| mstk  := Mvar_filter (keep_z x mp.(mp_ofs)) sm.(mstk);
                 meqon := Sv.remove x sm.(meqon);
              |} in
          let (bid, disp) := 
            if mp.(mp_id) is Some id then (id, 0%Z)
            else (nrsp, mp.(mp_ofs)) in
          let bp := {| v_var := {| vname := bid; vtype := sword Uptr|}; v_info := x.(v_info) |} in
          let ofs := mk_ofs ws e1 disp in
          ok (sm, Lmem ws bp ofs)
        else not_aligned
      else cerror (Cerr_stk_alloc "assign global array")

    | None =>
      cerror (Cerr_stk_alloc ("array assign remains " ++ x.(vname)))
    end

  end.

Definition bad_lval_number := Cerr_stk_alloc "invalid number of lval".

Definition alloc_assgn gm sm ii r t ty e := 
  Let e := add_iinfo ii (alloc_e gm sm e) in
  Let r := add_iinfo ii (alloc_lval gm sm r ty) in
  ok (r.1, Cassgn r.2 t ty e).

Definition fmapM {eT aT bT cT} (f : aT -> bT -> result eT (aT * cT))  : aT -> seq bT -> result eT (aT * seq cT) :=
  fix mapM a xs :=
    match xs with
    | [::] => Ok eT (a, [::])
    | [:: x & xs] =>
      Let y := f a x in
      Let ys := mapM y.1 xs in
      Ok eT (ys.1, y.2 :: ys.2)
    end.

Definition fmapM2 {eT aT bT cT dT} (e:eT) (f : aT -> bT -> cT -> result eT (aT * dT)) : 
   aT -> seq bT -> seq cT -> result eT (aT * seq dT) :=
  fix mapM a lb lc :=
    match lb, lc with
    | [::], [::] => Ok eT (a, [::])
    | [:: b & bs], [:: c & cs] =>
      Let y := f a b c in
      Let ys := mapM y.1 bs cs in
      Ok eT (ys.1, y.2 :: ys.2)
    | _, _ => Error e
    end.

Definition alloc_lvals gm sm rs tys := 
  fmapM2 bad_lval_number (alloc_lval gm) sm rs tys.

(* TODO: MOVE *)
Definition is_var e := 
  match e with
  | Pvar x => Some x
  | _      => None
  end.

(* TODO: MOVE *)
Definition is_arr_type t := 
  match t with
  | sarr _ => true
  | _      => false
  end.

Definition merge_alloc_pos (x:var) (ap1 ap2: option alloc_pos) := 
  match ap1, ap2 with
  | Some ap1, Some ap2 => if ap1 == ap2 then Some ap1 else None
  | _       , _        => None
  end.

Definition merge (m1 m2: smap) := 
  {| mstk  := Mvar.map2 merge_alloc_pos m1.(mstk) m2.(mstk);
     meqon := Sv.inter m1.(meqon) m2.(meqon);
  |}.

Definition incl_alloc_pos ap1 (ap2 : option alloc_pos) := 
  match ap2 with
  | Some ap2 => ap1 == ap2
  | None => false
  end.

Definition incl (m1 m2: smap) := 
  all (fun xap => incl_alloc_pos xap.2 (Mvar.get m2.(mstk) xap.1)) (Mvar.elements m1.(mstk)) &&
  Sv.subset m1.(meqon) m2.(meqon).

Section LOOP.

 Variable ii:instr_info.

 Variable check_c2 : smap -> ciexec ((smap * smap) * (pexpr * (seq instr * seq instr)) ).

 Fixpoint loop2 (n:nat) (m:smap) := 
    match n with
    | O => cierror ii (Cerr_Loop "stack_alloc")
    | S n =>
      Let m' := check_c2 m in
      if incl m m'.1.2 then ok (m'.1.1, m'.2)
      else loop2 n (merge m m'.1.2)
    end.

End LOOP.

Section ALLOC.

Fixpoint alloc_i (gm:gmap) (sm: smap) (i: instr) : result instr_error (smap * instr) :=
  let (ii, ir) := i in
  Let ir := 
    match ir with
    | Cassgn r t ty e => 
      alloc_assgn gm sm ii r t ty e

    | Copn rs t o e => 
      Let e  := add_iinfo ii (mapM (alloc_e gm sm) e) in
      Let rs := add_iinfo ii (alloc_lvals gm sm rs (sopn_tout o)) in
      ok (rs.1, Copn rs.2 t o e)               
  
    | Cif e c1 c2 => 
      Let e := add_iinfo ii (alloc_e gm sm e) in
      Let c1 := fmapM (alloc_i gm) sm c1 in
      Let c2 := fmapM (alloc_i gm) sm c2 in
      let sm := merge c1.1 c2.1 in
      ok (sm, Cif e c1.2 c2.2)
  
    | Cwhile a c1 e c2 => 
      let check_c sm := 
        Let c1 := fmapM (alloc_i gm) sm c1 in
        let sm := c1.1 in
        Let e := add_iinfo ii (alloc_e gm sm e) in
        Let c2 := fmapM (alloc_i gm) sm c2 in
        ok ((sm, c2.1), (e, (c1.2, c2.2))) in
      Let r := loop2 ii check_c Loop.nb sm in
      ok (r.1, Cwhile a r.2.2.1 r.2.1 r.2.2.2)
  
    | Cfor _ _ _  => cierror ii (Cerr_stk_alloc "don't deal with for loop")
    | Ccall _ _ _ _ => cierror ii (Cerr_stk_alloc "don't deal with call")
    end in
  ok (ir.1, MkI ii ir.2).

End ALLOC.

(* TODO : move *)
Definition add_err_fun (A : Type) (f : funname) (r : cexec A) :=
  match r with
  | ok _ a => ok a
  | Error e => Error (Ferr_fun f e)
  end.

Definition alloc_fd rip mglob 
    (stk_alloc_fd : fun_decl -> Z * list (var * Z) * (list var * saved_stack))
    (f: fun_decl) :=
  let info := stk_alloc_fd f in
  let (fn, fd) := f in
  Let sfd :=  
    let: ((size, l), saved) := info in
    Let mstk := add_err_fun fn (init_map size l) in
    let mstk := Mvar.map APmem mstk in
    let gm := 
        {| rip   := rip;
           mglob := mglob;
        |} in
    let sm0 :=  
        {| mstk  := mstk;
           meqon := Sv.empty;
        |} in
    
    Let sm1 := add_err_fun fn (foldM (check_lvar gm) sm0 fd.(f_params)) in
    Let body := add_finfo fn fn (fmapM (alloc_i gm) sm1 fd.(f_body)) in
    if (nrsp != rip) && all (check_var body.1) fd.(f_res) then
      ok {| sf_iinfo  := fd.(f_iinfo);
            sf_stk_sz := size;
            sf_tyin   := fd.(f_tyin);
            sf_params := fd.(f_params);
            sf_body   := body.2;
            sf_tyout  := fd.(f_tyout);
            sf_res    := fd.(f_res);
            sf_extra  := saved;
         |} 
    else add_err_fun fn invalid_var in
  ok (fn, sfd).

Definition check_glob (m: Mvar.t Z) (data:seq u8) (gd:glob_decl) := 
  let x := gd.1 in
  match Mvar.get m x with
  | None => false 
  | Some z =>
    let n := Z.to_nat z in
    let data := drop n data in
    match gd.2 with
    | @Gword ws w =>
      let s := Z.to_nat (wsize_size ws) in 
      (s <= size data) && 
      (LE.decode ws (take s data) == w)
    end
  end.

Definition check_globs (gd:glob_decls) (m:Mvar.t Z) (data:seq u8) := 
  all (check_glob m data) gd.

Definition alloc_prog stk_alloc_fd (glob_alloc_p : prog -> seq u8 * Ident.ident * list (var * Z) ) P := 
  let: ((data, rip), l) := glob_alloc_p P in 
  Let mglob := add_err_msg (init_map (Z.of_nat (size data)) l) in
  if check_globs P.(p_globs) mglob data then
    Let p_funs := mapM (alloc_fd rip mglob stk_alloc_fd) P.(p_funcs) in
    ok  {| sp_rip   := rip; 
           sp_globs := data; 
           sp_stk_id := nrsp;
           sp_funcs := p_funs |}
  else 
     Error (Ferr_msg (Cerr_stk_alloc "invalid data: please report")).

End NRSP.
